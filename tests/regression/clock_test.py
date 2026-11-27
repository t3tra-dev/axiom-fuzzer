"""Clock/deadline fault tests: no subprocesses, real waiting, or system sleep."""
import contextlib
import pathlib
import signal
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest import mock

sys.path.insert(0, str(pathlib.Path(sys.argv.pop(1)).resolve().parent))
import external as atp


class FakeRun:
    def __init__(self):
        self.wall_ns = self.awake_ns = 0
        self.waits = []
        self.process_waits = []
        self.signals = []
        self.exited = False
        self.reaped = self.thread_started = False
        self.start_error = None
        self.process = SimpleNamespace(pid=1234, returncode=None, wait=self.process_wait,
                                       kill=lambda: self.finish(-signal.SIGKILL))
        self.on_wait = lambda: None
        self.on_start = lambda: None
        self.on_kill = lambda: self.finish(-signal.SIGKILL)
        self.on_awake = lambda: None
        self.on_sleep = lambda: None
        self.on_set = lambda: None
        self.on_wall = lambda: None

    def advance(self, awake=0., suspend=0.):
        self.awake_ns += round(awake * 1e9)
        self.wall_ns += round((awake + suspend) * 1e9)

    def finish(self, code=0):
        if self.process.returncode is None:
            self.process.returncode = code
            if self.thread_started:
                self.reap()

    def process_wait(self, timeout=None):
        self.process_waits.append(timeout)
        if self.process.returncode is None:
            raise atp.subprocess.TimeoutExpired("mock-only", timeout)
        self.reaped = True
        return self.process.returncode

    def read_wall(self, clock_id):
        self.on_wall()
        return self.wall_ns

    def read_awake(self):
        self.on_awake()
        return self.awake_ns

    def set(self):
        self.on_set()
        self.exited = True

    def wait(self, seconds):
        if not self.exited:
            self.waits.append(seconds)
            self.advance(awake=seconds)
            self.on_wait()
        return self.exited

    def thread(self, *, target, daemon):
        self.reap = target
        return SimpleNamespace(start=self.start_thread)

    def start_thread(self):
        if self.start_error:
            raise self.start_error
        self.thread_started = True
        self.on_start()

    def killpg(self, pid, sig):
        self.signals.append((pid, sig))
        self.on_kill()

    def sleep(self, seconds):
        self.advance(awake=seconds)
        self.on_sleep()

    @contextlib.contextmanager
    def installed(self):
        with contextlib.ExitStack() as stack:
            for obj, name, value in [
                (atp.platform, "system", lambda: "Darwin"),
                (atp.time, "CLOCK_MONOTONIC_RAW", 4),
                (atp.time, "clock_gettime_ns", self.read_wall),
                (atp.time, "clock_getres", lambda clock_id: 1e-9),
                (atp.time, "monotonic_ns", self.read_awake),
                (atp.time, "monotonic", lambda: self.awake_ns / 1e9),
                (atp.time, "get_clock_info", lambda name: SimpleNamespace(
                    implementation="fixture awake clock", resolution=1e-9)),
                (atp.time, "sleep", self.sleep),
                (atp.subprocess, "Popen", lambda *args, **kwargs: self.process),
                (atp.threading, "Event", lambda: self),
                (atp.threading, "Thread", self.thread),
                (atp.os, "killpg", self.killpg),
            ]:
                stack.enter_context(mock.patch.object(obj, name, value, create=True))
            yield self

    def is_set(self):
        return self.exited


class ClockTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="axiom-clock-test-")
        self.addCleanup(directory.cleanup)
        self.output = pathlib.Path(directory.name) / "log"

    def run_fake(self, fixture, seconds=1.):
        with fixture.installed():
            return atp.run_logged(["mock-only"], self.output, seconds)

    def test_platform_clocks_have_different_suspend_semantics(self):
        for system, name, clock_id in [("Darwin", "CLOCK_MONOTONIC_RAW", 4),
                                      ("Linux", "CLOCK_BOOTTIME", 7)]:
            with self.subTest(system=system), FakeRun().installed(), \
                    mock.patch.object(atp.platform, "system", return_value=system), \
                    mock.patch.object(atp.time, name, clock_id, create=True), \
                    mock.patch.object(atp.time, "clock_gettime_ns", return_value=0) as read:
                clock = atp._wall_clock()
                self.assertEqual(clock.name, name)
                self.assertEqual(atp.wall_clock_info(), {
                    "wall_clock": name, "wall_clock_source": "time.clock_gettime_ns",
                    "wall_clock_suspend_aware": True, "awake_clock": "fixture awake clock"})
                clock.now_ns()
                self.assertTrue(all(call.args == (clock_id,) for call in read.call_args_list))

    def test_unsupported_or_unavailable_clock_fails_before_spawn(self):
        for system, error in [("Windows", None), ("FreeBSD", None),
                              ("Darwin", AttributeError("missing API")),
                              ("Linux", OSError("unsupported clock"))]:
            with self.subTest(system=system, error=error), FakeRun().installed(), \
                    mock.patch.object(atp.platform, "system", return_value=system), \
                    mock.patch.object(atp.time, "CLOCK_BOOTTIME", 7, create=True), \
                    mock.patch.object(atp.time, "clock_gettime_ns", side_effect=error), \
                    mock.patch.object(atp.subprocess, "Popen") as spawn:
                with self.assertRaisesRegex(atp.SetupError, "suspend-aware"):
                    atp.run_logged(["must-not-spawn"], self.output, 1.)
                spawn.assert_not_called()

    def test_suspend_jump_expires_wall_deadline_after_one_bounded_wait(self):
        fixture = FakeRun()
        fixture.on_wait = lambda: fixture.advance(suspend=30.)
        result = self.run_fake(fixture)
        self.assertTrue(result["timed_out"])
        self.assertEqual(result["returncode"], -signal.SIGKILL)
        self.assertEqual(len(fixture.waits), 1)
        self.assertLessEqual(fixture.waits[0], .1)
        self.assertAlmostEqual(result["wall_seconds"], 30.1)
        self.assertEqual(result["wall_seconds"], result["continuous_seconds"])
        self.assertAlmostEqual(result["awake_seconds"], .1)
        self.assertAlmostEqual(result["clock_gap_seconds"], 30.)
        self.assertGreater(result["clock_gap_seconds"], result["clock_gap_uncertainty_seconds"])
        self.assertEqual(result["wall_clock"], "CLOCK_MONOTONIC_RAW")
        self.assertEqual(result["wall_clock_source"], "time.clock_gettime_ns")
        self.assertTrue(result["wall_clock_suspend_aware"])
        self.assertEqual(result["awake_clock"], "fixture awake clock")

    def test_normal_timeout_and_early_exit_keep_process_group_cleanup(self):
        for early in (False, True):
            fixture = FakeRun()
            if early:
                fixture.on_wait = fixture.finish
            with self.subTest(early=early):
                result = self.run_fake(fixture)
                self.assertEqual(result["timed_out"], not early)
                self.assertEqual(result["returncode"], 0 if early else -signal.SIGKILL)
                self.assertTrue(all(0 < wait <= .1 for wait in fixture.waits))
                self.assertEqual(fixture.signals, [(fixture.process.pid, signal.SIGKILL)])
                self.assertEqual(result["clock_gap_seconds"], 0.)

    def test_reaper_timestamp_controls_deadline_boundary_before_cleanup(self):
        for ended in (.999999999, 1., 1.000000001):
            fixture = FakeRun()
            def finish():
                fixture.advance(awake=ended)
                fixture.finish()
            fixture.on_start = finish
            # Notification/cleanup scheduling must not inflate the finish time.
            fixture.on_set = lambda: fixture.advance(awake=2.)
            fixture.on_kill = lambda: fixture.advance(suspend=10.)
            with self.subTest(ended=ended):
                result = self.run_fake(fixture)
                self.assertEqual(result["wall_seconds"], ended)
                self.assertEqual(result["timed_out"], ended > 1.)
                self.assertEqual(result["clock_gap_seconds"], 0.)

    def test_preemption_between_clock_reads_is_covered_by_uncertainty(self):
        for at_start in (False, True):
            fixture = FakeRun()
            reads = []
            def preempt():
                reads.append(None)
                if len(reads) == (1 if at_start else 2):
                    fixture.advance(awake=3.)
            fixture.on_awake = preempt
            fixture.on_wait = fixture.finish
            with self.subTest(at_start=at_start):
                result = self.run_fake(fixture, seconds=10.)
                self.assertAlmostEqual(abs(result["clock_gap_seconds"]), 3.)
                self.assertLessEqual(abs(result["clock_gap_seconds"]),
                                     result["clock_gap_uncertainty_seconds"])
                self.assertFalse(result["timed_out"])

    def test_on_time_reap_with_delayed_notification_is_not_a_timeout(self):
        fixture = FakeRun()
        def delayed_notification():
            fixture.finish()
            fixture.exited = False
            fixture.advance(awake=2.)
        fixture.on_wait = delayed_notification
        fixture.on_kill = lambda: setattr(fixture, "exited", True)
        result = self.run_fake(fixture)
        self.assertEqual(result["wall_seconds"], .1)
        self.assertFalse(result["timed_out"])

    def test_reaper_errors_still_notify_and_clean_up(self):
        for failed_read in (False, True):
            fixture = FakeRun()
            def fail():
                raise OSError("fixture reaper failure")
            if failed_read:
                reads = []
                def read_awake():
                    reads.append(None)
                    if len(reads) == 2:
                        fail()
                fixture.on_awake = read_awake
            else:
                fixture.process.wait = fail
            fixture.on_start = fixture.finish
            with self.subTest(failed_read=failed_read), \
                    self.assertRaisesRegex(atp.ProcessCleanupError, "cannot reap process"):
                self.run_fake(fixture)
            self.assertTrue(fixture.exited)
            self.assertEqual(fixture.signals, [(fixture.process.pid, signal.SIGKILL)])

    def test_suspend_during_cleanup_permission_retries_expires_cleanup_budget(self):
        fixture = FakeRun()
        def denied():
            raise PermissionError(1, "fixture group denial")
        fixture.on_kill = denied
        fixture.on_sleep = lambda: fixture.advance(suspend=5.)
        with self.assertRaisesRegex(atp.ProcessCleanupError, "cannot stop process group"):
            self.run_fake(fixture)
        self.assertEqual(fixture.process.returncode, -signal.SIGKILL)
        self.assertEqual(len(fixture.signals), 2)

    def test_suspend_during_reap_wait_expires_cleanup_budget(self):
        fixture = FakeRun()
        fixture.on_kill = lambda: None
        fixture.on_wait = lambda: fixture.advance(suspend=5.) if fixture.signals else None
        with self.assertRaisesRegex(atp.ProcessCleanupError, "did not exit after SIGKILL"):
            self.run_fake(fixture)
        self.assertLessEqual(fixture.waits[-1], .1)
        self.assertLess(fixture.awake_ns, 2e9)

    def test_persistent_clock_failure_still_kills_group_and_reaps(self):
        for failed_at in ("wait", "cleanup", "permission_retry"):
            fixture = FakeRun()
            def broken_clock():
                raise OSError("fixture persistent clock failure")
            if failed_at == "wait":
                fixture.on_start = lambda: setattr(fixture, "on_wall", broken_clock)
            elif failed_at == "cleanup":
                def finish_then_break():
                    fixture.finish()
                    fixture.on_wall = broken_clock
                fixture.on_wait = finish_then_break
            else:
                fixture.on_wait = fixture.finish
                def deny_once():
                    if len(fixture.signals) == 1:
                        fixture.on_wall = broken_clock
                        raise PermissionError(1, "fixture group race")
                fixture.on_kill = deny_once
            with self.subTest(failed_at=failed_at), \
                    self.assertRaisesRegex(atp.ProcessCleanupError, "clock"):
                self.run_fake(fixture)
            self.assertTrue(fixture.signals, "clock failure bypassed group signalling")
            self.assertTrue(fixture.reaped)

    def test_clock_failure_with_denied_group_does_not_claim_cleanup_success(self):
        fixture = FakeRun()
        def broken_clock():
            raise OSError("fixture persistent clock failure")
        def denied():
            raise PermissionError(1, "fixture persistent group denial")
        fixture.on_start = lambda: setattr(fixture, "on_wall", broken_clock)
        fixture.on_kill = denied
        with self.assertRaisesRegex(atp.ProcessCleanupError, "cannot stop process group"):
            self.run_fake(fixture)
        self.assertTrue(fixture.reaped)
        self.assertGreater(len(fixture.signals), 1)
        self.assertLessEqual(len(fixture.signals), 100)

    def test_clock_failure_reap_wait_is_bounded(self):
        fixture = FakeRun()
        def broken_clock():
            raise OSError("fixture persistent clock failure")
        fixture.on_start = lambda: setattr(fixture, "on_wall", broken_clock)
        fixture.on_kill = lambda: None
        with self.assertRaisesRegex(atp.ProcessCleanupError, "did not exit after SIGKILL"):
            self.run_fake(fixture)
        self.assertEqual(fixture.signals, [(fixture.process.pid, signal.SIGKILL)])
        self.assertLessEqual(len(fixture.process_waits), 10)
        self.assertTrue(fixture.process_waits)
        self.assertTrue(all(timeout is not None and timeout <= .1
                            for timeout in fixture.process_waits))

    def test_waiter_start_failure_kills_and_reaps_without_a_thread(self):
        fixture = FakeRun()
        fixture.start_error = RuntimeError("fixture thread start failure")
        with self.assertRaisesRegex(atp.ProcessCleanupError, "thread start failure") as caught:
            self.run_fake(fixture)
        self.assertIs(caught.exception.__cause__, fixture.start_error)
        self.assertFalse(fixture.thread_started)
        self.assertEqual(fixture.signals, [(fixture.process.pid, signal.SIGKILL)])
        self.assertTrue(fixture.reaped)
        self.assertTrue(all(timeout is not None and timeout <= .1
                            for timeout in fixture.process_waits))

    def test_waiter_creation_failure_also_reaps_without_a_thread(self):
        for component in ("Thread", "Event"):
            fixture = FakeRun()
            with self.subTest(component=component), fixture.installed(), \
                    mock.patch.object(atp.threading, component,
                                      side_effect=RuntimeError("fixture creation failure")), \
                    self.assertRaisesRegex(atp.ProcessCleanupError, "creation failure") as caught:
                atp.run_logged(["mock-only"], self.output, 1.)
            self.assertIsInstance(caught.exception.__cause__, RuntimeError)
            self.assertEqual(fixture.signals, [(fixture.process.pid, signal.SIGKILL)])
            self.assertTrue(fixture.reaped)


if __name__ == "__main__":
    unittest.main(verbosity=2)
