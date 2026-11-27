"""Offline tests of benchmark contracts; fixture programs are not real ATPs."""
import argparse
import contextlib
import csv
import importlib.util
import io
import json
import os
import pathlib
import signal
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest
from unittest import mock
import zipfile

import clean_environment

clean_environment.scrub()

BENCHMARK, FUZZ, MUTATE, PROGRESS = [pathlib.Path(p).resolve() for p in sys.argv[1:5]]
sys.argv = sys.argv[:1]
sys.path.insert(0, str(BENCHMARK.parent))
import external as atp

# The archive tests extract with tarfile's extraction filters (benchmarks/external.py).
try:
    atp.require_tar_filters()
except atp.SetupError as error:
    sys.exit(f"benchmark_test.py: {error}")

spec = importlib.util.spec_from_file_location("benchmark_runner", BENCHMARK)
bench = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bench)


class BenchmarkTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="axiom-benchmark-test-")
        self.root = pathlib.Path(self.directory.name).resolve()
        self.addCleanup(self.directory.cleanup)

    def executable(self, text):
        path = self.root / "fixture"
        path.write_text("#!" + sys.executable + "\n" + text)
        path.chmod(0o755)
        return path

    def test_proof_path_observation_checks_witness_before_search(self):
        problem, witness = self.root / "input.p", self.root / "witness.cert"
        problem.write_text("cnf(p,axiom,p(a)). cnf(n,axiom,~p(a)).\n")
        subprocess.run([FUZZ, "--problem", problem, "--quiet", "--seconds", "2",
                        "--certificate", witness], check=True, capture_output=True)
        observed = subprocess.run([PROGRESS, "--problem", problem, "--witness", witness,
                                   "--seconds", "2"], check=True, capture_output=True, text=True)
        rows = list(csv.DictReader(io.StringIO(observed.stdout)))
        self.assertTrue(rows)
        self.assertTrue(all(r["conditional"] == "false" for r in rows))
        self.assertTrue(any(r["literals"] == "0" and r["stage"] == "derived" for r in rows))
        self.assertIn("newly discovered proof checked", observed.stderr)
        problem.write_text("cnf(p,axiom,q(a)).\n")
        rejected = subprocess.run([PROGRESS, "--problem", problem, "--witness", witness],
                                  capture_output=True, text=True)
        self.assertNotEqual(rejected.returncode, 0)
        self.assertEqual(rejected.stdout, "")

    def test_proof_edge_diagnostics_distinguish_reached_and_unobserved_parents(self):
        problem, witness = self.root / "input.p", self.root / "witness.cert"
        diagnostic = self.root / "edges.csv"
        problem.write_text("cnf(p,axiom,p(a)). cnf(n,axiom,~p(a)).\n")
        subprocess.run([FUZZ, "--problem", problem, "--quiet", "--seconds", "2",
                        "--certificate", witness], check=True, capture_output=True)
        for seconds, state in [(2, "reached"), (0, "parent_not_observed")]:
            subprocess.run([PROGRESS, "--problem", problem, "--witness", witness,
                            "--diagnostics", diagnostic, "--seconds", str(seconds)],
                           check=True, capture_output=True)
            with diagnostic.open() as stream:
                edges = [r for r in csv.DictReader(stream) if r["kind"] == "edge"]
            self.assertTrue(edges)
            self.assertTrue(all(r["state"] == state for r in edges))

    def arguments(self, **changes):
        values = dict(binary=FUZZ, mutate_binary=MUTATE, output=self.root / "result.csv",
                      # Functional checks share the host with Dune's other jobs;
                      # dedicated deadline tests below use their own short limits.
                      seconds=15., runs=2, observations=8, problem=[], external=["all"],
                      external_bin=[], tag=[], keep_tools=False, jobs=1,
                      setup_seconds=30., source=False, zipper_ocaml="auto",
                      suite=None, case=[], profile=False)
        return argparse.Namespace(**(values | changes))

    def test_platform_selection_excludes_foreign_archives_and_checksums(self):
        assets = ["vampire-linux-arm64.zip", "vampire-macos-x86_64.zip",
                  "vampire-macos-arm64.zip", "vampire-macos-arm64.sha256",
                  "vampire-macos-universal.tar.gz", "source.tar.gz"]
        selected = [n for n in assets if atp.asset_score(n, "darwin", "arm64")]
        self.assertEqual(selected, [assets[2], assets[4]])
        with mock.patch.object(atp.subprocess, "run") as command:
            command.return_value.stdout = "Mach-O 64-bit executable x86_64"
            self.assertFalse(atp.native_binary("ignored", "darwin", "arm64"))
            command.return_value.stdout = "ELF 64-bit LSB executable, ARM aarch64"
            self.assertTrue(atp.native_binary("ignored", "linux", "arm64"))
            self.assertFalse(atp.native_binary("ignored", "darwin", "arm64"))

    def test_status_errors_timeouts_and_conflicts_are_distinct(self):
        for text, code, timeout, expected in [
            ("% SZS status Unsatisfiable for p", 0, False, "UNSAT"),
            ("# SZS status Satisfiable", 1, False, "SAT"),
            ("% (123) SZS status Theorem for p", 0, False, "UNSAT"),
            ("% SZS status GaveUp", 1, False, "UNKNOWN"),
            ("unknown option --bad", 2, False, "ERROR"),
            ("% SZS status InputError", 1, False, "ERROR"),
            ("% SZS status Unsatisfiable", -9, False, "ERROR"),
            ("% SZS status Unsatisfiable", 0, True, "UNKNOWN"),
            ("% SZS status Satisfiable\n% SZS status Unsatisfiable", 0, False, "ERROR"),
        ]:
            with self.subTest(text=text, code=code, timeout=timeout):
                self.assertEqual(atp.szs_result(text, code, timeout)[0], expected)

    def test_single_search_policy_and_resource_settings_reach_solver(self):
        problem = self.root / "problem.p"
        problem.write_text("cnf(a,axiom,p(a)). cnf(b,axiom,~p(a)).\n")
        row = bench.measure(
            atp.Tool("axiom-fuzzer", FUZZ, {"method": "local", "executable_sha256": atp.sha256(FUZZ)}),
            {"case": "strategy", "path": problem, "problem_sha256": atp.sha256(problem),
             "problem_bytes": problem.stat().st_size, "axioms": 2},
            self.arguments(), self.root, 0, 0, os.environ)
        self.assertEqual(row["result"], "UNSAT")
        self.assertTrue(row["verified"])
        with (self.root / "strategy-000-axiom-fuzzer.csv").open() as stream:
            measured = next(csv.DictReader(stream))
        self.assertEqual((measured["ordered"], measured["clause_weight"], measured["fingerprint"], measured["avatar_enabled"]),
                         ("true", "mixed", "true", "true"))
        command = json.loads(row["command"])
        self.assertIn("--seconds", command)
        for flag in ["--avatar", "--ordered", "--clause-weight"]:
            self.assertNotIn(flag, command)

    def test_zipper_smoke_and_measurement_use_supported_first_order_arguments(self):
        # CLI contract from the actual 2.1 failure log: "best" is not a mode.
        # This fixture checks argument handling; it is not an ATP implementation.
        program = self.executable("""import argparse, json, pathlib
parser = argparse.ArgumentParser()
parser.add_argument('--mode', choices=['fo-complete-basic', 'ho-complete-basic'], required=True)
parser.add_argument('--input', choices=['zf', 'tptp'], required=True)
parser.add_argument('--output', choices=['zf', 'tptp', 'default', 'none'], required=True)
parser.add_argument('--disable-e', action='store_true')
parser.add_argument('--timeout', type=int, required=True)
parser.add_argument('problem', type=pathlib.Path)
args = parser.parse_args()
assert args.mode == 'fo-complete-basic'
assert args.input == args.output == 'tptp'
assert args.disable_e and args.timeout > 0
print(json.dumps(vars(args), default=str))
status = 'Unsatisfiable' if '~p(a)' in args.problem.read_text() else 'Satisfiable'
print('% SZS status ' + status)
""")
        rejected = self.root / "unsupported-mode.log"
        old = atp.run_logged([program, "--mode", "best"], rejected, 15)
        self.assertNotEqual(old["returncode"], 0)
        self.assertIn("invalid choice: 'best'", rejected.read_text())
        releases = atp.Releases(self.root, self.root / "records")
        releases.smoke("zipperposition", program)
        for case in ("unsat", "sat"):
            text = (releases.records / f"zipperposition-{case}.log").read_text()
            self.assertEqual(json.loads(text.splitlines()[0])["mode"], "fo-complete-basic")
        problem = self.root / "zipperposition-unsat.p"
        row = bench.measure(
            atp.Tool("zipperposition", program, {"method": "provided", "executable_sha256": atp.sha256(program)}),
            {"case": "fixture", "path": problem, "problem_sha256": atp.sha256(problem),
             "problem_bytes": problem.stat().st_size, "axioms": 2},
            self.arguments(), self.root, 0, 0, os.environ,
        )
        self.assertEqual(row["result"], "UNSAT")
        self.assertFalse(row["verified"])

    def test_extraction_rejects_escaping_tar_and_zip_entries(self):
        for kind in ("tar", "zip", "link"):
            path = self.root / kind
            if kind == "zip":
                with zipfile.ZipFile(path, "w") as stream:
                    stream.writestr("../escaped", "bad")
            else:
                with tarfile.open(path, "w") as stream:
                    entry = tarfile.TarInfo("../escaped" if kind == "tar" else "link")
                    if kind == "link":
                        entry.type, entry.linkname = tarfile.SYMTYPE, "../escaped"
                    stream.addfile(entry)
            with self.subTest(kind=kind), self.assertRaises((atp.SetupError, tarfile.TarError)):
                atp.unpack(path, self.root / ("unpacked-" + kind))
        self.assertFalse((self.root / "escaped").exists())

    def test_wall_deadline_cancels_descendants(self):
        marker = self.root / "late"
        program = self.executable(
            "import subprocess, sys, time\n"
            "subprocess.Popen([sys.executable, '-c', "
            + repr(f"import time,pathlib;time.sleep(.4);pathlib.Path({str(marker)!r}).write_text('leaked')")
            + "])\ntime.sleep(5)\n")
        result = atp.run_logged([program], self.root / "log", .15)
        self.assertTrue(result["timed_out"])
        self.assertLess(result["wall_seconds"], 2.)
        time.sleep(.45)
        self.assertFalse(marker.exists(), "a descendant outlived the measured process group")

    def test_exited_parent_does_not_leave_background_search(self):
        marker = self.root / "late"
        program = self.executable(
            "import subprocess,sys\nsubprocess.Popen([sys.executable, '-c', "
            + repr(f"import time,pathlib;time.sleep(.3);pathlib.Path({str(marker)!r}).write_text('leaked')")
            + "])\n")
        # Exercise normal parent exit, not a startup deadline under concurrent
        # native/Rocq builds. The marker still checks descendant cleanup.
        result = atp.run_logged([program], self.root / "log", 15)
        self.assertFalse(result["timed_out"])
        self.assertEqual(result["returncode"], 0)
        time.sleep(.4)
        self.assertFalse(marker.exists())

    def test_permission_race_retries_for_running_and_exited_processes(self):
        killpg = os.killpg
        for running in (False, True):
            with self.subTest(running=running):
                program = self.executable("import time\ntime.sleep(30)\n" if running else "pass\n")
                attempts = []
                def deny_once(pid, sig):
                    attempts.append(pid)
                    if len(attempts) == 1:
                        raise PermissionError(1, "fixture: group exit race")
                    return killpg(pid, sig)
                with mock.patch.object(atp.os, "killpg", side_effect=deny_once), \
                        mock.patch.object(atp.threading, "excepthook") as unhandled:
                    result = atp.run_logged([program], self.root / "log", .1 if running else 15)
                self.assertEqual(result["timed_out"], running)
                self.assertEqual(result["returncode"], -signal.SIGKILL if running else 0)
                self.assertGreaterEqual(len(attempts), 2)
                unhandled.assert_not_called()

    def test_persistent_permission_error_aborts_without_hanging(self):
        program = self.executable("import time\ntime.sleep(30)\n")
        processes = []
        popen = subprocess.Popen
        def spawn(*args, **kwargs):
            process = popen(*args, **kwargs)
            processes.append(process)
            return process
        started = time.monotonic()
        with mock.patch.object(atp.subprocess, "Popen", side_effect=spawn), \
                mock.patch.object(atp.os, "killpg", side_effect=PermissionError(1, "fixture: denied")), \
                mock.patch.object(atp.threading, "excepthook") as unhandled:
            with self.assertRaisesRegex(atp.ProcessCleanupError, "cannot stop process group"):
                atp.run_logged([program], self.root / "log", .1)
        self.assertLess(time.monotonic() - started, 5)
        self.assertEqual(processes[0].wait(timeout=1), -signal.SIGKILL)
        unhandled.assert_not_called()

    def test_comparison_stops_and_preserves_rows_after_cleanup_failure(self):
        problem = self.root / "input.p"
        problem.write_text("fof(p,axiom,p).\nfof(n,axiom,~p).\n")
        args = self.arguments(problem=[problem], external=["eprover"],
                              external_bin=[f"eprover={sys.executable}"])
        measure = bench.measure
        def fail_external(tool, *args, **kwargs):
            if tool.name == "eprover":
                raise atp.ProcessCleanupError("fixture: cannot stop process group")
            return measure(tool, *args, **kwargs)
        with mock.patch.object(bench, "native_binary", return_value=True), \
                mock.patch.object(atp.Releases, "smoke"), \
                mock.patch.object(bench, "measure", side_effect=fail_external) as measured, \
                contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaisesRegex(atp.ProcessCleanupError, "cannot stop process group"):
                bench.comparison(args)
        self.assertEqual(measured.call_count, 2)
        with args.output.open() as stream:
            rows = list(csv.DictReader(stream))
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["result"], "UNSAT")
        manifest = json.loads(next(self.root.glob("result-*/manifest.json")).read_text())
        self.assertEqual(manifest["status"], "failed")
        self.assertEqual(manifest["measurements"], 1)
        self.assertIn("cannot stop process group", manifest["error"])

    def test_ctrl_c_preserves_partial_results_without_traceback(self):
        problem = self.root / "input.p"
        problem.write_text("fof(p,axiom,p).\nfof(n,axiom,~p).\n")
        ready = self.root / "ready"
        program = self.executable(
            "import os,pathlib,time\n"
            f"pathlib.Path({str(ready.with_suffix('.tmp'))!r}).write_text(str(os.getpid()))\n"
            f"os.replace({str(ready.with_suffix('.tmp'))!r}, {str(ready)!r})\n"
            "time.sleep(30)\n")
        output = self.root / "result.csv"
        wrapper = self.root / "interrupt.py"
        argv = [str(BENCHMARK), "--binary", str(FUZZ), "--mutate-binary", str(MUTATE),
                "--external", "eprover", "--external-bin", f"eprover={program}",
                "--problem", str(problem), "--runs", "5", "--seconds", "15",
                "--output", str(output)]
        # Bypass native-header and smoke checks only for this protocol fixture.
        wrapper.write_text(
            "import runpy,sys\n"
            f"sys.path.insert(0, {str(BENCHMARK.parent)!r})\n"
            "import external\n"
            "external.native_binary = lambda *args: True\n"
            "external.Releases.smoke = lambda *args: None\n"
            f"sys.argv = {argv!r}\n"
            f"runpy.run_path({str(BENCHMARK)!r}, run_name='__main__')\n")
        parent = subprocess.Popen([sys.executable, "-B", str(wrapper)],
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 15
            while not ready.exists() and parent.poll() is None and time.monotonic() < deadline:
                time.sleep(.01)
            self.assertTrue(ready.exists(), "fixture never started")
            parent.send_signal(signal.SIGINT)
            stdout, stderr = parent.communicate(timeout=5)
            self.assertEqual(parent.returncode, 130, stdout + stderr)
            self.assertIn("Benchmark interrupted.", stderr)
            self.assertNotIn("Traceback", stderr)
            with self.assertRaises(ProcessLookupError):
                os.kill(int(ready.read_text()), 0)
        finally:
            if parent.poll() is None:
                parent.kill()
            parent.communicate(timeout=5)
            if ready.exists():
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(int(ready.read_text()), signal.SIGKILL)
        with output.open() as stream:
            rows = list(csv.DictReader(stream))
        self.assertEqual(len(rows), 1)
        manifest = json.loads(next(self.root.glob("result-*/manifest.json")).read_text())
        self.assertEqual(manifest["status"], "interrupted")
        self.assertEqual(manifest["error"], "KeyboardInterrupt")
        self.assertEqual(manifest["measurements"], len(rows))

    def test_mktemp_is_removed_on_failure(self):
        with self.assertRaisesRegex(RuntimeError, "fixture"):
            with atp.temporary_tools() as root:
                self.assertTrue(root.is_dir())
                (root / "download").write_text("temporary data")
                raise RuntimeError("fixture")
        self.assertFalse(root.exists())

    def test_release_digest_mismatch_is_fatal_before_execution(self):
        temporary, records = self.root / "tools", self.root / "records"
        temporary.mkdir()
        releases = atp.Releases(temporary, records, tags={"eprover": "release-fixture"})
        releases.target = ("darwin", "arm64")
        release = dict(draft=False, prerelease=False, tag_name="release-fixture",
                       html_url="https://github.com/eprover/eprover/releases/tag/release-fixture",
                       id=1, published_at="fixture", assets=[
                           dict(name="eprover-macos-arm64", id=2, browser_download_url="fixture",
                                digest="sha256:" + "0" * 64)])
        def download(command, **kwargs):
            pathlib.Path(command[-1]).write_bytes(b"corrupted")
        with mock.patch.object(releases, "api", return_value=release) as api, \
                mock.patch.object(releases, "execute", side_effect=download), \
                mock.patch.object(releases, "smoke") as smoke, \
                mock.patch.object(releases, "build") as build:
            with self.assertRaisesRegex(atp.SetupError, "digest"):
                releases.install("eprover")
        self.assertIn("/releases/tags/release-fixture", api.call_args.args[0])
        smoke.assert_not_called()
        build.assert_not_called()
        record = json.loads((records / "eprover.json").read_text())
        self.assertFalse(record["ready"])
        self.assertEqual(record["tag"], "release-fixture")

    def test_corpus_is_independent_of_search_time_budget(self):
        first, second = self.root / "first", self.root / "second"
        first.mkdir()
        second.mkdir()
        a = bench.corpus(self.arguments(seconds=.1), first)
        b = bench.corpus(self.arguments(seconds=2.), second)
        self.assertEqual([p["problem_sha256"] for p in a], [p["problem_sha256"] for p in b])
        tool = atp.Tool("axiom-fuzzer", FUZZ, {"method": "local", "executable_sha256": atp.sha256(FUZZ)})
        result = bench.measure(tool, a[0], self.arguments(), self.root, 0, 0, os.environ)
        self.assertEqual(result["result"], "UNSAT")
        self.assertTrue(result["verified"])

    def test_unusable_asset_falls_back_to_the_same_release_source(self):
        temporary, records = self.root / "tools", self.root / "records"
        temporary.mkdir()
        releases = atp.Releases(temporary, records)
        releases.target = ("darwin", "arm64")
        release = dict(draft=False, prerelease=False, tag_name="release-fixture",
                       html_url="fixture", id=1, published_at="fixture", assets=[
                           dict(name="eprover-macos-arm64", id=2,
                                browser_download_url="fixture", digest=None)])
        def download(command, **kwargs):
            pathlib.Path(command[-1]).write_bytes(b"this is not a native executable")
        def build(name, directory, record):
            self.assertEqual(record["tag"], "release-fixture")
            record["method"] = "source"
            return pathlib.Path(sys.executable).resolve()
        with mock.patch.object(releases, "api", return_value=release), \
                mock.patch.object(releases, "execute", side_effect=download), \
                mock.patch.object(releases, "build", side_effect=build), \
                mock.patch.object(releases, "smoke"):
            tool = releases.install("eprover")
        self.assertEqual(tool.provenance["method"], "source")
        self.assertIn("rejected", tool.provenance["asset_attempts"][0])
        self.assertEqual(tool.provenance["tag"], "release-fixture")
        self.assertEqual(tool.provenance["origin"], "release")

    def test_e_release_404_uses_highest_numeric_tag_and_pinned_commit(self):
        temporary, records = self.root / "tools", self.root / "records"
        temporary.mkdir()
        releases = atp.Releases(temporary, records)
        tags = [[{"name": name, "commit": {"sha": sha}} for name, sha in [
            ("origin", "a" * 40), ("E-4.0-rc1", "b" * 40), ("E-3.9", "c" * 40)]],
            [{"name": "E-3.10.1", "commit": {"sha": "d" * 40}}]]
        execute = atp.run_logged
        def github(command, output, seconds, **kwargs):
            if command[0] != "gh":
                return execute(command, output, seconds, **kwargs)
            if command[2].endswith("/releases/latest"):
                self.assertIn("--include", command)
                # GitHub error bodies need not contain a "status" key.
                pathlib.Path(output).write_text('HTTP/2.0 404 Not Found\n\n{"message":"Not Found"}\n')
                code = 1
            else:
                self.assertEqual(command[2], "repos/eprover/eprover/tags?per_page=100")
                self.assertEqual(command[-2:], ["--paginate", "--slurp"])
                pathlib.Path(output).write_text(json.dumps(tags))
                code = 0
            return {"returncode": code, "timed_out": False, "wall_seconds": .001}
        program = self.executable("print('% SZS status Unsatisfiable')\n")
        def build(name, directory, record):
            self.assertEqual(record["commit"], "d" * 40)
            self.assertEqual(record["tag"], "E-3.10.1")
            record["method"] = "source"
            return program
        with mock.patch.object(atp, "run_logged", side_effect=github), \
                mock.patch.object(releases, "build", side_effect=build), \
                mock.patch.object(releases, "smoke"):
            tool = releases.install("eprover")
        self.assertEqual(tool.provenance["origin"], "tag")
        self.assertNotIn("release_id", tool.provenance)
        self.assertTrue((records / "eprover-tag.json").exists())
        self.assertFalse((records / "eprover-release.json").exists())
        problem = temporary / "problem.p"
        problem.write_text("fof(p,axiom,p(a)).")
        row = bench.measure(tool, {"case": "fixture", "path": problem,
                                  "problem_sha256": atp.sha256(problem),
                                  "problem_bytes": problem.stat().st_size, "axioms": 1},
                            self.arguments(), self.root, 0, 0, os.environ)
        self.assertEqual((row["origin"], row["tag"], row["release"]), ("tag", "E-3.10.1", ""))

    def test_release_lookup_does_not_hide_transport_auth_or_server_errors(self):
        for name, body, code, timeout in [
            ("eprover", "", 1, False),  # DNS failure
            ("eprover", "HTTP/2.0 401 Unauthorized\n\n{}", 1, False),
            ("eprover", "HTTP/2.0 403 Forbidden\n\n{}", 1, False),
            ("eprover", "HTTP/2.0 429 Too Many Requests\n\n{}", 1, False),
            ("eprover", "HTTP/2.0 500 Internal Server Error\n\n{}", 1, False),
            ("eprover", "HTTP/2.0 404 Not Found\n\n{}", -9, True),
            ("vampire", '{"status":"404"}', 1, False),
            ("zipperposition", '{"status":"404"}', 1, False),
        ]:
            with self.subTest(name=name, body=body, timeout=timeout):
                releases = atp.Releases(self.root, self.root / "records")
                releases.deadline = time.monotonic() + 10
                def reply(command, output, seconds, **kwargs):
                    pathlib.Path(output).write_text(body)
                    return {"returncode": code, "timed_out": timeout, "wall_seconds": .001}
                with mock.patch.object(atp, "run_logged", side_effect=reply) as run:
                    with self.assertRaises(atp.SetupError):
                        releases.select(name, None)
                    self.assertEqual(run.call_count, 1)

    def test_pinned_e_tag_must_exist_and_never_substitutes_a_branch(self):
        releases = atp.Releases(self.root, self.root / "records")
        tags = [[{"name": "E-3.9", "commit": {"sha": "c" * 40}},
                 {"name": "E-3.10", "commit": {"sha": "d" * 40}}]]
        with mock.patch.object(releases, "api", side_effect=[None, tags]) as api:
            record, assets = releases.select("eprover", "E-3.9")
        self.assertTrue(api.call_args_list[0].args[0].endswith("/releases/tags/E-3.9"))
        self.assertEqual(record["tag"], "E-3.9")
        self.assertEqual(record["commit"], "c" * 40)
        self.assertEqual(assets, [])
        for tag, available in [("missing", tags), (None, []),
                               (None, [[{"name": "origin"}, {"name": "E-4.0-rc1"}]])]:
            with self.subTest(tag=tag, available=available), \
                    mock.patch.object(releases, "api", side_effect=[None, available]):
                with self.assertRaises(atp.SetupError):
                    releases.select("eprover", tag)

    def test_published_release_keeps_priority_over_tags(self):
        releases = atp.Releases(self.root, self.root / "records")
        releases.deadline = time.monotonic() + 10
        release = dict(draft=False, prerelease=False, tag_name="E-3.0", html_url="fixture",
                       id=42, published_at="fixture", assets=[{"name": "eprover-linux-x86_64"}])
        def reply(command, output, seconds, **kwargs):
            self.assertIn("--include", command)
            pathlib.Path(output).write_text("HTTP/2.0 200 OK\r\nContent-Type: application/json\r\n\r\n"
                                           + json.dumps(release))
            return {"returncode": 0, "timed_out": False, "wall_seconds": .001}
        with mock.patch.object(atp, "run_logged", side_effect=reply) as run:
            record, assets = releases.select("eprover", None)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(record["origin"], "release")
        self.assertEqual(record["release_id"], 42)
        self.assertEqual(assets, release["assets"])

    def zipper_build(self, requested="auto", fail_install=False,
                     commit="1051eaafb0040262f1e9acd338e0f605cd2d8c17"):
        """Exercise the preparation order; real dependency solving is separate."""
        directory = self.root / requested
        directory.mkdir()
        source = directory / "source"
        source.mkdir()
        releases = atp.Releases(self.root, directory / "records", zipper_ocaml=requested)
        record = {"tag": "2.1", "commit": commit}
        calls = []
        def execute(command, *, env, output=None, **kwargs):
            calls.append((list(map(str, command)), env.copy()))
            if command[1] == "install" and fail_install:
                raise atp.SetupError("No solution found")
            if output:
                pathlib.Path(output).write_text(
                    "4.12.1\n" if command[1] == "var" else "ocaml 4.12.1\nzipperposition 2.1\n")
        with mock.patch.dict(os.environ, {"OPAMROOT": "/unused-root", "OPAMSWITCH": "unrelated",
                                         "OCAMLPATH": "/unused-libraries"}), \
                mock.patch.object(releases, "source_archive", return_value=(source, "fixture")), \
                mock.patch.object(releases, "submodules"), \
                mock.patch.object(releases, "execute", side_effect=execute), \
                mock.patch.object(atp, "find_binary", return_value=self.root / "zipperposition") as find:
            if fail_install:
                with self.assertRaisesRegex(atp.SetupError, "No solution found"):
                    releases.build("zipperposition", directory, record)
                find.assert_not_called()
            else:
                releases.build("zipperposition", directory, record)
        return directory, record, calls

    def test_zipper_compiler_is_solved_after_pinning_release_in_private_switch(self):
        for requested, compiler in [("auto", "ocaml-base-compiler"),
                                    ("4.12.1", "ocaml-base-compiler.4.12.1")]:
            with self.subTest(requested=requested):
                directory, record, calls = self.zipper_build(requested)
                commands = [command for command, _ in calls]
                switch = next(command for command in commands if command[1] == "switch")
                self.assertIn("--empty", switch)
                self.assertFalse(any(arg.startswith("ocaml-base-compiler") for arg in switch))
                pin = next(i for i, command in enumerate(commands) if command[1] == "pin")
                install = next(i for i, command in enumerate(commands) if command[1] == "install")
                self.assertLess(pin, install)
                self.assertIn("--no-action", commands[pin])
                self.assertEqual(commands[install][-2:], [compiler, "zipperposition"])
                self.assertIn("mtime<2.0", commands[install])
                self.assertIn("menhir<20211215", commands[install])
                self.assertEqual(record["dependency_constraints"], ["mtime<2.0", "menhir<20211215"])
                for command, env in calls:
                    self.assertEqual(env["OPAMROOT"], str(directory / "opam"))
                    self.assertNotIn("OCAMLPATH", env)
                    if command[1] in ("init", "switch"):
                        self.assertNotIn("OPAMSWITCH", env)
                    else:
                        self.assertEqual(env["OPAMSWITCH"], "bench")
                self.assertEqual(record["ocaml_request"], requested)
                self.assertEqual(record["ocaml"], "4.12.1")
                self.assertIn("ocaml 4.12.1", (directory / "records/zipperposition-packages.txt").read_text())
        with mock.patch.object(sys, "argv", [str(BENCHMARK), "--external", "zipperposition"]), \
                mock.patch.object(bench, "comparison") as comparison, \
                contextlib.redirect_stdout(io.StringIO()):
            bench.main()
        self.assertEqual(comparison.call_args.args[0].zipper_ocaml, "auto")

    def test_zipper_incompatible_requested_compiler_does_not_fall_back(self):
        _, record, calls = self.zipper_build("4.14.2", fail_install=True)
        command = calls[-1][0]
        self.assertEqual(command[-2:], ["ocaml-base-compiler.4.14.2", "zipperposition"])
        self.assertEqual(record["ocaml_request"], "4.14.2")
        self.assertNotIn("ocaml", record)
        self.assertFalse(any("--update-invariant" in command for command, _ in calls))

    def test_zipper_dependency_bounds_are_specific_to_the_release_commit(self):
        # A different source under the same tag must not inherit 2.1's bounds.
        _, record, calls = self.zipper_build(commit="b" * 40)
        install = next(command for command, _ in calls if command[1] == "install")
        self.assertNotIn("mtime<2.0", install)
        self.assertNotIn("menhir<20211215", install)
        self.assertEqual(record["dependency_constraints"], [])

    def test_comparison_rotates_solvers_and_persists_identical_inputs(self):
        problem = self.root / "input.p"
        problem.write_text("fof(p,axiom,p(a)).\nfof(n,axiom,~p(a)).\n")
        program = self.executable(
            "import hashlib,pathlib,sys\n"
            "print('input_sha256=' + hashlib.sha256(pathlib.Path(sys.argv[-1]).read_bytes()).hexdigest())\n"
            "print('% SZS status Unsatisfiable for fixture')\n")
        args = self.arguments(problem=[problem],
                              external_bin=[f"{name}={program}" for name in atp.REPOSITORIES])
        # Protocol fixtures exercise the actual runner without acquiring or
        # pretending to measure the real E/Vampire/Zipperposition implementations.
        with mock.patch.object(bench, "native_binary", return_value=True), \
                mock.patch.object(atp.Releases, "smoke"), \
                contextlib.redirect_stdout(io.StringIO()):
            bench.comparison(args)
        with args.output.open() as stream:
            rows = list(csv.DictReader(stream))
        self.assertEqual(len(rows), 8)
        self.assertEqual({r["result"] for r in rows}, {"UNSAT"})
        self.assertEqual({r["problem_sha256"] for r in rows}, {atp.sha256(problem)})
        self.assertNotEqual(rows[0]["solver"], rows[4]["solver"])
        self.assertTrue(all(r["verified"] == "False" for r in rows if r["solver"] != "axiom-fuzzer"))
        artifacts = next(self.root.glob("result-*/manifest.json"))
        metadata = json.loads(artifacts.read_text())
        self.assertEqual(metadata["status"], "complete")
        self.assertFalse(metadata["external_proofs_checked"])
        for row in rows:
            if row["solver"] != "axiom-fuzzer":
                text = (args.output.parent / row["log"]).read_text()
                self.assertIn("input_sha256=" + atp.sha256(problem), text)

    def test_invalid_budgets_and_release_bindings_fail_before_download(self):
        for option, value in [("--seconds", "nan"), ("--seconds", "0"), ("--runs", "0"),
                              ("--setup-seconds", "inf"), ("--observations", "-1")]:
            result = subprocess.run([sys.executable, "-B", str(BENCHMARK), option, value],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
        with self.assertRaises(ValueError):
            bench.bindings(["eprover=v1", "eprover=v2"], "--tag")
        with self.assertRaises(ValueError):
            bench.bindings(["unknown=v1"], "--tag")

    def test_application_corpus_preserves_all_axioms_and_has_distinct_inputs(self):
        args = self.arguments(suite="applications", external=[])
        problems = bench.corpus(args, self.root)
        self.assertEqual(len(problems), 8)
        self.assertEqual(len({p["problem_sha256"] for p in problems}), 8)
        self.assertEqual({p["case"]: p["axioms"] for p in problems}, {
            "SWV001-1": 14, "SWV002-1": 23, "HWV001-1": 47, "SWC078-1": 199,
            "KRS018+1": 4, "KRS063+1": 27, "PLA012-1": 31, "SWV851-1": 669,
        })
        for problem in problems:
            text = problem["path"].read_text()
            self.assertNotIn("include(", text)
            self.assertEqual(problem["library_version"], "6.4.0" if problem["case"] == "SWV851-1" else "9.0.0")
            self.assertTrue(problem["source_files"])
            self.assertIn(problem["expected"], ("SAT", "UNSAT"))
            for record in problem["source_files"].values():
                self.assertIn(problem["source_commit"], record["source_url"])
                self.assertEqual(len(record["sha256"]), 64)
        from corpus import ROOT, applications
        copied = self.root / "tampered"
        shutil.copytree(ROOT, copied, copy_function=shutil.copyfile)
        path = copied / "tptp/Axioms/SWV001-0.ax"
        path.write_text(path.read_text() + "% changed\n")
        with self.assertRaisesRegex(ValueError, "checksum"):
            applications(copied)

    def test_profile_is_exclusive_preserves_proof_and_needs_no_external_tools(self):
        problem = self.root / "input.p"
        problem.write_text("fof(p,axiom,p(a)).\nfof(n,axiom,~p(a)).\n")
        baseline = self.root / "baseline.cert"
        subprocess.run([str(FUZZ), "--problem", str(problem), "--quiet",
                        "--certificate", str(baseline)], check=True, capture_output=True, timeout=15)
        args = self.arguments(problem=[problem], external=[], profile=True, runs=1)
        with mock.patch.object(bench, "temporary_tools") as temporary, \
                mock.patch.object(bench, "Releases") as releases, \
                contextlib.redirect_stdout(io.StringIO()):
            bench.comparison(args)
        temporary.assert_not_called()
        releases.assert_not_called()
        with args.output.open() as stream:
            row = next(csv.DictReader(stream))
        self.assertEqual((row["result"], row["profile_complete"]), ("UNSAT", "True"))
        self.assertEqual((args.output.parent / row["certificate"]).read_bytes(), baseline.read_bytes())
        phases, complete, active = bench.read_profile(args.output.parent / row["profile"])
        self.assertTrue(complete)
        self.assertEqual(active, "")
        self.assertEqual(int(phases["input_read"]["calls"]), 1)
        self.assertEqual(int(phases["input_parse"]["calls"]), 1)
        self.assertEqual(int(phases["theory_copy"]["calls"]), 1)
        for name in ("input_read", "input_parse", "initial_axioms", "search", "proof_extract",
                     "proof_check", "certificate_encode", "certificate_write", "metrics_write"):
            self.assertGreaterEqual(float(phases[name]["seconds"]), 0)
            self.assertGreaterEqual(float(phases[name]["allocated_words"]), 0)
        app = float(row["application_seconds"])
        accounted = sum(float(r["seconds"]) for name, r in phases.items() if name != "application")
        self.assertAlmostEqual(accounted, app, delta=3e-8)
        self.assertAlmostEqual(app + float(row["outside_application_seconds"]),
                               float(row["wall_seconds"]), delta=2e-9)
        self.assertGreater(float(row["application_cpu_seconds"]), 0)
        self.assertGreater(float(row["application_allocated_words"]), 0)
        # A shared input snapshot is parsed once, including parallel/reference
        # portfolios. Only new Source arenas are created for their workers.
        profile = self.root / "parallel.csv"
        for flags, copies in [(["--workers", "2"], 2), (["--workers", "3"], 3)]:
            with self.subTest(flags=flags):
                subprocess.run([str(FUZZ), "--problem", str(problem), "--quiet", *flags,
                                "--profile", str(profile)], check=True,
                               capture_output=True, timeout=15)
                phases, complete, _ = bench.read_profile(profile)
                self.assertTrue(complete)
                self.assertIn("portfolio", phases)
                self.assertNotIn("search", phases)
                self.assertEqual(int(phases["input_read"]["calls"]), 1)
                self.assertEqual(int(phases["input_parse"]["calls"]), 1)
                if copies:
                    self.assertEqual(int(phases["theory_copy"]["calls"]), copies)
                else:
                    self.assertNotIn("theory_copy", phases)
        subprocess.run([str(FUZZ), "--theory", "naive", "--quiet",
                        "--workers", "2", "--profile", str(profile)], check=True,
                       capture_output=True, timeout=15)
        phases, complete, _ = bench.read_profile(profile)
        self.assertTrue(complete)
        self.assertEqual(int(phases["theory_setup"]["calls"]), 1)
        self.assertEqual(int(phases["theory_copy"]["calls"]), 2)
        self.assertNotIn("input_parse", phases)

    def test_profile_keeps_completed_stages_when_killed_and_reports_errors(self):
        profile = self.root / "partial.csv"
        command = [str(FUZZ), "--theory", "zf", "--quiet",
                   "--seconds", "30", "--max-instances", "1000000",
                   "--max-given", "1000000", "--max-generated", "100000000",
                   "--profile", str(profile)]
        process = subprocess.Popen(command, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            until = time.monotonic() + 10
            while time.monotonic() < until and process.poll() is None:
                if profile.exists() and "search,start," in profile.read_text():
                    break
                time.sleep(.005)
            else:
                self.fail("search did not start while profiling")
            process.kill()
            process.wait(timeout=5)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait(timeout=5)
        phases, complete, active = bench.read_profile(profile)
        self.assertFalse(complete)
        self.assertEqual(active, "search")
        self.assertIn("initial_axioms", phases)
        self.assertNotIn("search", phases)
        self.assertNotIn("application", phases)
        # An interrupted final write cannot become a completed measurement.
        with profile.open("a") as stream:
            stream.write("search,end,1.0")
        self.assertEqual(bench.read_profile(profile), (phases, complete, active))
        error_profile = self.root / "error.csv"
        result = subprocess.run([str(FUZZ), "--problem", str(self.root / "missing.p"),
                                 "--profile", str(error_profile)], capture_output=True, timeout=15)
        self.assertEqual(result.returncode, 2)
        phases, complete, _ = bench.read_profile(error_profile)
        self.assertFalse(complete)
        self.assertEqual(phases["application"]["event"], "error")

    def test_known_satisfiable_case_rejects_an_incorrect_refutation(self):
        program = self.executable("print('% SZS status Unsatisfiable for fixture')\n")
        args = self.arguments(suite="applications", case=["KRS018+1"], runs=1,
                              external=[], external_bin=[f"eprover={program}"])
        with mock.patch.object(bench, "native_binary", return_value=True), \
                mock.patch.object(atp.Releases, "smoke"), \
                contextlib.redirect_stdout(io.StringIO()), \
                self.assertRaisesRegex(RuntimeError, "unexpected definitive"):
            bench.comparison(args)
        metadata = json.loads(next(self.root.glob("result-*/manifest.json")).read_text())
        self.assertEqual(metadata["status"], "failed")
        self.assertEqual(metadata["conflicts"], [])
        self.assertEqual(metadata["expected_mismatches"], ["KRS018+1"])

    def test_local_suite_and_profile_cli_do_not_require_an_external_solver(self):
        with mock.patch.object(sys, "argv", [str(BENCHMARK), "--suite", "applications",
                                            "--case", "SWV001-1", "--profile"]), \
                mock.patch.object(bench, "comparison") as comparison, \
                contextlib.redirect_stdout(io.StringIO()):
            bench.main()
        args = comparison.call_args.args[0]
        self.assertEqual(args.suite, "applications")
        self.assertEqual(args.case, ["SWV001-1"])
        self.assertEqual(args.external, [])
        self.assertTrue(args.profile)
        with self.assertRaisesRegex(ValueError, "unknown cases"):
            bench.corpus(self.arguments(suite="applications", case=["misspelled"]), self.root)


unittest.main(verbosity=2)
