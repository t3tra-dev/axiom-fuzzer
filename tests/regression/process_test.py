"""CLI contracts of the forked-process portfolio: signals, external kills, and no orphans."""
import csv
import os
import pathlib
import signal
import subprocess
import sys
import tempfile
import time

import clean_environment

clean_environment.scrub()
fuzz = pathlib.Path(sys.argv[1]).resolve()
LONG = ["--theory", "zf", "--seconds", "30", "--max-instances", "1000000", "--quiet"]


def children(pid):
    out = subprocess.run(["pgrep", "-P", str(pid)], capture_output=True, text=True).stdout
    return [int(x) for x in out.split()]


def alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    # A zombie still answers kill(0); it is not running.
    state = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout
    return bool(state.strip()) and not state.strip().startswith("Z")


def start(args, env=None, session=False):
    process = subprocess.Popen([str(fuzz), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, env=env, start_new_session=session)
    deadline = time.monotonic() + 10
    while time.monotonic() < deadline:
        kids = children(process.pid)
        if len(kids) >= 3:  # two heuristic workers and the reference
            return process, kids
        assert process.poll() is None, process.communicate()
        time.sleep(0.02)
    process.kill()
    raise AssertionError("worker processes did not start")


def gone(pids, within):
    deadline = time.monotonic() + within
    while time.monotonic() < deadline:
        if not any(alive(p) for p in pids):
            return True
        time.sleep(0.02)
    return False


with tempfile.TemporaryDirectory(prefix="axiom-fuzzer-process-") as temp:
    temp = pathlib.Path(temp)
    metrics, workers = temp / "metrics.csv", temp / "workers.csv"

    # SIGINT, SIGTERM and SIGHUP stop cooperatively: every worker reports and is reaped.
    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        process, kids = start([*LONG, "--workers", "2", "--metrics", str(metrics),
                               "--worker-metrics", str(workers)])
        time.sleep(0.3)
        started = time.monotonic()
        process.send_signal(sig)
        stdout, stderr = process.communicate(timeout=15)
        assert process.returncode == 0 and "Result: UNKNOWN" in stdout, (sig, stdout, stderr)
        assert "cancelled" in stdout, stdout
        assert time.monotonic() - started < 5
        assert gone(kids, 1), f"{sig}: worker processes outlived the CLI"
        report = next(csv.DictReader(metrics.open()))
        assert report["isolation"] == "processes" and report["lost_workers"] == "0", report
        rows = list(csv.DictReader(workers.open()))
        assert [r["worker"] for r in rows] == ["0", "1"]
        assert all(r["worker_exit"] == "exit 0" and int(r["given"]) > 0 for r in rows), rows
        assert int(report["total_given"]) == sum(int(r["given"]) for r in rows)
        assert float(report["processes_peak_rss_bytes"]) >= sum(float(r["worker_peak_rss_bytes"]) for r in rows)

    # An external SIGKILL of one worker (a memory watchdog) loses only that worker.
    process, kids = start([*LONG, "--seconds", "2", "--workers", "2", "--metrics", str(metrics),
                           "--worker-metrics", str(workers)])
    os.kill(kids[0], signal.SIGKILL)
    stdout, stderr = process.communicate(timeout=20)
    assert process.returncode == 0 and "Result: UNKNOWN" in stdout, (stdout, stderr)
    assert "lost" in stdout, stdout
    report = next(csv.DictReader(metrics.open()))
    assert report["lost_workers"] == "1", report
    assert gone(kids, 1)

    # A supervisor killed with its whole process group (as benchmark drivers do) cannot stop its
    # workers: they run in their own sessions, notice that their parent is gone, and exit.
    process, kids = start([*LONG, "--workers", "2"], session=True)
    os.killpg(process.pid, signal.SIGKILL)
    process.communicate(timeout=10)
    assert gone(kids, 5), "orphaned worker processes kept running"

    # The Domain portfolio stays reachable for A/A measurements; unknown values are rejected.
    env = dict(os.environ, AXIOM_MEASURE_PORTFOLIO="domains")
    out = subprocess.run([str(fuzz), "--theory", "naive", "--workers", "2", "--quiet",
                          "--metrics", str(metrics)], env=env, capture_output=True, text=True, timeout=20)
    assert out.returncode == 0 and "Result: UNSAT" in out.stdout, out
    assert next(csv.DictReader(metrics.open()))["isolation"] == "domains"
    env = dict(os.environ, AXIOM_MEASURE_PORTFOLIO="threads")
    out = subprocess.run([str(fuzz), "--theory", "naive", "--quiet"], env=env, capture_output=True,
                         text=True, timeout=20)
    assert out.returncode == 2 and "AXIOM_MEASURE_PORTFOLIO" in out.stderr, out
print("ok  process portfolio signals, external kills, orphans, and A/A switch")
