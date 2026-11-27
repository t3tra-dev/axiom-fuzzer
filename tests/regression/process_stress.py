"""Adversarial reclamation stress test of the process portfolio (CLI level, stdlib only).

Every trial starts `axiom-fuzz` in its own session (as benchmark drivers do) with a random
configuration and injects random signals at random times across start-up, the run and
shutdown: SIGTERM, SIGINT, SIGHUP, SIGKILL, SIGSEGV, SIGABRT or a SIGSTOP that is continued
later, sent to the CLI, to its process group, to one of its forked children or to all of them.
Afterwards it checks the reclamation invariants:

  * no process is left: every trial passes a unique marker in its argv (the output directory),
    and forked children carry the supervisor's argv, so `ps` finds any survivor;
  * no temporary file is left in the trial's directory or in the private TMPDIR; two kinds are
    counted apart: the one file a CLI that received SIGKILL itself may leave in the middle of
    writing its own output (named with its dead PID; the target is never partial), and the file
    of a reference killed while saving whose supervisor was SIGKILLed before reaping it, which
    must be removed by the next run with the same checkpoint directory (the trial runs it);
  * defined exit behaviour: the CLI exits 0 with a "Result:" line unless a signal sent to the
    CLI itself (or its group) killed it, and it never exceeds its stop and kill deadlines.

process_stress.py FUZZ [--trials N] [--jobs J] [--seed S] [--max-seconds X] [--max-workers W]
                       [--out DIR] [--slots-module FILE] [--quiet]
--slots-module names a Python file whose acquire(weight) context manager is held around each
trial's CLI process (a machine-wide slot pool); without it trials run unthrottled.
"""
import argparse
import importlib.util
import json
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import clean_environment

clean_environment.scrub()

SIGNALS = {"TERM": signal.SIGTERM, "INT": signal.SIGINT, "HUP": signal.SIGHUP,
           "KILL": signal.SIGKILL, "SEGV": signal.SIGSEGV, "ABRT": signal.SIGABRT,
           "STOP": signal.SIGSTOP}
CLI_SIGNALS = ["TERM", "INT", "HUP", "KILL", "STOP", "TERM", "KILL"]
CHILD_SIGNALS = ["TERM", "INT", "HUP", "KILL", "SEGV", "ABRT", "STOP", "KILL"]
# Stop and kill deadlines of the supervisor (Portfolio.default_timing) plus scheduling slack.
MARGIN, GRACE, REFERENCE_GRACE, PROOF_GRACE, SLACK = 0.5, 1.0, 10.0, 10.0, 5.0
SETTLE = 2.0  # how long survivors may take to go after the CLI is reaped


def ps_lines():
    out = subprocess.run(["ps", "-e", "-ww", "-o", "pid=,ppid=,stat=,args="],
                         capture_output=True, text=True).stdout
    return [line.split(None, 3) for line in out.splitlines() if len(line.split(None, 3)) == 4]


def marked(marker):
    return [(int(p), int(pp), st, cmd) for p, pp, st, cmd in ps_lines() if marker in cmd]


def children(pid):
    out = subprocess.run(["pgrep", "-P", str(pid)], capture_output=True, text=True).stdout
    return sorted(int(x) for x in out.split())


def send(pid, sig, group=False):
    try:
        if group:
            os.killpg(pid, sig)
        else:
            os.kill(pid, sig)
        return True
    except (ProcessLookupError, PermissionError):
        return False


def plan(rng, max_seconds, max_workers):
    seconds = rng.choice([s for s in (0.3, 0.6, 1.0, 1.5, 2.5) if s <= max_seconds] or [0.3])
    workers = rng.choice([w for w in (1, 1, 2, 2, 3, 4) if w <= max_workers])
    theory = rng.choice(["zf", "zf", "zf", "naive"])
    checkpoint = rng.random() < 0.35
    injections = []
    for _ in range(rng.choice([1, 1, 2, 2, 3])):
        phase = rng.choice(["startup", "run", "run", "shutdown"])
        at = {"startup": rng.uniform(0.0, 0.06),
              "run": rng.uniform(0.06, max(0.07, seconds)),
              "shutdown": rng.uniform(max(0.0, seconds - 0.05), seconds + MARGIN + GRACE + 0.2)}[phase]
        target = rng.choice(["cli", "group", "child", "child", "children"])
        name = rng.choice(CLI_SIGNALS if target in ("cli", "group") else CHILD_SIGNALS)
        resume = rng.uniform(0.05, 1.5) if name == "STOP" else None
        injections.append(dict(at=round(at, 4), phase=phase, target=target, signal=name,
                               resume=None if resume is None else round(resume, 4)))
    injections.sort(key=lambda i: i["at"])
    return dict(seconds=seconds, workers=workers, theory=theory, checkpoint=checkpoint,
                injections=injections)


def trial(fuzz, root, n, p, slots_acquire, private_tmp):
    marker = f"axstress-{os.getpid()}-{n}-{random.getrandbits(32):08x}"
    tdir = root / marker
    tdir.mkdir()
    cmd = [fuzz, "--theory", p["theory"], "--seconds", str(p["seconds"]), "--workers",
           str(p["workers"]), "--max-instances", "1000000", "--quiet",
           "--metrics", str(tdir / "metrics.csv"), "--worker-metrics", str(tdir / "workers.csv"),
           "--certificate", str(tdir / "proof.cert")]
    if p["checkpoint"]:
        cmd += ["--checkpoint", str(tdir / "reference.checkpoint")]
    env = dict(os.environ, TMPDIR=str(private_tmp), AXIOM_MEASURE_PORTFOLIO="processes")
    sent = []  # (signal name, target, delivered)
    resumes = []
    gate = slots_acquire(p["workers"] + 1) if slots_acquire else _null()
    with gate:  # held while the CLI runs, released once it is reaped
        out = open(tdir / "stdout.txt", "wb")
        err = open(tdir / "stderr.txt", "wb")
        started = time.monotonic()
        proc = subprocess.Popen(cmd, stdout=out, stderr=err, start_new_session=True, env=env)
        out.close()
        err.close()
        limit = p["seconds"] + MARGIN + max(GRACE, PROOF_GRACE,
                                            REFERENCE_GRACE if p["checkpoint"] else 0) + SLACK

        def resume(now):
            for r in [r for r in resumes if r[0] <= now]:
                resumes.remove(r)
                # Also whatever the CLI forked meanwhile (a group stop can catch a child
                # between its fork and its setsid).
                for pid in r[1] + (children(proc.pid) if proc.returncode is None else []):
                    send(pid, signal.SIGCONT)

        pending = list(p["injections"])
        while proc.poll() is None and time.monotonic() - started <= limit:
            now = time.monotonic() - started
            resume(now)
            if pending and pending[0]["at"] <= now:
                inj = pending.pop(0)
                sig = SIGNALS[inj["signal"]]
                kids = children(proc.pid)
                if inj["target"] == "cli":
                    targets, ok = [proc.pid], send(proc.pid, sig)
                elif inj["target"] == "group":
                    targets, ok = [proc.pid], send(proc.pid, sig, group=True)
                elif inj["target"] == "child":
                    targets = [random.choice(kids)] if kids else []
                    ok = any([send(t, sig) for t in targets])
                else:
                    targets = kids
                    ok = any([send(t, sig) for t in targets])
                sent.append((inj["signal"], inj["target"], ok, round(now, 4)))
                if inj["signal"] == "STOP" and targets:
                    # The stopper owns what it stopped: it continues it later, also after the
                    # CLI is gone (an orphaned child then ends through its lifeline).
                    resumes.append((now + inj["resume"],
                                    targets + (kids if inj["target"] == "group" else [])))
            time.sleep(0.002)
        hung = proc.poll() is None
        if hung:  # past every stop and kill deadline: continue everything, then kill
            for pid in children(proc.pid):
                send(pid, signal.SIGCONT)
            send(proc.pid, signal.SIGCONT)
            try:
                proc.wait(timeout=3.0)
            except subprocess.TimeoutExpired:
                send(proc.pid, signal.SIGKILL)
                proc.wait()
        wall = time.monotonic() - started
        code = proc.returncode
    # No solver of ours runs any more unless the reclamation failed: continue what we stopped,
    # then look for survivors carrying the marker.
    while resumes:
        resume(time.monotonic() - started)
        time.sleep(0.002)
    reaped = time.monotonic()
    alive = marked(marker)
    while alive and time.monotonic() - reaped < SETTLE:
        time.sleep(0.002)
        alive = marked(marker)
    lived = time.monotonic() - reaped
    for pid, _, _, _ in alive:  # never let a failure accumulate processes
        send(pid, signal.SIGCONT)
        send(pid, signal.SIGKILL)
    stdout = (tdir / "stdout.txt").read_text(errors="replace")
    stderr = (tdir / "stderr.txt").read_text(errors="replace")
    expected = {"stdout.txt", "stderr.txt", "metrics.csv", "workers.csv", "proof.cert",
                "reference.checkpoint", "reference.checkpoint.lock"}
    files = sorted(os.listdir(tdir))
    stray = [f for f in files if f not in expected]
    cli_killed = any(s[0] == "KILL" and s[1] in ("cli", "group") and s[2] for s in sent)
    cli_temp = [f for f in stray if re.fullmatch(rf"\.axiom-fuzzer-{proc.pid}-.*\.tmp", f)]
    if cli_killed:
        stray = [f for f in stray if f not in cli_temp]
    else:
        cli_temp = []
    deferred = []
    orphan_temp = [f for f in stray if re.fullmatch(r"\.axiom-fuzzer-\d+-.*\.tmp", f)]
    if cli_killed and p["checkpoint"] and orphan_temp:
        # A reference killed while saving whose supervisor was killed before it could reap it:
        # nobody alive can remove its temporary file, so the next run with this checkpoint
        # directory must.
        follow = [fuzz, "--theory", "zf", "--seconds", "0.05", "--workers", "1",
                  "--max-instances", "1000", "--quiet",
                  "--checkpoint", str(tdir / "reference.checkpoint")]
        with (slots_acquire(2) if slots_acquire else _null()):
            subprocess.run(follow, capture_output=True, env=env, timeout=60)
        deferred = [f for f in orphan_temp if not (tdir / f).exists()]
        stray = [f for f in stray if f not in deferred]
    tmp_left = sorted(os.listdir(private_tmp))
    cli_signals = {-SIGNALS[s[0]] for s in sent if s[1] in ("cli", "group") and s[2]
                   and s[0] != "STOP"}
    problems = []
    if alive:
        problems.append(f"leftover processes: {[(a[0], a[2]) for a in alive]}")
    if stray:
        problems.append(f"leftover files: {stray}")
    if tmp_left:
        problems.append(f"files in TMPDIR: {tmp_left}")
    if hung:
        problems.append("the CLI missed its stop and kill deadlines")
    if code == 0:
        if "Result: " not in stdout:
            problems.append("exit 0 without a Result line")
    elif code not in cli_signals:
        problems.append(f"exit {code} not caused by a signal to the CLI: {stderr.strip()[:300]}")
    result = dict(n=n, marker=marker, plan=p, sent=sent, exit=code, wall=round(wall, 3),
                  hung=hung, result=(re.search(r"Result: (\w+)", stdout) or [None, None])[1],
                  survivors=len(alive), settle=round(lived, 4), cli_killed=cli_killed,
                  cli_temp=cli_temp, deferred_temp=deferred, problems=problems)
    if not problems:
        shutil.rmtree(tdir, ignore_errors=True)
    return result


class _null:
    def __enter__(self):
        return None

    def __exit__(self, *exc):
        return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("fuzz")
    ap.add_argument("--trials", type=int, default=24)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--seed", type=int, default=503)
    ap.add_argument("--max-seconds", type=float, default=1.0)
    ap.add_argument("--max-workers", type=int, default=4)
    ap.add_argument("--out")
    ap.add_argument("--slots-module")
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args()
    acquire = None
    if a.slots_module:
        spec = importlib.util.spec_from_file_location("slots", a.slots_module)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        acquire = mod.acquire
    rng = random.Random(a.seed)
    plans = [plan(rng, a.max_seconds, a.max_workers) for _ in range(a.trials)]
    root = Path(tempfile.mkdtemp(prefix="axiom-fuzzer-stress-"))
    lock = threading.Lock()
    rows = []
    log = open(Path(a.out) / "trials.jsonl", "a") if a.out else None

    def one(item):
        n, p = item
        private_tmp = root / f"tmp-{n}"
        private_tmp.mkdir()
        r = trial(a.fuzz, root, n, p, acquire, private_tmp)
        if not r["problems"]:
            shutil.rmtree(private_tmp, ignore_errors=True)
        with lock:
            rows.append(r)
            if log:
                log.write(json.dumps(r) + "\n")
                log.flush()
            if not a.quiet or r["problems"]:
                print(f"[{len(rows)}/{a.trials}] exit={r['exit']} wall={r['wall']} "
                      f"sent={[(s[0], s[1]) for s in r['sent']]} "
                      f"{'FAIL ' + '; '.join(r['problems']) if r['problems'] else 'ok'}",
                      flush=True)
        return r

    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        list(pool.map(one, enumerate(plans)))
    failed = [r for r in rows if r["problems"]]
    killed = [r for r in rows if r["cli_killed"]]
    summary = dict(trials=len(rows), failed=len(failed),
                   leftover_processes=sum(r["survivors"] for r in rows),
                   leftover_files=sum(1 for r in rows for q in r["problems"] if "files" in q),
                   hung=sum(r["hung"] for r in rows),
                   cli_sigkilled=len(killed),
                   cli_temp_files=sum(len(r["cli_temp"]) for r in rows),
                   deferred_temp_files_removed_by_next_run=sum(len(r["deferred_temp"]) for r in rows),
                   signals_sent=sum(len(r["sent"]) for r in rows),
                   signals_delivered=sum(1 for r in rows for s in r["sent"] if s[2]),
                   exits={str(c): sum(1 for r in rows if r["exit"] == c)
                          for c in sorted({r["exit"] for r in rows})},
                   phases={ph: sum(1 for r in rows for i in r["plan"]["injections"]
                                   if i["phase"] == ph)
                           for ph in ("startup", "run", "shutdown")},
                   max_wall_over_budget=round(max((r["wall"] - r["plan"]["seconds"] for r in rows),
                                                  default=0.0), 3))
    if a.out:
        (Path(a.out) / "summary.json").write_text(json.dumps(summary, indent=1))
    if not failed:
        shutil.rmtree(root, ignore_errors=True)
    print(json.dumps(summary))
    if failed:
        print(f"{len(failed)} trial(s) failed; kept in {root}", file=sys.stderr)
        sys.exit(1)
    print(f"ok  process reclamation stress: {len(rows)} trials, "
          f"{summary['signals_delivered']} signals delivered, 0 leftovers")


if __name__ == "__main__":
    main()
