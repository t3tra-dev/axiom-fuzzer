"""Randomized reclamation trials of the process portfolio at the API level (stdlib only).

process_chaos.py CHAOS_EXE [--trials N] [--jobs J] [--seed S] [--kill-supervisor P] [--out DIR]
                 [--quiet]
--kill-supervisor P adds, with probability P per trial, a SIGKILL of the supervisor at a
uniformly random time (start-up, run or shutdown).

Each trial runs `process_chaos.exe MARKER SEED DIR` (see process_chaos.ml): a forked supervisor
with synthetic children (no search) under random signals to the supervisor and the children.
The marker is passed only in argv; every process of the trial (the trial, its supervisor and
their forked children) carries it, so after the trial `ps` finds any survivor. A trial fails if
a process with its marker is still there after the settle time, if its directory or private
TMPDIR holds a file, or if the trial reports a problem (a child left unreaped by a live
supervisor, a missed deadline, an undefined exit).
"""
import argparse
import json
import os
import random
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

SETTLE = 2.0


def marked(marker):
    out = subprocess.run(["ps", "-e", "-ww", "-o", "pid=,stat=,args="], capture_output=True,
                         text=True).stdout
    found = []
    for line in out.splitlines():
        parts = line.split(None, 2)
        if len(parts) == 3 and marker in parts[2]:
            found.append((int(parts[0]), parts[1]))
    return found


def trial(exe, root, n, seed, kill_p):
    marker = f"axchaos-{os.getpid()}-{n}-{random.getrandbits(32):08x}"
    tdir, tmp = root / marker, root / f"tmp-{n}"
    tdir.mkdir()
    tmp.mkdir()
    env = dict(os.environ, TMPDIR=str(tmp))
    try:
        out = subprocess.run([exe, marker, str(seed), str(tdir), str(kill_p)], capture_output=True,
                             text=True, env=env, timeout=60)
        code, stdout, stderr = out.returncode, out.stdout, out.stderr
    except subprocess.TimeoutExpired as e:
        code, stdout, stderr = None, e.stdout or "", "trial timed out"
    reaped = time.monotonic()
    alive = marked(marker)
    while alive and time.monotonic() - reaped < SETTLE:
        time.sleep(0.002)
        alive = marked(marker)
    settle = time.monotonic() - reaped
    for pid, _ in alive:
        try:
            os.kill(pid, signal.SIGCONT)
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    try:
        row = json.loads(stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        row = {"problem": f"no trial report (exit {code}): {stderr.strip()[:300]}"}
    problems = []
    if row.get("problem"):
        problems.append(row["problem"])
    if code != 0:
        problems.append(f"trial exit {code}")
    if alive:
        problems.append(f"leftover processes: {alive}")
    left = sorted(os.listdir(tdir)) + sorted(os.listdir(tmp))
    if left:
        problems.append(f"leftover files: {left}")
    row.update(n=n, marker=marker, survivors=len(alive), settle=round(settle, 4), problems=problems)
    if not problems:
        shutil.rmtree(tdir, ignore_errors=True)
        shutil.rmtree(tmp, ignore_errors=True)
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("exe")
    ap.add_argument("--trials", type=int, default=100)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--seed", type=int, default=503)
    ap.add_argument("--kill-supervisor", type=float, default=0.0)
    ap.add_argument("--out")
    ap.add_argument("--quiet", action="store_true")
    a = ap.parse_args()
    # dune before 3.24 passes the executable as a bare name ("process_chaos.exe"), which
    # subprocess would look up on PATH: resolve it against the working directory.
    a.exe = str(Path(a.exe).resolve())
    root = Path(tempfile.mkdtemp(prefix="axiom-fuzzer-chaos-"))
    rng = random.Random(a.seed)
    seeds = [rng.getrandbits(30) for _ in range(a.trials)]
    lock = threading.Lock()
    rows = []
    log = open(Path(a.out) / "trials.jsonl", "a") if a.out else None

    def one(item):
        n, seed = item
        r = trial(a.exe, root, n, seed, a.kill_supervisor)
        with lock:
            rows.append(r)
            if log:
                log.write(json.dumps(r) + "\n")
                log.flush()
            if not a.quiet or r["problems"]:
                print(f"[{len(rows)}/{a.trials}] code={r.get('code')} wall={r.get('wall')} "
                      f"behaviours={r.get('behaviours')} sent={[(s['target'], s['signal']) for s in r.get('sent', [])]} "
                      f"{'FAIL ' + '; '.join(r['problems']) if r['problems'] else 'ok'}", flush=True)
        return r

    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        list(pool.map(one, enumerate(seeds)))
    failed = [r for r in rows if r["problems"]]
    behaviours = {}
    for r in rows:
        for b in r.get("behaviours", []):
            behaviours[b] = behaviours.get(b, 0) + 1
    signals = {}
    for r in rows:
        for s in r.get("sent", []):
            key = f"{s['target']}:{s['signal']}"
            signals[key] = signals.get(key, 0) + 1
    summary = dict(trials=len(rows), failed=len(failed),
                   leftover_processes=sum(r["survivors"] for r in rows),
                   supervisor_killed=sum(1 for r in rows if r.get("code") == -9),
                   codes={str(c): sum(1 for r in rows if r.get("code") == c)
                          for c in sorted({r.get("code") for r in rows if r.get("code") is not None})},
                   behaviours=behaviours, signals=signals,
                   max_settle=max((r["settle"] for r in rows), default=0.0))
    if a.out:
        (Path(a.out) / "summary.json").write_text(json.dumps(summary, indent=1))
    if not failed:
        shutil.rmtree(root, ignore_errors=True)
    print(json.dumps(summary))
    if failed:
        print(f"{len(failed)} trial(s) failed; kept in {root}", file=sys.stderr)
        sys.exit(1)
    print(f"ok  process reclamation chaos: {len(rows)} trials, 0 leftovers")


if __name__ == "__main__":
    main()
