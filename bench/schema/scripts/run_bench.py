#!/usr/bin/env python3
"""Run the schema-contradiction benchmark (schema_bench.exe run CASE ...).

usage: python3 -I run_bench.py --variant NAME=BIN[ FLAGS] [--variant ...] --out NEWDIR
           [--seconds S] [--workers W] [--repeats R] [--jobs J] [--batch B]
           [--cases C ...] [--seed N] [--slots DIR] [--skip-from DIR ...] [--extra FLAG ...]

Every (variant, case, repeat) trial is one process. Trials run in batches of
B (default 1) under one slot acquisition of weight workers + 1 (heuristic
workers + reference Domain), one trial after the other, so a busy shared pool
is queried once per batch.
Trials are interleaved in a seeded random order so that variants share the
same load. The case list defaults to `BIN list` of the first variant, so
newly registered cases are included automatically. Each binary re-checks every
UNSAT certificate with Kernel.check on a fresh theory copy after an
encode/decode roundtrip and prints result=REJECTED otherwise.
Writes NEWDIR/results.jsonl, NEWDIR/<variant>-<case>-r<k>.log and prints a
summary (see summarize.py). --skip-from DIR resumes an interrupted run: trials
whose log in DIR already holds a result line are skipped (merge the results
with summarize.py DIR NEWDIR).
"""
import argparse
import json
import random
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import benchlib  # noqa: E402
import summarize  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--variant", action="append", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--seconds", type=float, default=10)
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--repeats", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--batch", type=int, default=1)
    ap.add_argument("--cases", nargs="*")
    ap.add_argument("--seed", type=int, default=503)
    ap.add_argument("--slots")
    ap.add_argument("--skip-from", action="append", default=[])
    ap.add_argument("--extra", nargs=argparse.REMAINDER, default=[])
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=False)
    variants = [benchlib.parse_variant(v) for v in args.variant]
    cases = args.cases or benchlib.list_cases(variants[0][1])
    acquire = benchlib.slot_pool(args.slots)
    trials = [(v, c, r) for r in range(args.repeats) for c in cases for v in variants]
    random.Random(args.seed).shuffle(trials)

    def finished(directory, name, case, rep):
        log = Path(directory) / f"{name}-{case}-r{rep}.log"
        return log.exists() and any(
            benchlib.parse_result(line) for line in log.read_text(errors="replace").splitlines())

    trials = [t for t in trials
              if not any(finished(d, t[0][0], t[1], t[2]) for d in args.skip_from)]
    (out / "meta.json").write_text(json.dumps({
        "variants": [{"name": n, "binary": b, "flags": f} for n, b, f in variants],
        "cases": cases, "seconds": args.seconds, "workers": args.workers,
        "repeats": args.repeats, "jobs": args.jobs, "batch": args.batch, "seed": args.seed,
        "extra": args.extra,
    }, indent=1))

    def one(trial):
        (name, binary, flags), case, rep = trial
        cmd = [binary, "run", case, "--seconds", str(args.seconds), "--workers",
               str(args.workers)] + args.extra + flags
        log = out / f"{name}-{case}-r{rep}.log"
        t0 = time.time()
        with open(log, "w") as f:
            try:
                code = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT,
                                      timeout=args.seconds * 3 + 60).returncode
            except subprocess.TimeoutExpired:
                code = "timeout"
        wall = time.time() - t0
        res = {"variant": name, "case": case, "repeat": rep, "code": code,
               "wall": round(wall, 3), "result": "ERROR"}
        for line in log.read_text(errors="replace").splitlines():
            parsed = benchlib.parse_result(line)
            if parsed:
                res.update(parsed)
        return res

    def batch(group):
        with acquire(args.workers + 1):
            return [one(trial) for trial in group]

    size = max(1, args.batch)
    groups = [trials[i:i + size] for i in range(0, len(trials), size)]
    with ThreadPoolExecutor(args.jobs) as ex:
        results = [r for group in ex.map(batch, groups) for r in group]
    results.sort(key=lambda r: (r["variant"], r["case"], r["repeat"]))
    with open(out / "results.jsonl", "w") as f:
        for r in results:
            f.write(json.dumps(r) + "\n")
    summarize.report(results, [v[0] for v in variants], cases)


if __name__ == "__main__":
    main()
