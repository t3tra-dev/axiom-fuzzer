#!/usr/bin/env python3
"""ZF fixed-axiom mutant sweep (293 single-site mutants, schemas kept).

usage: python3 -I sweep_mutants.py --variant NAME=BIN[ FLAGS] [--variant ...] --out NEWDIR
           [--seconds 1] [--chunk 25] [--jobs 2] [--slots DIR] [--total 293]

Each chunk of mutants is one `BIN mutants --seconds S --start I --limit N
[FLAGS]` process (one heuristic worker + reference Domain: slot weight 2).
Chunks of all variants are interleaved in a seeded order. Add a variant with
the flag --no-schemas to measure the fixed axioms alone (schema-dependence).
Writes NEWDIR/<variant>.log (chunk logs concatenated in mutant order).
Analyse with analyze_mutants.py.
"""
import argparse
import json
import random
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import benchlib  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--variant", action="append", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--seconds", type=float, default=1)
    ap.add_argument("--chunk", type=int, default=25)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--total", type=int, default=293)
    ap.add_argument("--seed", type=int, default=503)
    ap.add_argument("--slots")
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=False)
    (out / "chunks").mkdir()
    variants = [benchlib.parse_variant(v) for v in args.variant]
    acquire = benchlib.slot_pool(args.slots)
    (out / "meta.json").write_text(json.dumps({
        "variants": [{"name": n, "binary": b, "flags": f} for n, b, f in variants],
        "seconds": args.seconds, "chunk": args.chunk, "total": args.total}, indent=1))
    chunks = [(v, s) for v in variants for s in range(0, args.total, args.chunk)]
    random.Random(args.seed).shuffle(chunks)

    def run(job):
        (name, binary, flags), start = job
        log = out / "chunks" / f"{name}-{start:04d}.log"
        cmd = [binary, "mutants", "--seconds", str(args.seconds), "--start", str(start),
               "--limit", str(args.chunk)] + flags
        with acquire(2), open(log, "w") as f:
            subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT,
                           timeout=args.chunk * (args.seconds * 3 + 10) + 60)

    with ThreadPoolExecutor(args.jobs) as ex:
        list(ex.map(run, chunks))
    for name, _, _ in variants:
        with open(out / f"{name}.log", "w") as f:
            for start in range(0, args.total, args.chunk):
                f.write((out / "chunks" / f"{name}-{start:04d}.log").read_text(errors="replace"))
    print("done:", [v[0] for v in variants])


if __name__ == "__main__":
    main()
