#!/usr/bin/env python3
"""Summarize one or more run_bench.py output directories.

usage: python3 -I summarize.py DIR [DIR ...] [--base NAME]

Per variant: solved per repeat, cases solved in every repeat / in at least one,
REJECTED/ERROR counts, and per case the solved fraction and the median time of
the solved trials. With --base, cases gained/lost against that variant
(majority over repeats).
"""
import json
import re
import statistics
import sys
from collections import defaultdict
from pathlib import Path


def load_logs(d):
    """Finished trials of an interrupted run_bench.py directory (no results.jsonl)."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import benchlib
    meta = json.loads((d / "meta.json").read_text())
    names = sorted((v["name"] for v in meta["variants"]), key=len, reverse=True)
    rows = []
    for log in sorted(d.glob("*.log")):
        m = re.match(r"(.*)-r(\d+)$", log.stem)
        variant = m and next((n for n in names if m.group(1).startswith(n + "-")), None)
        if not variant:
            continue
        result = None
        for line in log.read_text(errors="replace").splitlines():
            result = benchlib.parse_result(line) or result
        if result:
            result.update({"variant": variant, "case": m.group(1)[len(variant) + 1:],
                           "repeat": int(m.group(2))})
            rows.append(result)
    return rows


def load(dirs):
    results = []
    for d in map(Path, dirs):
        if (d / "results.jsonl").exists():
            results += [json.loads(line) for line in (d / "results.jsonl").read_text().splitlines()]
        else:
            results += load_logs(d)
    return results


def report(results, variants=None, cases=None, base=None):
    variants = variants or sorted({r["variant"] for r in results})
    cases = cases or sorted({r["case"] for r in results})
    by = defaultdict(list)
    for r in results:
        by[(r["variant"], r["case"])].append(r)
    repeats = max((r["repeat"] for r in results), default=0) + 1
    print(f"{'variant':24} " + " ".join(f"r{k}" for k in range(repeats))
          + "  all  any  rejected error")
    majority = {}
    for v in variants:
        per_rep = [sum(1 for c in cases for r in by[(v, c)]
                       if r["repeat"] == k and r["result"] == "UNSAT") for k in range(repeats)]
        solved = {c: sum(r["result"] == "UNSAT" for r in by[(v, c)]) for c in cases}
        n = {c: len(by[(v, c)]) for c in cases}
        all_ = sum(1 for c in cases if n[c] and solved[c] == n[c])
        any_ = sum(1 for c in cases if solved[c] > 0)
        rej = sum(1 for c in cases for r in by[(v, c)] if r["result"] == "REJECTED")
        err = sum(1 for c in cases for r in by[(v, c)] if r["result"] == "ERROR")
        majority[v] = {c for c in cases if n[c] and 2 * solved[c] > n[c]}
        print(f"{v:24} " + " ".join(f"{x:2d}" for x in per_rep)
              + f"  {all_:3d}  {any_:3d}  {rej:8d} {err:5d}")
    print()
    print(f"{'case':22} " + " ".join(f"{v[:16]:>16}" for v in variants))
    for c in cases:
        cells = []
        for v in variants:
            rs = by[(v, c)]
            ok = [r["seconds"] for r in rs if r["result"] == "UNSAT"]
            cell = f"{len(ok)}/{len(rs)}"
            if ok:
                cell += f" {statistics.median(ok):.3f}s"
            cells.append(f"{cell:>16}")
        print(f"{c:22} " + " ".join(cells))
    if base and base in majority:
        print()
        for v in variants:
            if v == base:
                continue
            gained = sorted(majority[v] - majority[base])
            lost = sorted(majority[base] - majority[v])
            print(f"{v} vs {base} (majority): +{len(gained)} {gained} -{len(lost)} {lost}")


if __name__ == "__main__":
    args = sys.argv[1:]
    base = None
    if "--base" in args:
        i = args.index("--base")
        base = args[i + 1]
        del args[i:i + 2]
    report(load(args), base=base)
