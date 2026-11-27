#!/usr/bin/env python3
"""Summarize sweep_mutants.py output directories.

usage: python3 -I analyze_mutants.py DIR [DIR ...] --base NAME [--noschema NAME] [--list]

For every variant: UNSAT count, REJECTED/ERROR count, kept/lost of the base
variant's UNSAT mutants, gains, and the median time on the base-solved
mutants. With --noschema (a variant run with --no-schemas), the
schema-dependent subset is the mutants refuted by some schema variant but not
by the fixed axioms alone at that budget. Variants from several DIRs are
merged by name (later DIRs win on name clashes).
"""
import re
import statistics
import sys
from pathlib import Path

MUTANT = re.compile(r"mutant=(\d+) axiom=(\S+) operator=(\S+) path=(\S*) formula=(.*)")
RESULT = re.compile(r"case=mutant-(\d+) result=(\S+) seconds=(\S+)(.*)")


def load(path):
    res, meta = {}, {}
    for line in Path(path).read_text(errors="replace").splitlines():
        m = MUTANT.match(line)
        if m:
            meta[int(m.group(1))] = (m.group(2), m.group(3), m.group(5))
            continue
        m = RESULT.match(line)
        if m:
            inst = re.search(r"instances=\[(.*)\]", line)
            src = re.search(r"source=(\S+)", line)
            res[int(m.group(1))] = (m.group(2), float(m.group(3)),
                                    inst.group(1) if inst else "", src.group(1) if src else "")
    return res, meta


def main():
    args = sys.argv[1:]
    opts = {}
    for key in ("--base", "--noschema"):
        if key in args:
            i = args.index(key)
            opts[key] = args[i + 1]
            del args[i:i + 2]
    show = "--list" in args
    args = [a for a in args if a != "--list"]
    runs, meta = {}, {}
    for d in args:
        for log in sorted(Path(d).glob("*.log")):
            res, m = load(log)
            runs[log.stem] = res
            meta.update(m)
    ids = sorted(meta)
    base = opts.get("--base")
    nos = opts.get("--noschema")
    unsat = {v: {i for i in ids if r.get(i, ("?",))[0] == "UNSAT"} for v, r in runs.items()}
    print(f"mutants: {len(ids)}")
    if nos:
        fo = unsat[nos]
        schema_variants = [v for v in runs if v != nos]
        dep = {i for v in schema_variants for i in unsat[v]} - fo
        print(f"fixed axioms alone ({nos}): {len(fo)}; schema-dependent "
              f"(refuted by a schema variant, not by {nos}): {len(dep)}")
    for v in sorted(runs):
        r = runs[v]
        bad = sum(1 for i in ids if r.get(i, ("?",))[0] in ("REJECTED", "ERROR"))
        missing = sum(1 for i in ids if i not in r)
        line = f"{v:24} UNSAT {len(unsat[v]):4d}  rejected/error {bad}  missing {missing}"
        if base and v != base:
            kept = len(unsat[base] & unsat[v])
            lost = sorted(unsat[base] - unsat[v])
            gained = sorted(unsat[v] - unsat[base])
            line += f"  kept {kept}/{len(unsat[base])} lost {len(lost)} gained {len(gained)}"
            if lost:
                line += f" LOST={lost[:20]}"
        if base:
            times = [r[i][1] for i in unsat[base] if i in r and r[i][0] == "UNSAT"]
            if times:
                line += f"  median_t(base-solved) {statistics.median(times):.3f}s"
        if nos and v != nos:
            line += f"  schema-dep {len(unsat[v] & dep)}/{len(dep)}"
        print(line)
    if show and base:
        for v in sorted(runs):
            if v == base:
                continue
            for i in sorted(unsat[v] ^ unsat[base]):
                ax, op, f = meta[i]
                r = runs[v].get(i) or runs[base].get(i)
                tag = "GAIN" if i in unsat[v] else "LOSS"
                print(f"{v} {tag} #{i} {ax} {op} t={r[1]:.3f} src={r[3]} inst=[{r[2][:80]}] :: {f[:100]}")


if __name__ == "__main__":
    main()
