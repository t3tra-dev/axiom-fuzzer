#!/usr/bin/env python3
"""Default-engine schema synthesis and late-equality regression measurements."""
import argparse
import csv
import pathlib
import statistics
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--binary", type=pathlib.Path, default=ROOT / "_build/default/bin/fuzz/main.exe")
parser.add_argument("--runs", type=int, default=5)
parser.add_argument("--output", type=pathlib.Path, default=ROOT / "_build/synthesis.csv")
args = parser.parse_args()
if args.runs < 1:
    parser.error("--runs must be positive")
rows = []
with tempfile.TemporaryDirectory(prefix="axiom-synthesis-") as tmp:
    tmp = pathlib.Path(tmp)
    late = tmp / "late-equality.p"
    n = 100
    late.write_text("\n".join(
        [f"fof(old{i},axiom,(p{i}(f(a)) | ~q{i}(a)))." for i in range(n)]
        + ["fof(rule,axiom,(![X]:f(X)=X))."]
        + [f"fof(q{i},axiom,q{i}(a))." for i in range(n)]
        + ["fof(n,axiom,~p0(a))."]))
    cases = [
        ("late_equality", ["--problem", str(late)], "UNSAT"),
        ("foundation", ["--theory", "foundation-self"], "UNSAT"),
        ("separation_universal", ["--theory", "separation-universal"], "UNSAT"),
        ("zf", ["--theory", "zf", "--max-instances", "8", "--max-given", "100"], "UNKNOWN"),
    ]
    for case, base, expected in cases:
        for mode, flags in [("default", [])]:
            for run in range(args.runs):
                metrics = tmp / "metrics.csv"
                subprocess.run([str(args.binary), "--quiet", "--seconds", "3",
                                "--max-given", "1000", "--max-generated", "30000", "--max-retained", "25000",
                                "--metrics", str(metrics), *base, *flags], check=True, capture_output=True, timeout=15)
                with metrics.open() as stream:
                    row = dict(next(csv.DictReader(stream)), case=case, mode=mode, run=run)
                if row["result"] != expected:
                    raise RuntimeError((case, mode, row["result"], row["reason"]))
                rows.append(row)
    for case, base in [("naive_atomic", ["--theory", "naive", "--max-instances", "4"]),
                       ("zf_guidance", ["--theory", "zf", "--max-instances", "8", "--max-given", "100"])]:
        for mode, flags in [("default", [])]:
            for run in range(args.runs):
                metrics = tmp / "metrics.csv"
                subprocess.run([str(args.binary), "--quiet", "--seconds", "3",
                                "--max-given", "300", "--max-generated", "10000", "--max-retained", "8000",
                                "--metrics", str(metrics), *base, *flags],
                               check=True, capture_output=True, timeout=15)
                with metrics.open() as stream:
                    row = dict(next(csv.DictReader(stream)), case=case, mode=mode, run=run)
                expected = "UNSAT" if case == "naive_atomic" else "UNKNOWN"
                if row["result"] != expected:
                    raise RuntimeError((case, mode, row["result"], row["reason"]))
                rows.append(row)
args.output.parent.mkdir(parents=True, exist_ok=True)
with args.output.open("w", newline="") as target:
    writer = csv.DictWriter(target, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)
for case, mode in dict.fromkeys((r["case"], r["mode"]) for r in rows):
    group = [r for r in rows if (r["case"], r["mode"]) == (case, mode)]
    median = statistics.median(float(r["seconds"]) for r in group) * 1000
    r = group[0]
    print(f"{case} {mode}: {median:.3f} ms {r['result']}, generated={r['generated']}, "
          f"backward={r['backward_demodulated']}, guided={r['guided_instances']}, used={r['guided_used_instances']}")
print(args.output)
