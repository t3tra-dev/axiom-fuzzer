#!/usr/bin/env python3
"""Compare executable revisions with one common production search interface."""
import argparse
import csv
import pathlib
import statistics
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=pathlib.Path, default=pathlib.Path("_build/default/bin/fuzz/main.exe"))
    parser.add_argument("--output", type=pathlib.Path, default=pathlib.Path("_build/improvements.csv"))
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--baseline", type=pathlib.Path, help="earlier executable to compare")
    args = parser.parse_args()
    if args.runs < 1:
        parser.error("--runs must be positive")
    binaries = {"current": args.binary}
    if args.baseline:
        binaries["baseline"] = args.baseline
    rows = []
    with tempfile.TemporaryDirectory(prefix="axiom-improvements-") as tmp:
        metrics = pathlib.Path(tmp) / "metrics.csv"
        for theory in ("naive", "separation-universal", "foundation-self", "mutated-separation", "separation", "zf"):
            for name, binary in binaries.items():
                group = []
                for run in range(args.runs):
                    subprocess.run([str(binary.resolve()), "--theory", theory, "--quiet",
                                    "--seconds", "3", "--max-given", "100", "--max-generated", "10000",
                                    "--metrics", str(metrics)], check=True, capture_output=True, timeout=15)
                    with metrics.open() as source:
                        row = dict(next(csv.DictReader(source)), theory=theory, variant=name, run=run)
                    rows.append(row)
                    group.append(row)
                print(theory, name, "median_ms=", round(statistics.median(float(r["seconds"]) for r in group)*1000, 3),
                      "generated=", group[0]["generated"], "retained=", group[0]["retained"],
                      "subsumption_trials=", group[0]["subsumption_trials"], flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as target:
        writer = csv.DictWriter(target, fieldnames=list(dict.fromkeys(key for row in rows for key in row)))
        writer.writeheader()
        writer.writerows(rows)


if __name__ == "__main__":
    main()
