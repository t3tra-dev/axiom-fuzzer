"""The evaluation switches: one documented list, a notice when one is set, none set by default.

docs/evaluation-switches.md must show the table that `axiom-fuzz --eval-help` prints (both come
from Eval.switches), a run with a switch set must say so on standard error, and a run without one
must not.
"""
import os
import pathlib
import subprocess
import sys

fuzz, doc = (pathlib.Path(p).resolve() for p in sys.argv[1:])
env = {k: v for k, v in os.environ.items() if not k.startswith("AXIOM_")}
table = subprocess.run([str(fuzz), "--eval-help"], capture_output=True, text=True, check=True,
                       timeout=20).stdout
assert table.startswith("| Variable |") and table.count("\n| `AXIOM_") >= 19, table
assert table in doc.read_text(), (
    "docs/evaluation-switches.md does not show the current `axiom-fuzz --eval-help` table")
args = [str(fuzz), "--theory", "naive", "--seconds", "5", "--quiet"]
plain = subprocess.run(args, capture_output=True, text=True, timeout=60, env=env)
assert plain.returncode == 0 and "evaluation overrides" not in plain.stderr, plain
noted = subprocess.run(args + ["--eval-strategies", "production"], capture_output=True, text=True,
                       timeout=60, env=dict(env, AXIOM_MEASURE_COST_CLOCK="stopped"))
assert noted.returncode == 0, noted
assert ("Note: evaluation overrides active: AXIOM_MEASURE_COST_CLOCK=stopped, "
        "--eval-strategies=production\n") in noted.stderr, noted.stderr
quiet = subprocess.run(args, capture_output=True, text=True, timeout=60,
                       env=dict(env, AXIOM_MEASURE_COST_CLOCK="wall"))
assert quiet.returncode == 0 and "evaluation overrides" not in quiet.stderr, quiet
print("ok  evaluation switches: documented as --eval-help lists them, and noted when set")
