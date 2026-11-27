"""The memory budget reads deterministic engine counts, never the garbage collector.

With the scheduling costs on a stopped clock (AXIOM_MEASURE_COST_CLOCK=stopped) a bounded search
depends on its input alone. Its budget readings and responses (budget_checks, the digest of every
reading and response, the peak reading, the responses, drops and trims, and the stop) must then
be the same for worker 0 in process and in Domain mode, at 1 and at 4 workers, under different
OCAMLRUNPARAM collector settings, and with or without other solver runs beside it. Worker 0 runs
production alone in every configuration: at 4 workers by the default composition, at 1 worker by the
A/A portfolio (--eval-strategies production). The default single worker time-shares production
with e208 under the same budget: both engines read the worker's whole state. On this input
production stops at the budget first and e208 runs on alone until the deadline; production's
readings, responses and slices repeat in every mode and collector setting.
"""
import csv
import os
import pathlib
import subprocess
import sys
import tempfile

import clean_environment

clean_environment.scrub()

fuzz, problem = (pathlib.Path(p).resolve() for p in sys.argv[1:])
FIELDS = ["budget_checks", "budget_digest", "peak_footprint_words", "budget_responses",
          "budget_heap_responses", "budget_cursor_drops", "budget_trimmed", "given", "generated",
          "reason"]
SLICES = ["slice_main_slices", "slice_main_work", "slice_main_given", "slice_main_generated"]
CONFIGS = [
    ("processes-w1", "1", {}),
    ("processes-w4", "4", {}),
    ("domains-w4", "4", {"AXIOM_MEASURE_PORTFOLIO": "domains"}),
    ("domains-w1", "1", {"AXIOM_MEASURE_PORTFOLIO": "domains"}),
    ("small-minor-eager-major", "1", {"OCAMLRUNPARAM": "s=4k,o=20"}),
    ("large-minor-lazy-major", "1", {"OCAMLRUNPARAM": "s=8M,o=400"}),
]


PRODUCTION = ["--eval-strategies", "production"]


def start(temp, name, workers, extra, args=None):
    if args is None:
        args = PRODUCTION if workers == "1" else []
    out = temp / (name + ".csv")
    env = dict(os.environ)
    # The fixture must reach the budget responses and trimming (asserted below). Under the default
    # equivalence rule (derive), SWV851-1 keeps each rewritten clause next to its original and reaches
    # the 2x ceiling after one response, so the budget machinery is exercised under redundant, which
    # rewrites the same way without adding the derived clauses. The rule does not touch the readings.
    # Without the reference worker (which would run to the wall limit) a run ends when its
    # workers stop at the budget, long before this deadline, also on a heavily loaded machine.
    env.update(AXIOM_MEASURE_COST_CLOCK="stopped", AXIOM_EQUIVALENCE="redundant",
               AXIOM_MEASURE_REFERENCE="off", **extra)
    cmd = [str(fuzz), "--problem", str(problem), "--seconds", "120", "--quiet", "--memory-budget", "3",
           "--workers", workers, *args, "--worker-metrics", str(out)]
    return name, subprocess.Popen(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  text=True), out


def worker0(name, proc, out, fields=FIELDS):
    stdout, stderr = proc.communicate(timeout=600)
    assert proc.returncode == 0, (name, proc.returncode, stdout, stderr)
    row = next(r for r in csv.DictReader(out.open()) if r["worker"] == "0")
    return {k: row[k] for k in fields}


with tempfile.TemporaryDirectory(prefix="axiom-fuzzer-budget-") as temp:
    temp = pathlib.Path(temp)
    # Alone first, then every configuration at once (each run is load for the others).
    alone = worker0(*start(temp, "alone", "1", {}))
    assert alone["reason"] == "memory budget exhausted", alone
    assert int(alone["budget_responses"]) >= 2 and int(alone["budget_trimmed"]) > 0, alone
    assert int(alone["budget_cursor_drops"]) > 0 and len(alone["budget_digest"]) == 16, alone
    runs = [start(temp, name, workers, extra) for name, workers, extra in CONFIGS]
    for name, proc, out in runs:
        row = worker0(name, proc, out)
        assert row == alone, (name, row, alone)
    # The default single worker: production and e208 time-shared under one budget.
    share = worker0(*start(temp, "share", "1", {}, []), FIELDS + SLICES)
    assert share["reason"] == "memory budget exhausted; e208+0~ ran on alone", share
    assert int(share["budget_responses"]) >= 2 and int(share["budget_trimmed"]) > 0, share
    runs = [start(temp, "share-" + name, workers, extra, []) for name, workers, extra in CONFIGS
            if workers == "1"]
    for name, proc, out in runs:
        row = worker0(name, proc, out, FIELDS + SLICES)
        assert row == share, (name, row, share)
    # The switch accepts only its two values.
    bad = subprocess.run([str(fuzz), "--theory", "naive", "--seconds", "0.1", "--quiet"],
                         env=dict(os.environ, AXIOM_MEASURE_COST_CLOCK="paused"),
                         capture_output=True, text=True, timeout=60)
    assert bad.returncode == 2 and "AXIOM_MEASURE_COST_CLOCK" in bad.stderr, bad
print("ok  budget readings and responses are the same in every mode, worker count, GC setting and load")
