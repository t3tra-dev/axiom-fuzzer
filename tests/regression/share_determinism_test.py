"""One balanced worker time-shares production and e208 on the work clock: same input, same search.

The single-worker default runs production as the continuing engine and one resumed e208 lane at
queue phase 0, 1:1 in slices of the work clock (allocated words plus 20 per cooperative check),
never of wall time. With the scheduling costs on a stopped clock (AXIOM_MEASURE_COST_CLOCK=stopped)
the whole search then depends on its input alone. A bounded run (each engine stops at its
given-clause cap) must repeat exactly: alone and beside other solver runs, in process and in Domain
mode, and under different OCAMLRUNPARAM collector settings, which change when the collector runs
but not what the worker allocates. The e208 slices suspend production and never perturb it: the
continuing engine's search is the A/A portfolio's (--eval-strategies production), which runs
production alone, while its budget readings also count the lane's state whenever production holds
the larger part (the worker's budget covers both engines), so they never read less. Production reaches its cap first; e208 then runs on alone
to its own cap, and the worker's reason says so.
"""
import csv
import os
import pathlib
import subprocess
import sys
import tempfile

import clean_environment

clean_environment.scrub()

fuzz = pathlib.Path(sys.argv[1]).resolve()
# Satisfiable (non-abelian groups with p true and q false everywhere are models), with equality,
# non-unit clauses and a negated goal: neither engine refutes it or saturates soon.
PROBLEM = """cnf(left_identity, axiom, mult(e, X) = X).
cnf(left_inverse, axiom, mult(inv(X), X) = e).
cnf(associativity, axiom, mult(mult(X, Y), Z) = mult(X, mult(Y, Z))).
cnf(not_commutative, negated_conjecture, mult(a, b) != mult(b, a)).
cnf(p_or_q, axiom, p(X) | q(X)).
cnf(p_closed, axiom, p(mult(X, Y)) | ~p(X)).
cnf(not_both, axiom, ~q(e) | ~p(e)).
"""
SHARE = "[e208+0~] unit=15000000 work geometric:1 ratio=1 carry"
SEARCH = ["given", "generated", "reason", "budget_checks", "budget_digest", "peak_footprint_words"]
SLICES = ["slice_policy", "slice_main_slices", "slice_probe_slices", "slice_main_steps",
          "slice_probe_steps", "slice_main_work", "slice_probe_work", "slice_probes_created",
          "slice_peak_live_probes", "slice_probe_given", "slice_probe_generated", "slice_probe_admitted",
          "slice_winner", "slice_winner_slice", "slice_main_given", "slice_main_generated",
          "slice_main_retained"]
CONFIGS = [
    ("processes", [], {}),
    ("domains", [], {"AXIOM_MEASURE_PORTFOLIO": "domains"}),
    ("small-minor-eager-major", [], {"OCAMLRUNPARAM": "s=4k,o=20"}),
    ("large-minor-lazy-major", [], {"OCAMLRUNPARAM": "s=8M,o=400"}),
    ("again", [], {}),
]


def start(temp, problem, name, args, extra):
    out = temp / (name + ".csv")
    # Both engines stop at their given-clause cap long before the wall limit, also on a loaded
    # machine; without the reference worker (which would run to the wall limit) the run ends there.
    env = dict(os.environ, AXIOM_MEASURE_COST_CLOCK="stopped", AXIOM_MEASURE_REFERENCE="off", **extra)
    cmd = [str(fuzz), "--problem", str(problem), "--seconds", "120", "--quiet", "--max-given", "120",
           "--worker-metrics", str(out), *args]
    return name, subprocess.Popen(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  text=True), out


def worker0(name, proc, out):
    stdout, stderr = proc.communicate(timeout=600)
    assert proc.returncode == 0 and "Result: UNKNOWN" in stdout, (name, proc.returncode, stdout, stderr)
    return next(r for r in csv.DictReader(out.open()) if r["worker"] == "0")


with tempfile.TemporaryDirectory(prefix="axiom-fuzzer-share-") as temp:
    temp = pathlib.Path(temp)
    problem = temp / "groups.p"
    problem.write_text(PROBLEM)
    alone = worker0(*start(temp, problem, "alone", [], {}))
    assert alone["slice_policy"] == SHARE, alone["slice_policy"]
    assert alone["reason"] == "given clause limit; e208+0~ ran on alone", alone["reason"]
    # One e208 engine, admitted once and resumed; both engines ran several slices.
    assert alone["slice_probes_created"] == "1" and alone["slice_peak_live_probes"] == "1", alone
    assert int(alone["slice_main_slices"]) >= 3 and int(alone["slice_probe_slices"]) >= 2, alone
    assert int(alone["slice_probe_given"]) > 0 and alone["slice_winner"] == "", alone
    reference = {k: alone[k] for k in SEARCH + SLICES}
    runs = [start(temp, problem, name, args, extra) for name, args, extra in CONFIGS]
    production = start(temp, problem, "production", ["--eval-strategies", "production"], {})
    for name, proc, out in runs:
        row = worker0(name, proc, out)
        assert {k: row[k] for k in SEARCH + SLICES} == reference, (name, row, reference)
    row = worker0(*production)
    assert row["slice_policy"] == "off" and row["slice_probes_created"] == "0", row["slice_policy"]
    assert row["reason"] + "; e208+0~ ran on alone" == alone["reason"], (row, alone)
    same = ["given", "generated", "budget_checks"]
    assert {k: row[k] for k in same} == {k: alone[k] for k in same}, (row, alone)
    assert int(alone["peak_footprint_words"]) >= int(row["peak_footprint_words"]), (row, alone)
print("ok  the single-worker share repeats its search in every mode, GC setting and load, "
      "and leaves production's search unchanged")
