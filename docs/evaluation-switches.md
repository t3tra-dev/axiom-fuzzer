# Evaluation switches

These switches exist for measurements, A/B runs against earlier rules and diagnostics. None of them
is a user option, none is needed to use `axiom-fuzz`, and any of them may change or disappear in a
0.x release. With all of them unset, `axiom-fuzz` runs its default search. When any of them is set,
`axiom-fuzz` prints one line on standard error before it starts, for example

```text
Note: evaluation overrides active: AXIOM_MEASURE_COST_CLOCK=stopped, --eval-strategies=e208
```

## Environment variables read by axiom-fuzz

`lib/scheduler/eval.ml` holds this list (`Eval.switches`) and is the only place that parses these
variables; `axiom-fuzz --eval-help` prints the table below. *Search* switches change the search.
*Certificate* switches change how a found proof is written, not the search. *Measurement* switches
change how a run is clocked, isolated or traced. *Diagnostic* switches print internal counters on
standard error. An invalid value stops `axiom-fuzz` with an error (exit status 2) before any search
starts. The schema benchmark (`bench/schema/schema_bench.exe`) reads `AXIOM_MEASURE_COST_CLOCK` only.

| Variable | Kind | Values | Unset | Effect |
| --- | --- | --- | --- | --- |
| `AXIOM_PHASE_BASE` | search | integer 0..1000000 | 0 | Adds K to every worker's queue phase (worker 0 starts at phase K). |
| `AXIOM_EQ_UNFOLD` | search | off, on, or an integer limit -1000000..1000000 | each strategy's own setting | Replaces the equational-definition unfolding of every worker strategy: off, on with E's eq-unfold-limit, or on with the given limit. |
| `AXIOM_LEAN_NF` | search | rewrite, both, given or off | rewrite | Sets the lean workers' normal-form rewriting and immediate processing of a simplified given clause: the rewriting only, both, the immediate processing only, or neither (production's one-step admission and re-queued given). |
| `AXIOM_LEAN_EQ` | search | on, off, or a comma-separated subset of inst, gj, cc | off | Sets the unit-equality redundancy tests (EQ-UNIT) of the lean workers with ordered rewriting: instances, ground joinability and connectedness. |
| `AXIOM_EQUIVALENCE` | search | redundant, legacy or derive | derive | Chooses when Contraction's literal rewriting with an equivalence may retire the rewritten clause: only as a redundancy deletion (redundant); on any strict decrease, units included (legacy, a refutationally incomplete rule kept for A/B runs); or as redundant, with the other rewrites added as consequences without retiring anything (derive). |
| `AXIOM_LEAN_LOOP` | search | ported, e, presat, or a comma-separated list of loop details | each heuristic's own loop | Replaces the E loop details of every ported E heuristic worker. |
| `AXIOM_LANE` | search | comma-separated key=value overrides | the default probe lane | Overrides the schema probe lane's evaluation options: clock=alloc\|events, main_weight, ev_main, ev_engine, ev_raw, luby, luby_levels, share, mace, mace_precheck, oe, pad=T:A. |
| `AXIOM_SLICES` | search | off, on, share, or overrides of the slice candidate | share for one worker on an input without schemas | Replaces the probe slices of a single worker whatever its portfolio and input; members= can name any strategy. |
| `AXIOM_GROUND_EXPLANATION` | certificate | forest or short | short | Chooses how the ground congruence closure explains a conflict: along the union-find forest (forest) or, for a long final conflict, along the cheapest paths with shared lemmas (short). The certificate changes, the search does not. |
| `AXIOM_AVATAR_REFUTATION` | certificate | incremental or smaller | smaller | Chooses the Boolean refutation of an AVATAR certificate outside the Vampire members: the incremental solver's (incremental), or the one with fewer steps of the incremental and a fresh re-solve of the same inputs after pruning (smaller). |
| `AXIOM_MEASURE_COST_CLOCK` | measurement | wall or stopped | wall | stopped charges the scheduling costs to a stopped clock, so that a bounded search depends on its input alone (the time limit still reads the wall clock). |
| `AXIOM_MEASURE_REFERENCE` | measurement | on or off | on | off runs no reference worker, so that a search that caps end stops with its heuristic workers (the reference worker runs to the wall limit). For tests and identity checks; --checkpoint needs the reference worker. |
| `AXIOM_MEASURE_PORTFOLIO` | measurement | processes or domains | processes | Runs the portfolio as forked processes or as Domains of one process. |
| `AXIOM_MEASURE_GIVEN_TRACE` | measurement | a file prefix | off | Every lean (ported E heuristic) worker writes one line per given clause to the file PREFIX.PID of its process, to compare its given clauses with E's. |
| `AXIOM_MEASURE_EVAL_TRACE` | measurement | a file prefix | off | The same for every clause that enters Passive, with its evaluations. |
| `AXIOM_MEASURE_NEW_TRACE` | measurement | any value but 0 | off | With AXIOM_MEASURE_GIVEN_TRACE, also writes every clause that enters Passive. |
| `AXIOM_EQ_UNFOLD_REPORT` | diagnostic | any value but 0 | off | Every engine that unfolds equational definitions prints what it removed and rewrote. |
| `AXIOM_LEAN_EQ_REPORT` | diagnostic | any value but 0 | off | Every lean worker that ran an EQ-UNIT redundancy test prints its counters when it stops. |
| `AXIOM_EQUIVALENCE_REPORT` | diagnostic | any value but 0 | off | Every engine prints its counters of literal rewriting with equivalences when it stops. |
| `AXIOM_VAMPIRE_ORDERING` | diagnostic | any value but 0 | off | Every Vampire slice member prints its precedence, KBO weights and predicate levels. |

## Evaluation-only command-line options

Both are hidden from `axiom-fuzz --help`.

- `--eval-strategies SPEC` sets the strategy of every worker: `balanced` (the default), `standard`
  (worker 1 runs calc:e), one strategy name for every worker, or a comma-separated list with one
  name per worker. The default search reaches only production, calc:e, e208, y1346 and sat001; the
  other strategy names are evaluation baselines, reachable only through this option or
  `AXIOM_SLICES` (`members=`).
- `--eval-help` prints the table above.

## Variables that axiom-fuzz does not read

| Variable | Read by | Effect |
| --- | --- | --- |
| `AXIOM_MARK_TRIALS`, `AXIOM_MARK_SEED` | `tests/unit/unit_tests.ml` | Trial count (default 400) and seed (default 29) of the randomized index-cursor test, to run it as a stress test. |
| `AXIOM_PROOF_FIXTURES` | `tests/regression/proof_builder_tests.ml` | A directory where the test writes each checked problem and certificate it builds. |
| `AXIOM_FUZZER_ROCQ_SWITCH` | `scripts/rocq-editor.py` | The opam switch of the Rocq editor toolchain (default: opam's active switch; without opam, the tools on `PATH`). |
| `AXIOM_FUZZER_STDLIB_SOURCE` | `scripts/rocq-editor.py` | A Rocq Stdlib source directory to build when the switch has no compiled Stdlib. |
| `AXF_SLOTS_DIR` | `bench/schema/scripts/benchlib.py`, `bench/schema/scripts/lane_calibrate.py` | A directory with a `slots.py` whose `acquire(weight)` throttles benchmark processes machine-wide. |

The tests remove every `AXIOM_*` variable and the OCaml runtime parameters from the environment of
the processes they start (`tests/regression/clean_environment.py`), so a variable set in a
developer's shell does not change what they check.
