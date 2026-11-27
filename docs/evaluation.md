# Evaluation-only strategies and switches

axiom-fuzz has one search policy: the worker strategies follow from `--workers`, and no public
option changes the search. The switches below exist for measurement: A/A comparisons with
frozen builds, ablations of a single mechanism, and traces that compare a ported heuristic with
the prover it comes from. They are evaluation-only.

- They are not a stable interface. Names, values and effects may change in any 0.x release.
- Unset, they leave the default search exactly as it is. An invalid value is an error (exit 2).
- One registry (`Eval.switches` in `lib/scheduler/eval.ml`) parses all of them. When any of them
  is active, `axiom-fuzz` prints one line on standard error before it starts, naming them:
  `Note: evaluation overrides active: AXIOM_MEASURE_COST_CLOCK=stopped, --eval-strategies=e208`.
  The CSV files do not record the overrides; keep the command line and the environment with the
  results.
- A run with an override is not a run of axiom-fuzzer's default search. Report it as such.

## Strategies

The strategy names below select a worker's strategy through `--eval-strategies`. All of them
change the **search** (which clauses are selected, and so the result).

| Name | Kind | Values (default first) | Effect | What it does |
| --- | --- | --- | --- | --- |
| `--eval-strategies SPEC` | hidden CLI option | `balanced`, `standard`, `NAME`, `NAME,NAME,...` | search | Per-worker strategies. `balanced` is the default rule. `NAME` runs that strategy on every worker; `production` is the all-production A/A baseline, and with one worker it runs production alone, without the single-worker time share. `standard` puts `calc:e` on worker 1 only. A comma-separated list names one strategy per worker. The last occurrence wins. A list that repeats a deterministic E heuristic at the same queue phase is refused |
| `production`, `calc:e`, `e208`, `y1346`, `sat001` | strategy names | | search | The five strategies that the default rule uses ([architecture.md](architecture.md#strategies)) |
| `e208e`, `e208k`, `y1346k`, `sat001k`, `e208av`, `y1346av`, `e208sl` | strategy names | | search | Variants of the default E ports: E's given-clause loop details (`e208e`), E's own KBO instance (`*k`), AVATAR splitting (`*av`), SInE layers in clause selection (`e208sl`) |
| `h042`, `h047b31`, `calc:lpo` | strategy names | | search | LPO members: two LPO4 heuristics of E, and production with LPO instead of KBO |
| `c18`, `c18s2s`, `x1276`, `h047`, `x1276rg`, `c18sos`, `c18c`, `b07c`, `s4d`, `c01`, `c41` | strategy names | | search | Further ported E 3.5.9 heuristics |
| `c18csl`, `sat001sl`, `c18sl` | strategy names | | search | E heuristics that first select axioms with SInE. They drop axioms, so they are not refutationally complete |
| `calc:v10` | strategy name | | search | Production with Vampire's literal selection 10 |
| `v:sos21`, `v:g34av`, `v:lpo10av`, `v:lpo1av`, `v:flr4`, `v:flr4u`, `v:la1011av`, `v:la11urr`, `v:dis10` | strategy names | | search | Ported Vampire 5.1.0 schedule slices. `v:sos21` (set of support) and `v:flr4`, `v:flr4u` (Vampire's forward literal rewriting condition) are not complete |
| `proto:e`, `proto:ela`, `proto:maxw`, `proto:combo` | strategy names | | search | Early prototypes of E-style literal selection and precedence, kept for comparison |

The `--eval-strategies` names are also accepted by `AXIOM_SLICES` `members=` and by the library
(`Strategy.of_name`). A suffix on a heuristic's name marks a variant of it: `k` uses E's own KBO
instance, `av` AVATAR splitting, `sl` SInE (layers in clause selection for `e208sl`, axiom
selection for the others), `e` E's given-clause loop, and `rg` the
literal selection of E's `..._RG_S04AN` configuration (`x1276rg`).

The CSV columns `r13_*` and `r14_*` are fixed column names from earlier experiments; they are
not modes that you can select.

## Environment variables

[evaluation-switches.md](evaluation-switches.md) lists every `AXIOM_*` variable that
`axiom-fuzz` reads, with its kind, values, unset default and effect. That table is what
`axiom-fuzz --eval-help` prints, and a test keeps the page equal to it. The kinds are:

- **search**: changes the search, for example `AXIOM_SLICES` (the single worker's time slices),
  `AXIOM_PHASE_BASE`, `AXIOM_EQ_UNFOLD`, `AXIOM_LEAN_*`, `AXIOM_EQUIVALENCE` and `AXIOM_LANE`
  (the schema probe lane's options);
- **certificate**: changes how a found proof is written, not the search
  (`AXIOM_GROUND_EXPLANATION`, `AXIOM_AVATAR_REFUTATION`);
- **measurement**: changes how a run is clocked, isolated or traced
  (`AXIOM_MEASURE_COST_CLOCK`, `AXIOM_MEASURE_REFERENCE`, `AXIOM_MEASURE_PORTFOLIO` and the
  trace prefixes `AXIOM_MEASURE_*_TRACE`);
- **diagnostic**: prints internal counters on standard error (`AXIOM_*_REPORT`,
  `AXIOM_VAMPIRE_ORDERING`).

The same page lists the variables that only the tests, the editor script and the benchmark
scripts read. The schema benchmark (`bench/schema/schema_bench.exe`) reads
`AXIOM_MEASURE_COST_CLOCK` only; its `witness CASE --tptp-out FILE` subcommand exports a case's
first-order witness problem.
