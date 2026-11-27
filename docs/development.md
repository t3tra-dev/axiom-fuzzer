# Development

How to build, test and change axiom-fuzzer. [CONTRIBUTING.md](../CONTRIBUTING.md) has the rules
for contributions; [installation.md](installation.md) has the toolchain.

## Build

| Command | Builds or runs |
| --- | --- |
| `dune build` | Everything in the dev profile: warnings are errors, `-opaque` keeps rebuilds small |
| `make release` | The binaries, `schema_bench` and the benchmark executables in the release profile with `-O3` (use an OCaml 5.5.2 + flambda switch for measured builds) |
| `make build` | `dune build` |
| `make test` | The deterministic and the timing test tiers (`dune runtest`, then `dune build @runtest-timing`) |
| `make test-timing`, `make test-eval` | One tier: `dune build @runtest-timing`, `dune build @runtest-eval` |
| `make rocq` | `dune build @rocq` |
| `make check` | `dune build @ci`: formatting, the three test tiers and `@rocq` |

The dev and release profiles share `_build/default`; switching between them rebuilds. Use one
Dune version per checkout.

## Tests

The suite has three tiers, each a Dune alias:

| Alias | Runs |
| --- | --- |
| `@runtest` (`dune runtest`) | The deterministic tier: searches bounded by caps, by the stopped cost clock or by generous wall limits. OCaml unit, property and differential tests with no external test library, regression tests, scheduling tests, the process-portfolio tests, CLI tests in Python (standard library only), the schema benchmark's smoke subset, and the tests of the external-prover harness (which need no network) |
| `@runtest-timing` | Tests of wall-clock deadlines, signals and process reclamation (the clock, deadline and slice-deadline tests, `process_test.py`, `process_stress.py`, `process_chaos.py`) and `benchmark_test.py`, the test of the benchmark driver; they run one at a time (`(locks /timing)`) |
| `@runtest-eval` | Every complete evaluation-only strategy must find a kernel-checked refutation |

Tests that use randomness use fixed seeds. The Python tests remove every `AXIOM_*` variable and
the OCaml runtime parameters from the environment of the processes they start
(`tests/regression/clean_environment.py`), and the capped CLI runs set
`AXIOM_MEASURE_REFERENCE=off`, so that a run ends with its heuristic workers.

| Kind | Examples |
| --- | --- |
| unit and property | arena, binding, unification, α-variants, rewriting, literal selection, subsumption and its indexes, KBO and LPO against reference implementations, CNF and Skolemization on finite models, the ported E and Vampire components against traces of E 3.5.9 |
| differential | indexes against brute force, ordered inference, ground equality problems against finite models |
| regression | the built-in theories, mutation, proofs through every inference rule, minimization, AVATAR certificates, the memory budget (deterministic readings across GC settings, process and Domain portfolios, worker counts), completeness regressions (multiset subsumption, equivalence rewriting), the probe lane |
| processes | report frames, supervisor re-checks, deadlines, kills, lifelines, temporary files; `process_stress.py` sends random signals at random times to the CLI and checks that nothing is left behind |
| CLI | certificates, replay and its exit codes, FOF/CNF round trips, Rocq, TSTP and CSV output, signals |

`make stress-processes` runs the randomized reclamation tests with 1,000 trials each (the
timing tier runs a few dozen).

`dune build @rocq` checks the Rocq side ([below](#rocq)). It needs Rocq 9.3.0 with its Stdlib,
built with OCaml 5.5.x for the byte comparison of the extracted files. It finds such a `rocq`
itself (`scripts/find_rocq.sh`); set `ROCQ` to choose another.

`make check` runs `dune build @ci`: `@fmt`, `@runtest`, `@runtest-timing`, `@runtest-eval` and
`@rocq`. It is a separate alias so that Dune's own `@check`, which editors build, stays a type
check.

Dune memoizes test actions: a test that passed is not run again until one of its dependencies
changes. In a checkout where the tiers have already passed, `make check` and `make test` run only
the tests whose inputs changed. To run everything again, use `dune build @ci --force` (or `--force`
with one tier, such as `dune build @runtest --force`).

## Formatting

Hand-written OCaml and Dune files are formatted with ocamlformat 0.29.0 (`conventional` profile,
100 columns), the version `.ocamlformat` names. Install it into the opam switch of the checkout
with the development dependencies (ocamlformat 0.29.0, ocaml-lsp-server, Rocq 9.3.0 and
rocq-stdlib 9.2.0), or alone:

```sh
opam install . --deps-only --with-dev-setup   # every development tool
opam install ocamlformat.0.29.0               # ocamlformat alone
```

Then:

```sh
dune fmt          # format
dune build @fmt   # check without changing files
```

The 14 extracted files are listed in `.ocamlformat-ignore` and must never be formatted; their
bytes are compared with Rocq's output.

## Rocq

`rocq/` holds the whole Rocq development (25 files under the logical path `AxiomFuzzer`). Seven
modules of it are extracted into 14 OCaml files that the kernel check calls:
`lib/proof/{rocq,avatar,wire,kernel,natural}_checker.ml(i)`, `lib/proof/wire_normalizer.ml(i)` and
`lib/syntax/source_checker.ml(i)`.

`dune build @rocq` (`scripts/check_rocq.sh`):

1. compiles `rocq/` in a temporary directory and compares the 14 re-extracted files with `lib/`
   byte by byte;
2. generates 26 proofs with `axiom-fuzz --rocq` and the regression tests (built-in theories,
   example problems, registered schemas, natural deduction, enumerated theories, AVATAR,
   congruence closure, goals, contraction) and compiles them;
3. checks every `Print Assumptions` result of the library and of the generated proofs against
   the allow-list in `scripts/rocq_assumptions.py`, and rejects `Admitted`, global `Axiom` and
   `Parameter`, `Declare Instance`, `Redirect` and other ways to hide assumptions;
4. checks that the audit still rejects every known hole in `tests/fixtures/rocq_audit/`;
5. checks that the example problems still exercise the rules they are named after.

Rules for changes to the Rocq side:

- Never edit the 14 extracted files by hand. Change `rocq/`, re-extract and copy the generated
  files. A Rocq build of `rocq/` leaves them at the top of its build directory: for example,
  `RECHECK_ROCQ_LIB=DIR scripts/recheck.sh --theory naive CERT` builds into `DIR`, and
  `scripts/check_rocq.sh` builds the same way in a temporary directory.
- Re-extraction must be byte-identical with the committed files; `@rocq` fails otherwise.
- Do not weaken the allow-list. A theorem whose assumptions change needs a matching change to the
  allow-list and to [guarantees.md](guarantees.md), and the review of both.
- Assumptions passed as theorem arguments (excluded middle, functional choice, the comparison
  interface) are not visible to the audit; state them in the theorem and in the documentation.
- `Wire_types` and the constructor mappings in `rocq/Extraction.v` must change together.

## Checking that a change keeps the search

The default search must not change unless a change is meant to change it. Because the default
scheduling costs read the wall clock, compare searches with the cost clock stopped
(`AXIOM_MEASURE_COST_CLOCK=stopped`) and with caps (`--max-given`, `--max-generated`) that every
run reaches long before its time limit; a capped search then depends only on its input and its
binary. Compare binaries built the same way (dev with dev, release with release): the
single-worker time share and the probe lane count allocated words, so code motion can change the
search of a release build even when the logic is unchanged.

`tools/same_search.py` runs two `axiom-fuzz` binaries on the same capped searches and compares
the result, the proof source, the used axioms, each worker's stop reason, given count and
memory-budget digest, the counters of the selected search, the deterministic worker CSV columns
and the certificate bytes, at three levels:

| Level | Runs | SAME means |
| --- | --- | --- |
| A | each of `production`, `calc:e`, `e208`, `y1346` and `sat001` alone (`--eval-strategies NAME`) on the bundled TPTP problems and `theories/examples` | every engine searches as before; expected for any change that keeps the search, and also between build configurations |
| B | the default four-worker portfolio on the same problems | every worker that stopped at a cap, a budget or a proof in both runs did the same |
| C | the default single worker on the same problems, and the six built-in theories | the allocation-clocked time share and the probe lane are unchanged too |

```sh
python3 -I tools/same_search.py BASE/_build/default/bin/fuzz/main.exe \
  CANDIDATE/_build/default/bin/fuzz/main.exe
```

Each line starts with `SAME`, `DIFF` or `UNSTABLE` (a run that hit the wall limit instead of its
cap); the exit status is 0 when every run is `SAME`. [tools/README.md](../tools/README.md) has
the options. A change that is meant to keep the search must report `SAME` at all three levels
on the release build. A change that moves level C changes the default search, and needs the
evidence that [CONTRIBUTING.md](../CONTRIBUTING.md#changes-to-the-search) asks for.

## Adding an inference rule

The checker accepts a rule only once every layer knows it. Change, in one series:

1. the `Wire` rule, its parents, substitution and positions, and the certificate codec;
2. the search side that produces it, and `Verified`, which expands it into primitive steps;
3. the kernel's reconstruction of the rule;
4. the Rocq checker and its soundness proof, then re-extract;
5. the TSTP output and the documentation of the format;
6. tests: a proof that uses the rule, tampered certificates that must be rejected, and a
   generated Rocq proof compiled by `@rocq`.

## Adding a schema

A registered schema (`Theory.Schema.create`, [theories.md](theories.md#registering-a-schema))
needs no change to the kernel or the scheduler: its `check` callback becomes part of the theory
and is trusted. A new built-in schema, checked by Rocq like the four existing ones, needs a new
`Wire.schema` case, its generation and provenance check in `Theory`, its expansion, meaning and
correctness theorem in `rocq/Source/Language.v`, the certificate encoder, and tests. In both
cases the checking side never calls the search's generator.

## Documentation

The pages in `docs/` describe the current version in the present tense, by topic. History goes
into [CHANGELOG.md](../CHANGELOG.md); measurement logs and design notes go into a dated entry
of a results page that follows the [results header](benchmarks.md#results-header), not into the
reference pages.
