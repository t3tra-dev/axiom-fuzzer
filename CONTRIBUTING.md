# Contributing

axiom-fuzzer is a research prototype at version 0.x. Issues and pull requests are welcome; this
page says what a report or a change needs.

## Reporting a false `UNSAT` first

A false `UNSAT` (a refutation reported for a satisfiable theory) is the most serious bug this
project can have. If you find one, or a certificate that `axiom-replay` accepts but should not,
open an issue with:

1. the input: the TPTP file exactly as solved, or the `--theory` name and, for a library user,
   the code that builds the theory;
2. the certificate (`--certificate FILE`);
3. the output of `axiom-replay --problem FILE CERT` (or `--theory NAME CERT`), and, if you can, of
   `scripts/recheck.sh` with the same arguments;
4. the version (`axiom-fuzz --version`), the operating system, the OCaml version, and whether the
   binary was a dev or a release build;
5. the full command line and any `AXIOM_*` variables that were set.

If the certificate passes `axiom-replay` but the problem is satisfiable, include a model if you
know one. [docs/guarantees.md](docs/guarantees.md) says which components a false `UNSAT` would
implicate.

Other bugs: give the command line, the input, the output, the version and the platform.

## Build, test and format

```sh
dune build
dune runtest                   # the deterministic test tier
dune build @runtest-timing     # deadlines, signals and process reclamation
dune build @runtest-eval       # the evaluation-only strategies
dune build @fmt                # ocamlformat 0.29.0
dune build @rocq               # Rocq 9.3.0 with its Stdlib (or ROCQ=/path/to/rocq)
```

`make check` (`dune build @ci`) runs all of them after the build.
[docs/development.md](docs/development.md) explains each check. A pull request should pass all
of them. Pull requests run CI on Linux and macOS.

`dune build @fmt` needs ocamlformat 0.29.0: `opam install . --deps-only --with-dev-setup` installs
it with the other development tools (ocaml-lsp-server, Rocq 9.3.0 and its Stdlib), and
`opam install ocamlformat.0.29.0` installs it alone. Dune memoizes tests: a test that passed runs
again only when one of its inputs changes, so `dune build @ci --force` runs every check again.

## Rules for the trusted parts

- Never edit the 14 files extracted from Rocq (`lib/proof/*_checker.ml(i)`,
  `lib/proof/wire_normalizer.ml(i)`, `lib/syntax/source_checker.ml(i)`) by hand. Change `rocq/`
  and re-extract; the result must be byte-identical with what you commit.
- Keep the `Print Assumptions` allow-list in `scripts/rocq_assumptions.py`. A change that adds an
  assumption to a theorem must say so, update [docs/guarantees.md](docs/guarantees.md), and is
  reviewed as a change to the trust base.
- Changes to `lib/proof/kernel.ml`, `lib/proof/verified.ml`, the Wire types, certificate reading
  (`lib/io/certificate_io.ml`, `lib/io/sexp.ml`) or `rocq/` are changes to the trust base. Keep
  them separate from other work and explain why they are sound.
- New inference rules follow the checklist in
  [docs/development.md](docs/development.md#adding-an-inference-rule).

## Changes to the search

- No public option selects a strategy. Per-worker strategies follow from `--workers` alone, and a
  change to that rule needs measurements for every worker count it affects.
- No problem names, problem-specific settings or priors about the shape of contradictions.
- A change that is meant to keep the search (refactoring, speed-ups, output) must keep it
  identical: run the identity check of
  [docs/development.md](docs/development.md#checking-that-a-change-keeps-the-search) on the
  release build and report its result.
- A change that alters the default search needs a measurement that follows
  [docs/benchmarks.md](docs/benchmarks.md): interleaved arms, re-checked solves, the results
  header, and gains and losses by name. Never use the TEST split of the held-out corpus for
  development ([docs/preregistration.md](docs/preregistration.md)).
- A memory limit must be deterministic: count it in the engine's own units, not with the garbage
  collector's readings.
- The solver never bundles or starts an external prover. Re-implementing published ideas is
  fine; credit them in [THIRD-PARTY.md](THIRD-PARTY.md).

## Documentation

The pages in `docs/` describe the current version in the present tense. Put history in
[CHANGELOG.md](CHANGELOG.md), and measurements in a results page with the header of
[docs/benchmarks.md](docs/benchmarks.md#results-header). Mark anything that you could not run.

## Commits and sign-off

Write commit messages as `Area: summary` (for example `Docs: ...`, `Search: ...`). Sign off your
commits (`git commit -s`) to certify the [Developer Certificate of
Origin](https://developercertificate.org/). By contributing you agree that your contribution is
licensed under the license of the files it changes (see [REUSE.toml](REUSE.toml)).
