# Benchmarks and measurement method

This page describes the benchmark suites in the repository and the method for measuring the
solver. The pre-registered TEST results of 0.1.0 are in the [README](../README.md#results-on-the-held-out-test-split)
and `benchmarks/results/`, measured with `benchmarks/heldout.py`. The numbers measured during
development are not published here: they are historical, and they used internal corpora and drivers that are not in
this repository.

## Suites in the repository

| Entry point | What it runs | Use |
| --- | --- | --- |
| `make bench` (`make release`, then `python3 benchmarks/run.py`) | The six built-in theories, 2 s each, 100 given and 10,000 generated clauses at most | Smoke check: fails if a result differs from the expected `UNSAT`/`UNKNOWN` |
| `python3 -B benchmarks/run.py --suite applications` | Eight TPTP problems from program and circuit verification, specification matching, knowledge representation, planning and Isabelle ([benchmarks/problems/](../benchmarks/problems/README.md)) | Fixed-input comparison; `--suite all` adds the built-in theories, `--profile` records the pipeline stages |
| `bash benchmarks/external.sh` | The same inputs on E, Vampire and Zipperposition, downloaded and pinned at run time | Comparison with external provers |
| `bench/schema/schema_bench.exe` and `bench/schema/scripts/` | 41 schema contradictions (34 inconsistent theories and 7 consistent controls) and 293 mutants of ZF's fixed axioms | The schema search and the probe lane |
| `benchmarks/replay_bench.exe` | Fixed valid certificates | The cost of the check alone |
| `benchmarks/guidance_bench.exe`, `progress_bench.exe`, `synthesis.py`, `improvements.py` | Internal mechanisms | Diagnostics |

Build the binaries that you measure with `make release` (OCaml 5.5.2 + flambda, release
profile, `-O3`; see [installation.md](installation.md#the-flambda-release-build)), and build the
`axiom-replay` that re-checks the results separately, preferably with another compiler.

`benchmarks/external.sh` finds the provers' GitHub Releases with `gh` (authenticated with
`gh auth login`, and with network access), downloads the asset for
the host, or builds the release sources in a temporary directory; E has no GitHub Releases, so
it builds a pinned version tag. It never changes an existing opam switch or stores the provers
in the repository. Pin the versions with `--tag PROVER=TAG` (for example `eprover=E-3.5.9`), and
read the licences of the provers you download. The harness runs each prover on one core.

## Corpora

| Corpus | Content | Published |
| --- | --- | --- |
| Applications | 8 TPTP problems (7 from TPTP v9.0.0, SWV851-1 from v6.4.0) and their 5 axiom files, verbatim | In the repository, with hashes in `benchmarks/problems/manifest.json` |
| Schema benchmark | 41 cases written in OCaml against the library API, and 293 ZF mutants | In the repository (`bench/schema/`) |
| Held-out TPTP v10.0.0 corpus | 320 problems: a development split DEV (149 UNSAT, 12 SAT) and a TEST split (147 UNSAT, 12 SAT) | Manifest and split rule: [preregistration.md](preregistration.md); the problem texts come from TPTP |
| Frozen corpus | 91 UNSAT problems and 23 satisfiable controls, from TPTP v9.0.0 and v10.0.0, project-generated synthetic problems and built-in theories, in three presentations | Not published in this release |

Prepare TPTP inputs by expanding `include` lines into the problem, with no other change
(`benchmarks/corpus.py`): no formula is added, removed or reordered, and no conjecture is negated
automatically. Every solver gets the same prepared bytes. Record the hash of each original file
and of each prepared file. Prepared files are modified TPTP files; do not redistribute them
without the permission of the TPTP maintainers.

DEV and the frozen corpus informed the design and the adoption decisions, so results on them
are optimistic. See [preregistration.md](preregistration.md) for the history of the TEST split.

## Procedure

1. **Fix everything before the run**: the source commit and a clean tree, the build, the
   corpus manifest, the order of the cases, the budgets, the seeds, the arms and the decision
   rule. Write them into the results header below.
2. **Interleave the arms.** Run every arm of a comparison in one driver run, in a seeded random
   order of (arm, case, seed) trials, so that all arms share the same load. Never compare solve
   counts from separate runs at different loads.
3. **Bound the whole process.** `--seconds` is a cooperative per-process budget; input
   parsing, the final check and the output come on top. A driver must watch the wall time of the
   whole process group and kill it at a hard deadline.
4. **Count only re-checked, in-time solves.** A solve is an `UNSAT` whose certificate a separate
   `axiom-replay` accepted against the original input, reported within the wall budget. A late
   solve (after the budget, inside a grace period) is listed but not counted. An `UNSAT` without
   a passed replay is an alarm (`UNVERIFIED_UNSAT`), as are an `UNSAT` on a satisfiable control
   (`FALSE_UNSAT`) and a rejected certificate (`INVALID_PROOF`).
5. **Account for resources.** axiom-fuzz runs `--workers` heuristic processes plus one
   reference enumeration process. Against a prover that uses N cores, state that axiom-fuzz used
   one process more.
6. **Keep every row**, including errors and crashes, in the raw results (one JSON line per
   trial: case, arm, seed, presentation, status, wall and CPU time, the load at the start, the
   certificate size and the replay status).
7. **Re-run boundary cases**, those solved close to the budget or by only some trials, with
   further seeds, and say so.

For an identity check (the same search, faster), use the stopped cost clock and caps instead of
a time limit, as described in [development.md](development.md#checking-that-a-change-keeps-the-search).

## Statistical convention

- Compare two arms on the cases that both covered. Decide each case by the majority of its
  trials (or by "any" or "all", stated in advance).
- Report the cases gained and lost by name, and an **exact two-sided sign test** on the
  discordant cases.
- The test is descriptive. It is not adjusted for multiple comparisons, and the cases are not a
  random sample of any population of problems.
- State the caveat that DEV and frozen-corpus results are optimistic, because both sets informed
  decisions.

## Decision rules used in development

These rules were applied with internal tools during development; this is their definition.

- **Margin rule.** For two arms over the n common UNSAT cases, let d_i be +1 if only the
  candidate solves case i, −1 if only the baseline does, and 0 otherwise; net = Σ d_i. The paired
  standard error is √(n × sample variance of the d_i). The verdict is GAIN if
  net > max(3, 2 × SE), LOSS if −net > max(3, 2 × SE), and WITHIN-NOISE otherwise. The
  threshold and the comparator are fixed before the data are seen.
- **A/A noise.** The same binary (or two builds with identical machine code) is run twice; the
  cases that flip between the two runs measure the noise. On DEV at 10 s with one worker this was
  about 3 of 149 cases.
- **Cover rule for strategy members.** A member of the balanced rule is replaced only if, at
  some worker count, the candidate composition beats the current one on DEV by more than the A/A
  noise in both halves of two stratified random splits and in a per-domain hold-out validation.
  No candidate met it, so the default members have not changed since they were introduced.
- **Alarms.** Any FALSE_UNSAT, INVALID_PROOF or UNVERIFIED_UNSAT, a certificate at the 32 MiB
  reader limit, or any TEST-split case among the inputs fails a comparison outright.

## Results header

Every published results table states, once per table:

```text
Date:            YYYY-MM-DD
Commit:          <commit>, clean tree; whether it equals the release tag
Build:           compiler, flambda yes/no, dune profile, flags, sha256 of each binary
Re-check:        axiom-replay commit, compiler, sha256
Machine:         CPU model, cores, RAM, OS version; shared or dedicated; median load1 at trial start
Corpus:          manifest name and sha256; split; presentations; SAT controls
Budget:          wall seconds per process; --workers (+1 reference process); --memory-budget; caps
Seeds:           seeds and repetitions; how boundary cases were re-run
Counting rule:   UNSAT re-checked by a separate replay within the wall budget; late solves excluded
Test:            exact two-sided sign test on discordant cases (descriptive, not adjusted)
Decision rule:   if any, stated before the run
Caveats:         DEV and frozen results are optimistic; anything else that departs from this page
```

For an external prover, add its version and commit, how it was obtained, the exact command line,
its cores, the memory guard, the date, and whether it ran interleaved with axiom-fuzzer. On macOS
note that Vampire's CASC schedule translates instruction limits to time limits and that its
`--memory_limit` has no effect.

## How the schema-benchmark cases were written

axiom-fuzzer was developed with AI assistance, and so were these cases. The schema benchmark
(`bench/schema/`) has three groups of cases, written by three separate AI agent sessions:

- **17 original cases** (`cases` in `schema_bench.ml`), written by the session that wrote the
  first prototype of the probe lane, together with that prototype.
- **2 skeptic cases** (`russell-4cycle`, `cantor-injection`), written by a separate reviewing
  session as held-out cases for the prototype. The first lane was then designed with knowledge of
  them (its diagonal prior covered 4-cycles and equality diagonals for them), so they are not
  independent of the lane. The default lane of 0.1.0 no longer has that prior.
- **22 independent cases** (`bench/schema/independent.ml`, names starting with `i-`): 15
  inconsistent theories and 7 consistent controls, written by a third session. It was given only
  `schema_bench.ml`, the public interfaces (`Theory`, `Source`, `Wire`, `Signature`, `Kernel`),
  the documents of the time on the theory API and on synthesis, the README of the time, and the
  literature. It did not
  read the lane implementation, which lived on another branch: the commit that added the cases
  (2026-11-14) contains the prototype but not the lane. It knew one run of the prototype on each
  case. Two of its cases, `i-russell-4cycle` and `i-cantor-injection`, rewrite the skeptic cases
  and share their dependence on the lane's design; results excluding them were reported
  separately.

A fourth session, which wrote neither the prototype nor the lane, measured the merged lane on
these cases. It fixed the subset of 13 diagonal-shaped cases before it saw the final results.
Each inconsistent case records a witness (the instances of a hand proof), and
`schema_bench independent-check` verifies, without search, that every witness instance is
accepted by its schema's checker. The consistent controls must never be refuted; an `UNSAT` on
one is a soundness alarm.

## Held-out TEST split

[preregistration.md](preregistration.md) publishes the manifest and the split rule of the
held-out TPTP v10.0.0 corpus and the rules for the next evaluation on its TEST split.
