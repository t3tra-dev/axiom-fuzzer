# axiom-fuzzer

axiom-fuzzer looks for contradictions in first-order theories. A theory can be a finite set of
axioms, a set of axiom schemas whose instances the tool synthesizes, or any recursively
enumerated set of axioms. When the search finds a refutation, a checker extracted from a Rocq
development re-checks it from the original axioms, and only then does the tool answer `UNSAT`.
Otherwise it answers `UNKNOWN`. It never answers `SAT`.

For example, on naive set theory (unrestricted comprehension) it finds the instance
`not (x in x)` by enumerating and combining candidate conditions, and refutes it. Neither that
condition nor the Russell proof is built into the search.

[日本語の README](README.ja.md)

**Status.** A research prototype, version 0.1.0. It is not a competitive automated theorem
prover: E and Vampire solve more of the TPTP problems we tried. Its point is that every
refutation it reports comes with a certificate that you can re-check, down to a Rocq proof.
During 0.x the command-line interface, the certificate and checkpoint formats and the CSV
columns may change without migration.

This project was developed with AI assistance.

## What `UNSAT` means

- `UNSAT` means that the tool found a refutation certificate and that `Kernel.check` accepted
  it. The final decision of `Kernel.check` is made by checkers extracted from the Rocq
  development in [rocq/](rocq/). The Rocq theorems `check_sound`, `avatar_check_sound` and
  `Reference.Certificate.Kernel.check_sound` show that the theory, as the tool read it, has no
  model over a non-empty domain.
- `UNKNOWN` claims nothing. It is not evidence of satisfiability, of consistency, or even of
  difficulty.
- You can re-check a certificate yourself: `axiom-replay` runs the checkers again in a separate
  process, and `axiom-replay --rocq` exports the refutation as a Rocq file that Rocq checks on
  its own. [scripts/recheck.sh](scripts/recheck.sh) does both.
- Still trusted: the Rocq kernel and its Stdlib; the Rocq definitions of the syntax, semantics
  and built-in schemas; the classical assumptions of the metatheory; the input side (the TPTP
  reader, the built-in theory manifests, the `check` callbacks of schemas you register); and,
  unless you use the Rocq route, the extraction and the OCaml compiler and runtime.
- Not covered by any proof: the completeness of the heuristic search, anything about `UNKNOWN`,
  and performance.

[docs/guarantees.md](docs/guarantees.md) gives the full trust model.

## Install

| Component | Version | Needed for |
| --- | --- | --- |
| OCaml | 5.2 to 5.5 (tested with 5.2.1, 5.4.1 and 5.5.2) | everything |
| Dune | 3.17 or later (tested with 3.17.2, 3.24.2 and 3.25.0) | everything |
| C compiler | any (Xcode Command Line Tools, gcc or clang) | the small C stubs |
| Python | 3.12 or later | tests and benchmark scripts |
| Rocq | 9.3.0 with its Stdlib (`rocq-core` 9.3.0 and `rocq-stdlib` 9.2.0) | proofs: `dune build @rocq`, the Rocq re-check |
| OCaml 5.5.2 + flambda | optional | the release build used for measurements (`make release`) |

The library depends on the OCaml standard library and `unix` only. macOS on arm64 is where the
tool was developed. Linux is supported: the test suite passed in an ubuntu-24.04 container, and
the CI workflow builds and tests on Linux and macOS. Windows is not supported: the process
portfolio uses `fork`, process groups and POSIX signals.

An opam setup from a fresh clone:

```sh
git clone https://github.com/t3tra-dev/axiom-fuzzer.git
cd axiom-fuzzer
opam switch create . 5.5.2 --no-install   # any OCaml from 5.2 to 5.5 works
eval $(opam env)
opam install . --deps-only --with-test
dune build
dune runtest
```

[docs/installation.md](docs/installation.md) covers Rocq, the flambda build, the editor setup
and troubleshooting.

## Quick start

Refute naive set theory, save the certificate and re-check it in a separate process:

```sh
dune exec axiom-fuzz -- --theory naive --certificate russell.cert
dune exec axiom-replay -- --theory naive russell.cert
```

The output lists the schema instances that the search tries (`[N] ...`), a short summary and
the clauses of the proof (`#N ...`):

```text
[0] comprehension_0: x in x
[1] guided comprehension_1: not (x in x)
Theory: naive
Result: UNSAT
Reason: refutation verified
Used axioms: comprehension_1
Proof clauses: 5
#2  (v0 in v0) | (v0 in sk_1_0)
#3  (sk_1_0 in sk_1_0)
#5  ~(v0 in v0) | ~(v0 in sk_1_0)
#6  ~(sk_1_0 in sk_1_0)
#7  BOTTOM
Certificate: russell.cert
```

`--quiet` keeps only the summary lines; `--stats` adds the counters of the workers, the probe
lane and the reference enumeration.

The replay prints `VERIFIED: theory=naive axioms=1 steps=5 ...` and exits 0. Passing another
theory, for example `--theory zf`, makes it print `REJECTED: theory manifest mismatch` and exit
1.

A TPTP problem works the same way. The problem file is part of the check, so pass it to the
replay as well:

```sh
dune exec axiom-fuzz -- --problem theories/examples/equality.p --certificate equality.cert
dune exec axiom-replay -- --problem theories/examples/equality.p equality.cert
```

With Rocq 9.3.0 and its Stdlib installed, re-check the certificate down to a Rocq proof (the
first run also compiles the Rocq development in `rocq/`; the script finds a suitable `rocq` on
the `PATH`, in the opam switches or in Homebrew, and `ROCQ=/path/to/rocq` chooses another):

```sh
scripts/recheck.sh --theory naive russell.cert
```

Theories that are believed to be consistent, such as `zf`, end in `UNKNOWN` at the time limit:

```sh
dune exec axiom-fuzz -- --theory zf --seconds 2
```

## Command-line tools

| Binary | Purpose |
| --- | --- |
| `axiom-fuzz` | Search a built-in theory (`--theory`) or a TPTP problem (`--problem`); write the certificate, TSTP, Rocq, FOF/CNF exports and CSV metrics |
| `axiom-replay` | Re-check a certificate against a theory or problem that you name; export it as Rocq source |
| `axiom-minimize` | Shrink a certificate (fewer axioms, smaller schema conditions, shorter natural deduction) and re-check the result |
| `axiom-mutate` | Generate mutants of a theory's axioms and search each one |
| `axiom-reference` | Run the Rocq-proved reference enumeration of natural-deduction certificates stage by stage |

`axiom-fuzz` has no option that picks a search strategy: the strategies follow from
`--workers` alone. Every binary exits 2 for a usage, input or internal error, with a message
on standard error; a run that ends in `UNKNOWN` exits 0, and `axiom-replay` exits 1 when it
rejects a certificate. Every binary accepts `--version`. Environment variables named
`AXIOM_*` are evaluation-only overrides; when one is set, `axiom-fuzz` prints
`Note: evaluation overrides active: ...` on standard error. See [docs/cli.md](docs/cli.md) and
[docs/evaluation.md](docs/evaluation.md).

## Theories and schemas

| `--theory` | Content | Result with the defaults |
| --- | --- | --- |
| `naive` | Unrestricted comprehension | `UNSAT` |
| `separation-universal` | Separation plus a universal set | `UNSAT` |
| `foundation-self` | Pairing, foundation and a set that contains itself | `UNSAT` |
| `mutated-separation` | Separation with its bounding set removed (a deliberate mutation) | `UNSAT` |
| `separation` | Separation alone | `UNKNOWN` |
| `zf` | Extensionality, empty set, pairing, union, power set, infinity, foundation, separation and replacement (no choice) | `UNKNOWN` |

`--problem` reads untyped first-order TPTP: `fof` and `cnf` formulas, without `include`, TFF,
THF or arithmetic, and with the conjecture already negated (`negated_conjecture`). The OCaml
library defines further theories: fixed axioms, registered schemas with your own parameter
types and checkers, definitions, and recursively enumerated axiom sets. Its entry points are
an unstable 0.x API. See [docs/theories.md](docs/theories.md).

## Results on the held-out TEST split

The pre-registered evaluation of [docs/preregistration.md](docs/preregistration.md), run once on
0.1.0. TEST had not been run since 2026-11-15 and was not used for any decision in 0.1.0 after
that date (see the history in the pre-registration for the decisions it confirmed before).

| TEST stratum (UNSAT cases) | 1 worker, 10 s | 4 workers, 30 s |
| --- | --- | --- |
| nonSET R0 (55) | 50 | 54 |
| nonSET R1 (35) | 23 | 27 |
| nonSET R2 (20) | 5 | 7 |
| nonSET R3 (10) | 0 | 0 |
| SET R0 (12) | 11 | 12 |
| SET R1 (7) | 7 | 7 |
| SET R2 (5) | 2 | 2 |
| SET R3 (3) | 0 | 0 |
| **Total (147)** | **98** | **109** |

- **Alarms: none.** All 12 satisfiable controls ended in `UNKNOWN` in every trial, and every one
  of the 621 `UNSAT` answers was accepted by a separately built `axiom-replay`. No trial was
  killed at the hard deadline and no solve was late.
- A case counts as solved when the majority of its three seeds gave an in-time, replayed `UNSAT`.
  The search is deterministic, so the seeds (503, 607, 701) only vary the order of the
  interleaved trials; all three agreed on every case. The only solve above 80 % of its budget was
  CAT004-3 with 4 workers (26.5 s of 30 s).
- These numbers are not a comparison with other provers; E and Vampire solve more of these
  problems. They are the solve rate of the default command line, every solve re-checked.

```text
Date:          2026-11-27
Commit:        v0.1.0 (9fa2970), clean tree
Build:         OCaml 5.5.2 + flambda, dune release profile, -O3; axiom-fuzz sha256 4d66fb1d…a85c
Re-check:      axiom-replay from v0.1.0, OCaml 5.4.1 without flambda, dev profile; sha256 0d9e19a2…50ac
Machine:       Apple M4 Max, 14 cores, 36 GB, macOS 26.0; 12 process slots (a trial with N workers
               takes N + 1); load1 at trial start median 12.8, max 23.7 (the machine was also
               used for builds during the run)
Corpus:        benchmarks/corpora/heldout-tptp10.json (sha256 375743d4…9a3f), TEST split,
               147 UNSAT + 12 SAT; TPTP-v10.0.0.tgz sha256 f23c2cb8…499e
Budget:        --workers 1 --seconds 10 and --workers 4 --seconds 30 (+1 reference process);
               default memory budget; hard kill at budget + 10 s
Seeds:         503, 607, 701; no boundary case to re-run (no case split its seeds)
Counting rule: UNSAT replayed against the prepared file and reported within the wall budget
Raw rows:      benchmarks/results/heldout-test-0.1.0.jsonl (954 trials)
```

Reproduce with `python3 -B benchmarks/heldout.py --split test --tptp TPTP-v10.0.0 --binary
AXIOM_FUZZ --replay AXIOM_REPLAY --work DIR --output OUT.jsonl`, then
`python3 -B benchmarks/heldout.py --summarize OUT.jsonl`.

## Limitations

- The search is heuristic. Finite runs prove nothing about consistency, and the reference
  enumeration that is proved to find every refutation eventually has no practical time bound.
- The memory budget is a cooperative per-worker target in the engine's own units, not a hard
  limit on the resident set size, and the reference enumeration is outside it.
- Certificates larger than 32 MiB are written, but `axiom-replay` cannot read them.
- Natural-deduction certificates have no TSTP output; proofs from external provers cannot be
  imported.
- Certificates and checkpoints carry no version: a different version of the tool rejects them,
  so re-run the search to regenerate them.

## Documentation

| Document | Content |
| --- | --- |
| [docs/installation.md](docs/installation.md) | Requirements, platforms, Rocq and flambda builds, editor setup, troubleshooting |
| [docs/cli.md](docs/cli.md) | Every binary, its options, output and exit codes |
| [docs/guarantees.md](docs/guarantees.md) | Trust model: what is proved, what stays trusted, how to re-check |
| [docs/theories.md](docs/theories.md) | Built-in theories and schemas, the TPTP subset, the OCaml library API |
| [docs/formats.md](docs/formats.md) | Certificate, TSTP, Rocq output, checkpoint and CSV formats |
| [docs/architecture.md](docs/architecture.md) | How the search, the checkers and the process portfolio fit together |
| [docs/evaluation.md](docs/evaluation.md) | Evaluation-only strategies and `AXIOM_*` switches |
| [docs/benchmarks.md](docs/benchmarks.md) | Benchmark suites and the measurement method |
| [docs/preregistration.md](docs/preregistration.md) | The held-out TPTP v10.0.0 split and the rules for its next evaluation |
| [docs/development.md](docs/development.md) | Building, testing, Rocq re-extraction and the search identity check |
| [CONTRIBUTING.md](CONTRIBUTING.md) | How to report a false `UNSAT`, and the rules for changes |
| [CHANGELOG.md](CHANGELOG.md) | Release notes |

## Citing

Cite the software with the metadata in [CITATION.cff](CITATION.cff):

> t3tra. *axiom-fuzzer*, version 0.1.0. 2026.

## License

The project's own code and documentation are under the [MIT license](LICENSE). The 14 OCaml files that
Rocq extracts (`lib/proof/{kernel,natural,avatar,rocq}_checker.ml(i)`,
`lib/proof/{wire_normalizer,wire_checker}.ml(i)` and `lib/syntax/source_checker.ml(i)`) contain
translations of Rocq Stdlib code and are under LGPL-2.1-only. The TPTP problems and axiom files
in `benchmarks/problems/tptp/` and `tests/fixtures/tptp/`, redistributed verbatim, keep the TPTP
terms of use. The measurement data and corpus manifests (`benchmarks/checker.csv`,
`benchmarks/corpora/`, `benchmarks/results/`) are under CC-BY-4.0. [REUSE.toml](REUSE.toml), [LICENSES/](LICENSES/) and
[THIRD-PARTY.md](THIRD-PARTY.md) declare the license of every path.

## Acknowledgements

The ported heuristics re-implement strategies of the E prover 3.5.9 and schedule slices of
Vampire 5.1.0; neither prover is bundled with or started by axiom-fuzzer, and
[THIRD-PARTY.md](THIRD-PARTY.md) gives the attributions. The benchmark problems come from the
TPTP Problem Library. The proofs are checked by the Rocq Prover.

---

The commands on this page, the opam setup from a fresh clone and the results in the theory table
were run with 0.1.0 on macOS (arm64).
