# Changelog

All notable changes are listed here. The project follows [Semantic Versioning](https://semver.org/);
see [Stability](#stability) for what that means during 0.x.

## Stability

During 0.x there is no compatibility guarantee. The command-line interface and its output, the
certificate format, the checkpoint format, the CSV columns and the OCaml library API may change in
any release, without a migration path. Certificates and checkpoints carry no version number: a
release rejects the files of another release, so regenerate them with the release you use.

## Unreleased

### Checking

- The expansion of `Definitions` is formalized (`rocq/Source/Definitions.v`) and leaves the
  trusted base. `expand_correct` proves that in every structure satisfying the defining axioms a
  formula and its expansion have the same truth value, and `expansions_match_sound` turns a
  refutation of the expanded axioms into a refutation of the definitions together with the
  original axioms. `Definitions.expand` returns the result of the extracted `expand_formula`; the
  OCaml traversal only bounds and cross-checks it.
- `Theory.of_definitions` closes each formula over its free parameters before expanding it, keeps
  the closed originals (`Theory.definitions`) and checks with the extracted `expansions_match`
  that they expand to the manifest axioms. A Rocq export of such a theory also proves
  `defined_theory_unsatisfiable`.

- `dune build @rocq` and `scripts/recheck.sh` find a Rocq 9.3.0 with its Stdlib by themselves
  (`scripts/find_rocq.sh`): on the `PATH`, in the opam switches or in Homebrew, preferring for
  `@rocq` one built with OCaml 5.5. `ROCQ` still overrides the search.

### Evaluation

- `benchmarks/heldout.py` runs the pre-registered evaluation on a split of the held-out TPTP
  v10.0.0 corpus. The TEST results of 0.1.0 are in `benchmarks/results/` and the README.

## 0.1.0 (2026-11-27)

The first public release. It collects the work of the development phases from 2026-11-05 to
2026-11-27.

### Checking

- Every `UNSAT` passes `Kernel.check`, whose final decision is made by checkers extracted from
  the Rocq development in `rocq/`: axiom permits, NNF, Skolemization, distributive, definitional
  and hybrid CNF, clause normalization and encoding, and every primitive inference. Clause
  refutations, AVATAR refutations and natural-deduction certificates are accepted.
- Rocq proofs connect accepted certificates to standard classical natural deduction, prove that
  every refutable theory has an accepted certificate, and that the reference enumeration finds one
  at a finite stage, including for recursively axiomatized theories.
- The AVATAR checker keeps its databases in indexed maps; each indexed function is proved equal to
  its list specification, so certificates with large Boolean parts check in near-linear time.
- `axiom-replay` re-checks a certificate in a separate process against a theory or problem that
  you name; `--rocq` exports a refutation that Rocq checks on its own.
  `scripts/recheck.sh` runs both, with an audit of every `Print Assumptions` result.
- `dune build @rocq` re-extracts the checkers byte for byte, compiles 26 generated proofs and
  audits every assumption against an allow-list that rejects known ways to hide assumptions.

### Search

- A single search policy (`production`): ordered resolution and superposition with KBO and
  literal selection with look-ahead, demodulation, multiset subsumption, AVATAR splitting with an
  incremental CDCL solver, congruence closure with proofs, goal expansion, and synthesis of schema
  conditions by enumeration and guidance.
- Worker strategies follow from the number of workers alone (the balanced rule): half the workers
  run production at different queue phases, the other half run OCaml ports of the E 3.5.9
  heuristics `e208`, `y1346` and `sat001` (with E's definition unfolding, given-clause loop and
  selection order) and E's literal selection on the production queues (`calc:e`).
- One worker, the default, time-shares production and `e208` 1:1 in slices of a deterministic work
  clock on inputs without schemas.
- Theories with schemas get a schema probe lane per worker that tries the fixed axioms with one
  instance at a time, ranked with finite models and fed by an observational-equivalence condition
  source over the theory's own language. It carries no prior about the shape of contradictions.
- A deterministic per-worker memory budget in the engine's own units (256 MiB by default) replaces
  permanent-stop count caps; explicit `--max-given`, `--max-generated` and `--max-retained` caps
  remain.
- Workers and the reference enumeration run as separate processes with a reclamation framework:
  no child outlives the supervisor, and a crashed worker loses only itself.
- Certificates are kept short: a long final congruence conflict is explained along the cheapest
  paths with shared lemmas, and an AVATAR refutation is re-solved when that gives fewer steps. The
  search itself is unchanged by both.
- Evaluation-only strategies (further E and Vampire ports, LPO members) and `AXIOM_*` switches stay
  available for measurements, outside the default search ([docs/evaluation.md](docs/evaluation.md)).

### Command line

- Five binaries: `axiom-fuzz`, `axiom-replay`, `axiom-minimize`, `axiom-mutate` and
  `axiom-reference`.
- The default output of `axiom-fuzz` is a short summary (with the schema instances tried and the
  proof clauses unless `--quiet`); `--stats` prints the counters of the workers, the probe lane
  and the reference enumeration. `--output` is an alias of `--certificate`. All binaries print
  `--version`, use the same exit codes (0 for a completed run, including `UNKNOWN`; 1 for a
  rejected certificate; 2 for errors) and report errors as one `Error: ...` line. A notice on
  standard error says when evaluation overrides are active.
- Inputs, certificates and checkpoints are read up to 32 MiB; `axiom-fuzz` warns when a
  certificate it writes exceeds the limit, and `--stats` prints the size of each one.

### Fixes made during development

- Subsumption is multiset subsumption: set subsumption let a clause delete its own factors, so
  some unsatisfiable inputs saturated.
- Rewriting with a binary equivalence could delete clauses that were not redundant (defect B), in
  production, `e208` and `calc:e`. The rewritten clause is now retired only as a redundancy
  deletion; otherwise the original stays and the rewrite is added as an ordinary consequence
  (`derive`, the default).
- Orphan deletion lost refutations in some evaluation-only E members.
- Schema enumeration steps and the probe lane stop at the deadline.

### Known limitations

- `UNKNOWN` is not evidence of consistency, and the reference enumeration has no practical time
  bound.
- The memory budget is cooperative and does not bound the reference enumeration or the resident
  set size.
- TPTP input is limited to untyped FOF and CNF without `include`; natural-deduction certificates
  have no TSTP output.
- Windows is not supported.
