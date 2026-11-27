# Guarantees and trust model

This page says what an answer of axiom-fuzzer means, which parts of the system that meaning
rests on, and how to re-check a certificate yourself.

## What the answers mean

- **`UNSAT`** means that the tool found a refutation certificate and that `Kernel.check`
  accepted it. The final decision of `Kernel.check` is made by checkers extracted from the Rocq
  development in `rocq/`. The Rocq theorems listed below show that an accepted certificate
  refutes the theory *as the tool read it*: the theory has no model over a non-empty domain.
- **`UNKNOWN`** claims nothing. It is not evidence of satisfiability or of consistency, and not
  even of difficulty: a run with more time, more workers or another build may find a
  refutation.
- **`SAT`** is never reported. A Boolean model found by the AVATAR solver, a saturated clause
  set, or a failed finite-model search is not reported as a model of the theory.

### What is checked before `UNSAT`

A clause refutation (with or without AVATAR) is accepted only if all of these hold:

1. The theory name in the certificate matches the manifest given to the checker.
2. Every axiom is allowed by that theory: a fixed axiom, an instance of a built-in schema whose
   formula matches the expansion of its condition, an instance of a registered schema that its
   checker accepts, or an enumerated axiom whose stage reproduces it.
3. The NNF, Skolemization and CNF of every axiom, rebuilt independently, match the input
   clauses of the proof.
4. Every inference step matches its parents, literal positions, substitution, subterm
   position and conclusion. For AVATAR, the dependencies on component assumptions are
   recomputed from the proof, and every split and Boolean step is checked.
5. The proof ends in the empty clause (for AVATAR, in the empty Boolean clause).

A natural-deduction certificate is checked by the extracted natural-deduction checker,
together with the permits of its axioms. A conditional empty clause, a SAT solver's answer, an
`UNSAT` string from another tool, or a prover's exit code is never accepted as a proof.
Unknown Skolem symbols, arity mismatches, cyclic substitutions, missing or later parents,
duplicate IDs and forged conclusions are rejected.

## What is proved

The theorems are in `rocq/`; `dune build @rocq` compiles them and audits every `Print
Assumptions` result ([Re-check routes](#4-checker-provenance)).

| Statement | Theorem |
| --- | --- |
| The primitive clause checker is sound: accepted input clauses have no model | `Clause.Kernel.check_sound` |
| An accepted source certificate gives a finite derivation of falsity from the theory, and the theory has no model | `Source.Kernel.check_derives_false`, `Source.Kernel.check_sound` |
| An accepted AVATAR certificate refutes the input clauses and the theory | `Clause.Avatar.check_sound`, `Source.Kernel.avatar_check_sound` |
| An accepted AVATAR certificate gives a refutation in standard natural deduction | `Source.Standard.Connection.avatar_check_is_standard` |
| The source refutation calculus embeds into standard classical natural deduction | `Source.Standard.Connection.refutation_is_standard` |
| An accepted certificate of any form gives a standard refutation, and every standard refutation has an accepted certificate | `Reference.Certificate.Kernel.check_sound`, `check_complete`, `check_iff_standard` |
| If a refutation exists, the reference enumeration finds an accepted certificate at a finite stage | `Reference.Certificate.Kernel.accepted_eventually_found`, `Reference.Progress.refutation_found` |
| The same for recursively axiomatized theories given by an enumerator | `enumeration_check_iff`, `Kernel.check_iff_enumerated`, `enumeration_eventually_found`, `recursively_axiomatized_complete` |
| In every structure that satisfies the defining axioms of a `Definitions` environment, a formula and its expansion have the same truth value; a refutation of the expanded axioms therefore refutes the definitions together with the original axioms | `Source.Definitions.expand_correct`, `expansions_match_sound` |
| The indexed checkers that run decide exactly as the list specifications | `check_correct`, `replay_indexed_correct`, `fast_check_correct` and others |

The standard logic is classical first-order natural deduction (`rocq/Logic/Deduction.v`), with
equality axioms added as schemas; its completeness (`rocq/Logic/Completeness.v`) is proved in
the repository, not assumed. A Rocq file exported with `--rocq` proves
`source_axioms_unsatisfiable` for the finite set of source axioms that the certificate uses,
and, for theories with fixed axioms and built-in schemas only, also `theory_refuted` and
`theory_unsatisfiable` for the whole manifest. For a theory made with `Theory.of_definitions`
it also proves `defined_theory_unsatisfiable`: the definitions' defining axioms together with
the original axioms that the certificate uses, closed in the extended language, have no model.

## Assumptions of the metatheory

These appear as explicit arguments of the theorems, not as global axioms:

- a non-empty domain;
- excluded middle and functional choice, for the semantic soundness statements;
- the comparison interface of the normalization functor (instantiated in the generated proofs by
  a ranked order whose properties are proved).

The bridge from clause refutations and AVATAR to standard natural deduction also uses `classic`,
`functional_extensionality_dep`, `propositional_extensionality`, `relational_choice` and
`dependent_unique_choice` from the Rocq Stdlib. These are assumptions of the metatheory; they add
nothing to the theory being refuted (the `zf` theory has no axiom of choice). `@rocq` checks that
every `Print Assumptions` result is closed or lists only these assumptions, theorem by theorem
(`scripts/rocq_assumptions.py`). It does not detect assumptions passed as theorem arguments, so
read the statements as well.

## Trusted computing base

| Component | Route 1: in the run | Route 2: `axiom-replay` | Route 3: Rocq |
| --- | --- | --- | --- |
| Rocq kernel (including the bytecode VM used by `vm_compute`) and Stdlib | trusted (the extracted checkers come from it) | trusted | trusted |
| Rocq definitions of syntax, semantics and the built-in schemas (`rocq/Logic`, `rocq/Source`) | trusted | trusted | trusted |
| The metatheory assumptions above | trusted | trusted | trusted |
| The input side: TPTP reader (`lib/io`), source construction (`lib/syntax`), built-in theory manifests (`lib/theory`) | trusted | trusted | trusted; compare the printed `source_axioms` and `theory_manifest` with your input |
| The `check` callback of a registered schema, and its codec | trusted by definition | not available: replay cannot rebuild such a theory | trusted |
| Rocq extraction (constructor realizations, `nat` and `int` mappings) | trusted | trusted | not needed |
| The OCaml compiler, runtime, native comparisons and read-only lookups | trusted | trusted (build replay with another compiler to diversify) | not needed |
| The glue that calls the checkers (`lib/proof/kernel.ml`, `checked_clauses.ml`) | trusted | trusted | not needed |
| `Marshal` frames from worker processes of the same binary | trusted for type safety only: the supervisor re-checks every certificate itself | not involved | not involved |

Not trusted at all, because the checkers re-check their output or compute it themselves: the
OCaml traversal of a `Definitions` expansion (the extracted `expand_formula` is the result, and
`expansions_match` relates the expanded originals to the manifest), the search and its strategies,
proof extraction, `verified.ml` (the expansion into primitive steps), the CNF, Skolemization and
definitional proposals, the AVATAR renaming proposals, the SAT solver, the minimizer, the
history hints and the checkpoints.

Not covered by any proof: the completeness of the heuristic search (term orderings, literal
selection, indexes, scheduling, AVATAR's model switching, resource limits), anything about
`UNKNOWN`, the practical time to find a refutation, and all performance numbers. The reference
enumeration's completeness theorem is about the abstract enumeration, not about machine
integers, finite memory, the 32 MiB file limit, the operating system or checkpoint I/O.

## Re-check routes

From least to most independent of the run that produced the certificate:

### 1. In the run

Every reported `UNSAT` has passed `Kernel.check` in the supervisor process. A certificate found
by a worker process is checked again by the supervisor, against its own copy of the theory,
after it crosses the process boundary; the worker's verdict is not trusted.

### 2. A separate replay

```sh
axiom-replay --theory NAME CERT
axiom-replay --problem ORIGINAL.p CERT
```

This runs the same checker code in another process, from the certificate file. Name the theory
or the problem yourself: a certificate is never its own authority, and a certificate of a TPTP
problem needs `--problem`. `ORIGINAL.p` must be the exact bytes that were solved, without
`include` lines; when a benchmark prepared the file, compare its SHA-256 with the corpus
manifest. For more diversity, build `axiom-replay` yourself with another OCaml compiler; the
development measurements re-checked every `UNSAT` with a replay built without flambda.
Certificates larger than 32 MiB cannot be read.

### 3. Rocq

```sh
scripts/recheck.sh --theory NAME CERT
scripts/recheck.sh --problem ORIGINAL.p CERT
```

The script runs route 2, exports the refutation with `axiom-replay --rocq`, compiles `rocq/`
with Rocq 9.3.0 and its Stdlib, compiles the export against it
(`rocq compile -Q <compiled rocq/> AxiomFuzzer Refutation.v`), and audits every `Print
Assumptions` result. The exported file re-runs the checker inside Rocq (`vm_compute`) and
proves `source_axioms_unsatisfiable`, and for fixed-axiom and built-in-schema theories also
`theory_refuted` and `theory_unsatisfiable`. For that certificate, this takes the extraction,
the OCaml compiler and the OCaml runtime out of the trusted base. Compare the printed source
axioms or manifest with your input; names are printed as byte lists. Set `RECHECK_KEEP=1` to keep
the exported file.

### 4. Checker provenance

```sh
dune build @rocq
```

This re-extracts the checkers from `rocq/` and compares all 14 extracted files with `lib/` byte
by byte, compiles 26 generated proofs (from the built-in theories, the example problems and the
regression tests), checks every `Print Assumptions` result against the allow-list, and checks
that the audit still rejects a set of known holes (`tests/fixtures/rocq_audit/`). The byte
comparison needs a Rocq 9.3.0 built with OCaml 5.5.x ([installation.md](installation.md#rocq-for-the-proofs)).

## Notes for verifiers

- Certificates have no version number. A certificate written by another version is rejected,
  not migrated: re-run the search with the version that you check with.
- A registered schema's `check` callback is part of the theory definition. Its correctness, its
  purity and its termination are the responsibility of whoever registers it; the theorems treat
  the set of formulas it accepts as the schema's axioms.
- The guarantee covers the theory as parsed. Unsupported TPTP input is rejected with an error,
  never reinterpreted, but whether the parsed theory is the one you meant is for you to check.
