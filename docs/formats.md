# File formats

None of these formats carries a version number. In 0.x each release reads only the formats it
writes: a certificate or checkpoint from another version is rejected, never migrated, so
regenerate it with the version you use. The CSV files carry a `metrics_version` column.

All files are written to a temporary file in the target directory (`.axiom-fuzzer-<pid>-*.tmp`)
and renamed into place.

## Certificates

A certificate is one data-only S-expression. It is read with escapes for strings and no code
evaluation or `Marshal`. The reader refuses files over 32 MiB (33,554,432 bytes) or nested deeper
than 512 levels; the same limits apply to TPTP input and checkpoints. The limits bound the size,
not the time or memory needed to read a file close to them.

```text
(axiom-fuzzer THEORY (cnf MODE) AXIOMS STEPS ROOT-ID)
(axiom-fuzzer THEORY (cnf MODE) AXIOMS STEPS 0 (avatar COMPONENTS SPLITS BOOLEAN-STEPS BOOLEAN-ROOT-ID))
(axiom-fuzzer THEORY (natural CODE))
```

The three forms are a clause refutation, a clause refutation with AVATAR splitting, and a
natural-deduction certificate.

- `THEORY` is the theory name (`tptp` for problems read with `--problem`). The checker compares
  it with the manifest that it is given, never takes the theory from the certificate.
- `MODE` is `distributive`, `definitional` or `hybrid`: the CNF transformation that the checker
  re-runs on every axiom (hybrid chooses per axiom, with a threshold of 32 estimated clauses).
- `AXIOMS`: each axiom with its ID, name, origin (`fixed`, `imported`, `schema` with the schema
  and its condition, `registered-schema` with the schema name, revision and encoded parameter, or
  an enumerated stage) and its source formula.
- `STEPS`: `(ID CLAUSE RULE)`. The rules are `input`, `component`, `resolve`, `factor`,
  `equality-resolve`, `equality-factor` and `paramodulate`, with parent IDs, literal positions,
  substitutions and subterm paths. `(input AXIOM-ID CLAUSE-INDEX)` refers to the checker's own
  clausification of the axiom. Skolem symbols are `Skolem(AXIOM-ID, OCCURRENCE)` and definitional
  predicates `(definition AXIOM-ID OCCURRENCE ARGUMENTS)`; names in the certificate are never
  trusted to identify them.
- `ROOT-ID` is the ID of the empty clause. With AVATAR it is 0, and the Boolean root ends the
  proof instead.
- `COMPONENTS` is a list of clauses (position = component ID); α-equivalent components share a
  representative. `SPLITS` is a list of `(FO-PARENT-ID (COMPONENT-ID ...))`. `BOOLEAN-STEPS` are
  `(ID (SIGNED-LITERAL ...) RULE)`, where component `i` is the literal `i+1` (positive) or
  `-(i+1)` (negative), and the rules are `(split SPLIT-ID)`, `(conflict FO-EMPTY-ID)` and
  `(boolean-resolve LEFT-ID PIVOT-COMPONENT-ID RIGHT-ID)`. The dependencies of each first-order
  clause on components are recomputed from the proof; the file stores none.
- `CODE` of a natural-deduction certificate is a non-negative integer or a pair of codes: the
  axiom permits and the proof tree, encoded as in `rocq/Reference/Encoding.v`.

Deleting unused axioms from a certificate keeps the original IDs of the others, so Skolem symbols
keep their identity. [guarantees.md](guarantees.md#what-is-checked-before-unsat) lists what the
checker verifies.

## Rocq output

`axiom-fuzz --rocq FILE` and `axiom-replay --rocq FILE` write a `.v` file that depends only on the
project's Rocq library (logical path `AxiomFuzzer`), compiled from `rocq/`:

```sh
rocq compile -q -Q PATH/TO/COMPILED/rocq AxiomFuzzer FILE.v
```

[scripts/recheck.sh](../scripts/recheck.sh) compiles the library and the file for you.

- A clause refutation defines the source axioms, the CNF proposal, the symbol table and the
  primitive steps, and proves `proof_checked` by `vm_compute` of the checker and
  `source_axioms_unsatisfiable`: the printed finite set of source axioms has no model.
- An AVATAR refutation adds the components, the conditional first-order proof, the splits and
  the Boolean DAG, checked by `avatar_check_sources`.
- For theories with fixed axioms and built-in schemas only, the file also contains the manifest
  and proves `theory_refuted` and `theory_unsatisfiable`. With a registered schema it proves the
  statement for the finite set of expanded instances only; the OCaml callback is never written as
  a Rocq axiom.
- A natural-deduction certificate gives `source_refutation` from the finite source premises.

Symbol, schema and parameter names are written as UTF-8 byte lists, so quotes, newlines, NUL and
comment delimiters in a name cannot change the meaning of the file. Regenerate a `.v` file from
the certificate rather than editing an old one.

## TSTP

`--tstp FILE` writes a TSTP derivation for other tools: the original axioms, the clausification
of each axiom (new Skolem symbols are introduced once, with `status(esa)` and
`new_symbols(skolem, [...])`, and definitional predicates with `new_symbols(definition, [...])`),
the clauses used, and the inferences with their parents. AVATAR proofs add a nullary predicate
`avatar_b_<id>` for each component, the dependencies as extra negative literals, and the split,
conflict and Boolean resolution steps (`avatar_component`, `avatar_split`, `avatar_conflict`).
Natural-deduction certificates have no TSTP output; the binary reports an error instead of
writing an empty proof. TSTP is never read back as a proof.

## FOF and CNF exports

`--export-fof FILE` writes the source axioms of the selected search as TPTP FOF. `--export-cnf
FILE` writes their clauses in the CNF mode of the selected search. Both rename symbols
consistently so that they cannot clash in other tools: source functions become `src_...`,
predicates `srcp_...`, Skolem functions `sk_<axiom>_<occurrence>` and definitional predicates
`def_<axiom>_<occurrence>`.

## Checkpoints

`--checkpoint FILE` stores the reference enumeration's cursor:

```text
(certified-frontier MANIFEST LEVEL ((PREFIX DEPTH) ...) COUNT WITNESS)
```

The manifest holds the theory name, the signature, the fixed axioms, and the names, revisions
and registration order of the schemas. A checkpoint with an unknown form, another manifest, an
invalid frontier or a witness that is not a natural-deduction certificate is refused, and a saved
witness is checked again when the run resumes. The file is saved every 1,000 ticks and at the end
of the run. Concurrent use of one checkpoint is refused through an in-process mutex and an OS
lock; an empty `.lock` file left behind does not mean that the checkpoint is in use. The search's
own state (clauses, indexes, the proof DAG) is not saved. A checkpoint that you edit by hand voids
the completeness argument, and saves are not `fsync`ed.

Changing the candidate order, the schema enumeration order or the CNF contract of the reference
enumeration requires a new head tag (instead of `certified-frontier`) or deleting old checkpoints.

## CSV metrics

| Option | Rows |
| --- | --- |
| `--metrics FILE` | One row for the selected result: the search counters, the reference enumeration (`reference_trials`, `reference_stage`, ...), `proof_source`, the worker strategy, and the process group's total CPU time and peak RSS |
| `--worker-metrics FILE` | One row per heuristic worker: the same counters for that worker, its strategy, single-worker slice columns (`slice_*`), memory-budget columns (`budget_*`, `peak_footprint_words`), process ID, exit status, CPU time and peak RSS |
| `--schema-metrics FILE` | One row per worker and schema: candidates and injected instances, split into exhaustive and guided |
| `--profile FILE` | One row per pipeline stage and event: wall seconds, CPU seconds, allocated words, calls |

The summary and worker files start with `metrics_version` (6 in 0.1.0). Columns that only a
heuristic worker can fill are empty in a row whose proof came from the reference enumeration.
Columns named `r13_*` and `r14_*` are fixed names from earlier experiments, not modes. RSS is
reported in bytes on every platform (macOS reports `ru_maxrss` in bytes, Linux in KiB).
