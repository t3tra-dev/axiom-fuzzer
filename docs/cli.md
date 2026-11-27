# Command-line reference

axiom-fuzzer installs five binaries. This page lists their options, defaults, output and exit
codes for version 0.1.0; it was checked against each binary's `--help` and by running them.
During 0.x any of this may change without a migration path.

## Conventions shared by all binaries

| Item | Behaviour |
| --- | --- |
| Exit code 0 | The run completed: `UNSAT`, `UNKNOWN` or `VERIFIED` (and, for `axiom-mutate`, the mutants were written) |
| Exit code 1 | `axiom-replay` rejected the certificate (`REJECTED: ...`) |
| Exit code 2 | Usage error, unreadable or malformed input, I/O error, or an internal error |
| Errors | One line on standard error, `Error: MESSAGE`, for example `Error: Unknown theory: foo (known: naive, separation, ...)`. An unknown option prints OCaml's `unknown option` message and the usage text instead |
| `--help` | Lists the options with their defaults |
| `--version` | Prints the binary name and the version, for example `axiom-fuzz 0.1.0` |
| Output files | Written only when there is something verified to write, to a temporary file in the same directory that is then renamed; an interrupted run never leaves a partial file at the target path, and an error names the target path. A `--checkpoint` whose directory does not exist is reported on that directory |

An `UNKNOWN` result also exits 0, including the `UNKNOWN` of `axiom-reference` at a stage limit
or a machine resource limit. Read the `Result:` line, not the exit code, to tell `UNSAT` from
`UNKNOWN`.

## axiom-fuzz

```text
axiom-fuzz [--theory NAME | --problem FILE] [options]
```

Searches for a refutation of one theory. With neither `--theory` nor `--problem` it searches
the built-in theory `naive`.

### Input

| Option | Meaning |
| --- | --- |
| `--theory NAME` | A built-in theory: `naive`, `separation`, `separation-universal`, `foundation-self`, `mutated-separation` or `zf` ([theories.md](theories.md)) |
| `--problem FILE` | A TPTP problem in the supported FOF/CNF subset ([theories.md](theories.md#tptp-input)); cannot be combined with `--theory` |
| `--history FILE` | A certificate whose proof supplies hints to the schema synthesis (repeatable). It is checked like any input |

### Resources

| Option | Default | Meaning |
| --- | --- | --- |
| `--seconds N` | 10 | Wall-clock budget of each search process, measured from its start; the reference enumeration uses the same budget |
| `--workers N` | 1 | Number of heuristic worker processes, 1 to 64; a reference enumeration process runs in addition |
| `--memory-budget MIB` | 256 | Per-worker budget for the search state, in the engine's own deterministic units (8-byte words); 0 disables it |
| `--max-given N` | unlimited | A worker that has selected N clauses stops for the rest of the run |
| `--max-generated N` | unlimited | The same for generated clauses |
| `--max-retained N` | unlimited | The same for stored proof nodes |
| `--max-instances N` | unlimited | Schema instances that each generator (exhaustive and guided) may inject, over all schemas |

The worker strategies follow from `--workers` alone (the balanced rule, see
[architecture.md](architecture.md#strategies)): one worker time-shares the production policy
with the ported E heuristic `e208` on inputs without schemas and runs production with the
schema probe lane on theories with schemas; more workers split between production and the
ported heuristics. Beyond 44 workers some production workers repeat another worker's queue
phase, and a warning on standard error says how many.

The memory budget is cooperative. Over it, a worker first drops suspended scans, then trims
heavy passive clauses and withdraws schema instances (re-injected later), and it stops with
`memory budget exhausted` only if its state stays at twice the budget. A last safety net stops
a worker whose major heap reaches 16 times the budget (at least 1 GiB). The reference
enumeration is not budgeted.

### Output files

| Option | Writes |
| --- | --- |
| `--certificate FILE` | The certificate, for `axiom-replay`, `axiom-minimize` and `--history` ([formats.md](formats.md#certificates)) |
| `--output FILE` | The same as `--certificate`, the name the other binaries use |
| `--rocq FILE` | A Rocq source file that re-checks the refutation in Rocq ([guarantees.md](guarantees.md#3-rocq)) |
| `--tstp FILE` | A TSTP derivation, for other tools; not accepted back as a proof |
| `--export-fof FILE` | The source axioms the selected search used, as TPTP FOF |
| `--export-cnf FILE` | The hybrid CNF of those axioms, as TPTP CNF |
| `--metrics FILE` | One CSV row about the selected result |
| `--worker-metrics FILE` | One CSV row per heuristic worker |
| `--schema-metrics FILE` | One CSV row per schema: candidates and injected instances |
| `--profile FILE` | Wall time, CPU time and allocation per pipeline stage (input, setup, search, proof check, encoding, output) |
| `--checkpoint FILE` | Saves and resumes the reference enumeration's cursor ([formats.md](formats.md#checkpoints)) |

The proof outputs (`--certificate`, `--rocq`, `--tstp`) are written only on `UNSAT`; on
`UNKNOWN` an existing file at the path is left untouched. A certificate larger than the 32 MiB
reader limit is still written, with a warning on standard error, but `axiom-replay` and
`--history` cannot read it.

`--checkpoint FILE` creates the file or resumes from it; the same command run again continues
the enumeration. It is saved every 1,000 ticks and at the end, which slows the enumeration down
noticeably in short runs. A checkpoint from another version, or for another theory, is refused.

### Standard output

| Option | Effect |
| --- | --- |
| `--quiet` | Print only the summary lines: no schema instances, no proof clauses |
| `--stats` | Also print the search statistics: the probe lane's counters, the reference enumeration, every heuristic worker's stop and the selected search's counters |

`axiom-fuzz` prints a short summary. Without `--quiet` it also lists each schema instance it
tries (`[N] NAME: CONDITION`, before the summary) and the clauses of the proof (`#ID  CLAUSE`,
after the proof size). With `--quiet`, `axiom-fuzz --theory naive --quiet --certificate
russell.cert` prints:

```text
Theory: naive
Result: UNSAT
Reason: refutation verified
Used axioms: comprehension_1
Proof clauses: 5
Certificate: russell.cert
```

| Line | Content |
| --- | --- |
| `Theory:` | The theory's name (`tptp` for `--problem`) |
| `Result:` | `UNSAT` or `UNKNOWN` |
| `Reason:` | Why the run ended, for example `refutation verified`, `time limit; reference time limit`, `memory budget exhausted`, `bounded formula/clauses exhausted; consistency not established` |
| `Used axioms:` | On `UNSAT`: the names of the axioms the certificate uses (schema instances are named after their schema) |
| proof size | On `UNSAT`: `Proof clauses: N` for a clause refutation, `Proof steps (FO + Boolean): N` for an AVATAR refutation, `Deduction steps: N` for a natural-deduction certificate |
| `Certificate:` | With `--certificate` (or `--output`): the path of the written certificate. A certificate over the 32 MiB reader limit also gets a warning on standard error |

`--stats` adds these lines. `--metrics` and `--worker-metrics` record the same values as CSV
columns (the `reason` column keeps the lane counters):

| Line | Content |
| --- | --- |
| `Reason: ... [lane: ...]` | On theories with schemas, the probe lane's counters after the reason |
| `Replay verified: true` | The in-process `Kernel.check` accepted the proof |
| `Certificate bytes: N limit=L readable=B` | The certificate size, the reader limit (33,554,432) and whether `axiom-replay` can read it |
| `Reference: ticks=... cumulative=... stage=... seconds=... resumed=... reason=...` | The reference enumeration's progress in this run and in total |
| `Reference heap: peak_domain_words=N` | The reference process's peak major heap |
| `Proof source:` | `heuristic:N` (worker N), `probe:N` (worker N's schema lane), `reference`, or `none` |
| `Heuristic N: stop="..." ...` | Per worker: stop reason, active and collection time, given clauses, memory-budget responses, drops and trims, peak readings, and the digest of every budget reading and response |
| `Metrics: ...` | Generated, retained and given clauses, unifications, index postings, heap words and times of the selected search |

### Signals

Ctrl-C, SIGTERM and SIGHUP stop every worker cooperatively. The binary waits for all processes,
prints the result (`UNKNOWN` with a cancellation reason, or an `UNSAT` that was already verified)
and exits 0. If the binary itself is killed, its workers notice within milliseconds and exit; a
reference enumeration with a checkpoint saves first.

## axiom-replay

```text
axiom-replay [--theory NAME | --problem FILE] [--rocq FILE] CERT
```

Re-checks a certificate with the same extracted checkers, in a fresh process, against a theory
that you name. It prints `VERIFIED: theory=T axioms=A steps=S replay_seconds=X` and exits 0, or
prints `REJECTED: REASON` on standard error and exits 1.

| Option | Meaning |
| --- | --- |
| `--theory NAME` | Require this built-in theory's manifest. Without it, the theory named in the certificate is used |
| `--problem FILE` | The original TPTP problem. Required for certificates of TPTP problems (`theory=tptp`): a certificate is never its own authority |
| `--rocq FILE` | After verifying, export the refutation as Rocq source |

Pass the exact bytes that were solved: the problem file is part of the check. Certificates over
32 MiB cannot be read. Certificates of theories with registered OCaml schemas cannot be replayed
by this binary, because the schema's checker is OCaml code; re-check them through the library
([theories.md](theories.md#registering-a-schema)).

## axiom-minimize

```text
axiom-minimize CERT --output FILE [--problem FILE] [--seconds N] [--shrink-conditions N]
```

Shrinks a certificate: it tries to delete axioms, to shrink schema conditions and re-search, and,
for natural-deduction certificates, to remove unused or duplicate hypotheses and detours. Every
accepted step is re-checked against the original theory. It prints
`VERIFIED: axioms=A -> A' steps=S -> S' reduction_attempts=N inconclusive=M`.

| Option | Default | Meaning |
| --- | --- | --- |
| `--output FILE` | required | The smaller certificate |
| `--problem FILE` | | The original TPTP problem; required for TPTP certificates |
| `--seconds N` | 2 | Search budget per deletion attempt, condition-shrinking phase or natural-deduction reduction |
| `--shrink-conditions N` | 32 | Maximum number of condition-shrinking attempts |

The result is smaller, not minimal: the budget bounds every attempt, and nothing guarantees the
fewest axioms or the shortest proof.

## axiom-mutate

```text
axiom-mutate --output-dir DIR [--theory NAME | --problem FILE] [options]
```

Builds variants of a theory by changing one negation, connective, quantifier or subformula at a
time in the fixed axioms and in finitely many observed schema instances, then searches each
variant. A refutation is a refutation of the mutated theory, not of the original.

| Option | Default | Meaning |
| --- | --- | --- |
| `--output-dir DIR` | required | A directory that must not exist yet |
| `--theory NAME` | `zf` | The theory to observe |
| `--problem FILE` | | A finite TPTP problem instead of a theory |
| `--mutations N` | 16 | Maximum number of mutants |
| `--observations N` | 4 | Finite observation stages per schema |
| `--seconds N` | 1 | Search time per mutant |

`DIR/original.p` holds the observed finite axiom set, `DIR/mutant-NNNN.p` each mutant, and
`DIR/mutant-NNNN.cert` the certificate of each refuted mutant. Each mutant prints one line
`DIR/mutant-NNNN axiom=ID operator=OP path=P result=UNSAT|UNKNOWN`. Re-check a mutant with
`axiom-replay --problem DIR/mutant-NNNN.p DIR/mutant-NNNN.cert`.

## axiom-reference

```text
axiom-reference [--theory NAME | --problem FILE] [--max-stage N | --unbounded] [--output FILE] [--rocq FILE]
```

Runs the reference enumeration of natural-deduction certificates, the one that Rocq proves to
find a certificate at some finite stage whenever the theory is refutable
([guarantees.md](guarantees.md#what-is-proved)). It prints `reference_stage=N` for each stage,
then one result line, and exits 0 with each of them:

| Line | When |
| --- | --- |
| `VERIFIED: axioms=A steps=S` | A stage found a certificate, and the kernel check accepted it |
| `UNKNOWN: finite reference stage limit` | No stage up to `--max-stage` found one |
| `UNKNOWN: reference machine resource limit` | The stack or the memory ran out first (with `--unbounded`, or a large `--max-stage`) |
| `UNKNOWN: reference machine integer limit` | With `--unbounded`, the stage counter reached the largest machine integer; not reachable in practice |

| Option | Default | Meaning |
| --- | --- | --- |
| `--theory NAME` | `naive` | A built-in theory |
| `--problem FILE` | | A TPTP problem |
| `--max-stage N` | 2 | The last stage to try |
| `--unbounded` | | Keep increasing the stage until a certificate or a machine limit; the enumeration grows extremely fast |
| `--output FILE` | | Write the certificate found |
| `--rocq FILE` | | Export the refutation as Rocq source |

The enumeration has no practical time bound. Small stages end in `UNKNOWN` even on refutable
theories; `axiom-fuzz` runs the same enumeration as a streaming process beside its heuristic
workers.

## Environment variables

`AXIOM_*` variables and the hidden `--eval-strategies` option change or instrument the search
for evaluation only. Ordinary runs leave them unset. When any of them is active, `axiom-fuzz`
prints one line on standard error before it starts, naming them, for example
`Note: evaluation overrides active: AXIOM_MEASURE_COST_CLOCK=stopped, --eval-strategies=e208`.
An invalid value is an error (exit 2). The hidden `axiom-fuzz --eval-help` prints the table of
the variables; [evaluation.md](evaluation.md) and
[evaluation-switches.md](evaluation-switches.md) list them all.

`OCAMLRUNPARAM` (or `CAMLRUNPARAM`) is honoured. `axiom-fuzz` raises the minor heap to 1 M words
(8 MiB) at start-up unless `s=` sets it; the memory budget does not depend on these settings.
