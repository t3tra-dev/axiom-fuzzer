# Architecture

This page describes how axiom-fuzzer 0.1.0 is put together.

## Pipeline

```text
Theory / Source AST
  -> formula enumeration and guided synthesis of schema conditions
  -> schema instances with provenance
  -> NNF, Skolemization, hybrid or definitional CNF
  -> conditional Active/Passive saturation engine  <->  incremental SAT (AVATAR)
  -> unconditional empty clause or Boolean refutation, with its dependency DAG
  -> independent re-construction of the inputs (OCaml)
  -> checkers extracted from Rocq: axiom permits, preprocessing, encoding, every inference
  -> certificate, TSTP, Rocq source
```

The search proposes; the checkers decide. A refutation that fails the independent re-check is an
internal error, never an answer.

## Modules

| Directory | Content |
| --- | --- |
| `lib/syntax` | Terms and formulas with abstract IDs, signatures, de Bruijn indices, capture-avoiding substitution |
| `lib/arena` | Hash-consed search terms, typed hash tables, interned symbols |
| `lib/theory` | Fixed axioms, schemas, the `Definitions` API, enumerated theories, manifests |
| `lib/clausify` | Polarity-aware NNF and Skolemization, distributive, definitional and hybrid CNF |
| `lib/unify` | Unification with occurs check, a binding table with trail and rollback |
| `lib/calculus` | Resolution, factoring, equality resolution and factoring, paramodulation, KBO and LPO, demodulation, contraction, literal selection, the strategy table |
| `lib/indexing` | Indexes for resolution, subsumption (feature vectors), equality subterms and variants |
| `lib/saturation` | The saturation engine: conditional knowledge, goals, consumers, AVATAR, congruence closure, the memory budget, the ported E and Vampire heuristics |
| `lib/synthesis` | Lazy formula enumeration, guided synthesis of schema conditions, axiom mutation, finite-model pools for the probe lane |
| `lib/scheduler` | Interleaving of schema enumeration and deduction, the single-worker time slices, the schema probe lane, the process portfolio, the reference enumeration |
| `lib/proof` | The proof DAG, the independent re-check, the bridge to the extracted checkers, the extracted checkers themselves, minimization |
| `lib/io` | The data-only S-expression reader and writer, TPTP, TSTP, certificates, CSV |
| `lib/telemetry*`, `lib/deadline`, `lib/process_stubs.c` | A monotonic clock without allocation, RSS and heap readings, amortized deadline checks, the lifeline thread of worker processes |
| `rocq/` | The Rocq development: syntax and semantics, schemas, preprocessing, the clause and AVATAR checkers, standard natural deduction and its completeness, the reference enumeration, extraction |
| `bin/` | The five binaries |

The modules that take part in the final decision, and their boundaries:

| Module | Role |
| --- | --- |
| `Wire`, `Wire_types` | Portable proof data and the source, schema and axiom types shared with Rocq. No inference judgement |
| `Verified` | Expands each search inference into primitive steps. Not trusted: its output is checked |
| `Checked_clauses` | A private module that connects the extracted preprocessing and normalization to `Kernel` |
| `Kernel` | Rebuilds manifest, provenance, signature, substitutions and inferences, and calls the extracted checkers for the final decision |
| `Kernel_checker`, `Source_checker`, `Wire_checker`, `Wire_normalizer`, `Rocq_checker`, `Avatar_checker`, `Natural_checker` | Extracted from `rocq/Extraction.v`; never edited by hand |

The search's unification, rewriting, clausifier and clause normalization are not shared with the
checking side. The one exception, the AVATAR split renaming, is a proposal that the extracted
checker verifies.

## Rocq layout

The 24 files in `rocq/` map to the logical path `AxiomFuzzer` (`-Q rocq AxiomFuzzer`), so
`rocq/Source/Language.v` is `AxiomFuzzer.Source.Language`.

| Files | Content |
| --- | --- |
| `Clause/Kernel.v`, `Clause/Avatar.v` | Numeric clauses, their semantics and checker; AVATAR splitting, conditional proofs and Boolean resolution; soundness and indexed-checker equivalence |
| `Source/Language.v`, `Source/Validation.v`, `Source/Kernel.v`, `Source/Refutation.v`, `Source/Standard.v` | Source syntax, binding, substitution, Boolean normalization and schemas; axiom permits; the integrated checker and its soundness; the connection to standard natural deduction |
| `Preprocess/NormalForms.v`, `Preprocess/Quantifiers.v`, `Preprocess/SkolemModel.v` | NNF, distributive and definitional CNF; quantifier traversal and Skolem witnesses; model extension |
| `Wire/Syntax.v`, `Wire/Preprocess.v`, `Wire/Refutation.v` | The shared term and clause types, the concrete preprocessing, normalization and encoding |
| `Logic/Syntax.v`, `Logic/Deduction.v`, `Logic/Completeness.v` | Standard first-order syntax, classical natural deduction, and its completeness (Henkin construction) |
| `Reference/Certificate.v`, `Reference/Encoding.v`, `Reference/Enumeration.v`, `Reference/Progress.v`, `Reference/Theory.v` | Certificates and permits, codecs, the finite-stage enumeration, the streaming enumeration, recursively axiomatized theories |
| `Examples/Completeness.v`, `Examples/Refutation.v` | Worked examples checked in the build |
| `Extraction.v` | Extraction of the seven checker modules (14 files) |

No external Rocq project is vendored; the development uses the Rocq Stdlib only.

## The search

Every worker runs a given-clause saturation engine over clauses that carry a support set (the
AVATAR components they depend on) and a proof. The default policy, `production`, combines:

- ordered resolution and superposition with unit-weight KBO, negative literal selection with a
  bounded look-ahead, equality factoring and resolution, demodulation and backward
  demodulation, multiset subsumption and subsumption resolution;
- AVATAR splitting of clauses into variable-disjoint components, with an incremental CDCL
  solver whose refutations are re-checked as Boolean resolution DAGs;
- congruence closure of ground unit equations, with proofs;
- goal expansion with general clauses and equations, and requests from ordinary inference work
  that intermediate proofs can answer;
- for theories with schemas, synthesis of schema conditions: exhaustive enumeration of formulas
  in the theory's own language, plus guided synthesis from the clauses of the search (remaining
  conditions, complementary structure, proof history).

Clause selection alternates two weights, age and protected slots per clause kind. No problem
names, problem-specific settings or priors are used; the TPTP role `negated_conjecture` is read
as a selection hint by the ported E heuristics only.

### Strategies

The strategies of the workers follow from the number of workers W alone (the balanced rule,
`Strategy.balanced`):

- Workers 0 to ⌈W/2⌉−1 run `production` at queue phases 0, 1, ... (a phase shifts the start of
  the periodic clause-selection schedule, so each worker searches differently).
- The other ⌊W/2⌋ workers take, round-robin, the OCaml ports of the E 3.5.9 heuristics `e208`,
  `y1346` and `sat001` (literal selection, term ordering, clause selection, definition
  unfolding and given-clause loop as in E), and `calc:e` (E's literal selection on the
  production queues). Copy k of an E heuristic runs at phase k.

| W | production (phases) | other workers (phases) |
| --- | --- | --- |
| 1 | 0, time-shared with `e208` (0) on inputs without schemas | |
| 2 | 0 | `e208` (0) |
| 4 | 0, 1 | `e208` (0), `y1346` (0) |
| 8 | 0 to 3 | `e208` (0), `y1346` (0), `sat001` (0), `calc:e` (7) |
| 16 | 0 to 7 | `e208`, `y1346`, `sat001` at 0 and 1 each, `calc:e` at 11 and 15 |
| 64 | 0 to 31 | `e208`, `y1346`, `sat001` at 0 to 7 each, `calc:e` ×8 |

No strategy gets more than ⌈(W/2)/4⌉ of the diversified workers. Phases repeat with a period
(22 for the production queues, 11 for `e208` and `sat001`, 26 for `y1346`), so all workers
search differently up to W = 44; beyond that some production workers repeat a phase and the CLI
warns. The ported heuristics run inside axiom-fuzzer; E is never started. More strategies exist
for evaluation only ([evaluation.md](evaluation.md)).

### One worker

With one worker (the default) and no schemas, the worker time-shares two engines: `production`
continues throughout, and `e208` is a lane that admits the input once and is suspended and
resumed. They alternate in slices of a deterministic work clock (15,000,000 units of allocated
words plus 20 per cooperative deadline check, about 50 ms at the nominal rate), and an overrun is
carried into the next slice, so the work is split 1:1 over a run. If either engine stops without
a proof for a reason other than the deadline (budget, cap, exhaustion), its state is released and
the other engine runs alone. On theories with schemas the single worker runs `production` with
the schema probe lane instead.

### The schema probe lane

On theories with schemas, each worker also runs a probe lane: a separate bounded engine that
tries to refute the fixed axioms together with one schema instance at a time. The instances come
from the schema's own enumeration (looked ahead), from the instances that the main search
injected, and from an observational-equivalence condition source: formulas of the theory's own
language, built smallest first and deduplicated by their truth tables over a pool of small
finite models. A finite-model pool also ranks the candidates. Waiting instances are grouped by
schema and by shape, so that no schema or shape crowds out the others. The lane runs while its
own work stays within half of the total, counting the main engine's allocation at a calibrated
weight of 1.5. The lane carries no prior about the shape of contradictions.

## Memory budget

Each worker has a budget for its search state, counted by the engine itself in 8-byte words (the
footprint of retained proof nodes, suspended scans and goal-index postings), not by the garbage
collector. For the same search, the readings and the responses therefore do not depend on the
machine, the load, the GC settings or the number of workers. Over budget, a worker drops
suspended scans (resumed later from their positions), then trims a quarter of the heaviest
passive clauses and withdraws schema instances (re-injected later under new IDs); fixed axioms
and the negated conjecture are never dropped. It stops only if the footprint stays at twice the
budget, or at the GC-based safety net (16 times the budget, at least 1 GiB). After trimming, the
search is incomplete and never reports saturation. Auxiliary tables (index cells, interned
symbols, caches) are outside the footprint.

## Processes

The CLI is a supervisor that forks each heuristic worker and the reference enumeration as a
separate OS process (a Domain-based variant exists for A/A measurements). Processes do not share
a heap, so no worker waits for another's minor collections. The reclamation invariants:

1. Each child creates its own session and process group right after `fork`; the supervisor
   signals only its own children and only before reaping them.
2. On every path (success, a child's failure, the supervisor's own exception) the supervisor
   kills the remaining process groups and reaps every child before it returns.
3. A child never outlives the supervisor: a C thread in each child waits on a lifeline pipe and
   ends the child (after a checkpoint save, for the reference enumeration) when the supervisor
   disappears, however it disappears.
4. Each report is one length-prefixed frame with an MD5 digest; a truncated or corrupt report
   loses that worker only. The supervisor re-checks every certificate with its own copy of the
   theory.
5. Temporary files carry the writer's PID and are removed by the supervisor, or by the next run
   when both died.

Randomized tests send signals at random times to the CLI, its process group and its children and
check that no process, temporary file or descriptor is left behind
([development.md](development.md#tests)). The mechanism uses POSIX pipes, threads and process
groups only.

## The reference enumeration

Besides the heuristic workers, one process steps through the Rocq-proved enumeration of
natural-deduction certificates (`Reference.Progress.tick`, extracted). It continues for the whole
time budget even when the heuristic workers stop at their caps or budgets, and whatever it finds
goes through the same `Kernel.check`. Its theorem says that every refutable theory is refuted at
some finite stage; it gives no practical bound. `--checkpoint` saves and resumes its cursor.

## Determinism

The search reads two kinds of clocks. Deterministic work clocks (allocated words, check counts)
drive the single-worker slices, the probe lane's share and the memory budget. The default
scheduling costs read wall time, so two runs of the same binary on the same input can differ
under load. With `AXIOM_MEASURE_COST_CLOCK=stopped` and caps that end the search before the time
limit, a search depends only on its input and its binary. Because the work clocks count allocated
words, builds that allocate differently (dev and release, other compilers) can schedule
differently: "the same search" is defined per build configuration.

## Boundaries

Not implemented, by design or so far: a hard per-worker memory limit in bytes, a memory limit for
the reference enumeration, checkpoints of the heuristic search, sharing of clauses or proofs
between workers, learned models for synthesis, importing proofs from other provers, TSTP output
for natural-deduction certificates, and a formalization of the `Definitions` expansion.
Substitution trees and packed term arenas are in scope but not built. The completeness of the
heuristic search as a whole (orderings, selection, scheduling, AVATAR's model switching, the
budget) is not proved; the reference enumeration carries the completeness guarantee.
