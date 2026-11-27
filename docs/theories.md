# Theories, schemas and the library API

axiom-fuzzer refutes theories of three kinds, all checked by the same `Kernel.check` and stored
in the same certificate format:

- **fixed axioms**: a finite set of first-order formulas (the built-in theories, a TPTP problem,
  `Theory.custom`);
- **axiom schemas**: infinitely many axioms, one per parameter (the four built-in schemas, and
  schemas you register with `Theory.Schema.create`);
- **recursively enumerated theories**: any axiom set given by a total enumerator
  (`Theory.of_enumerator`).

## Built-in theories

The built-in theories use one binary predicate `member` (written `∈`) and equality.

| `--theory` | Fixed axioms | Schemas | Default result |
| --- | --- | --- | --- |
| `naive` | none | comprehension | `UNSAT` (Russell) |
| `separation` | none | separation | `UNKNOWN` |
| `separation-universal` | universal | separation | `UNSAT` |
| `foundation-self` | pairing, foundation, self-member | none | `UNSAT` |
| `mutated-separation` | none | unrestricted separation | `UNSAT` |
| `zf` | extensionality, empty, pairing, union, power, infinity, foundation | separation, replacement | `UNKNOWN` |

The fixed axioms (`lib/theory/theory.ml`):

| Name | Formula |
| --- | --- |
| extensionality | ∀a ∀b ((∀x (x ∈ a ↔ x ∈ b)) → a = b) |
| empty | ∃e ∀x ¬(x ∈ e) |
| pairing | ∀a ∀b ∃p ∀x (x ∈ p ↔ (x = a ∨ x = b)) |
| union | ∀a ∃u ∀x (x ∈ u ↔ ∃y (y ∈ a ∧ x ∈ y)) |
| power | ∀a ∃p ∀x (x ∈ p ↔ ∀y (y ∈ x → y ∈ a)) |
| infinity | ∃i ((∃e (∀x ¬(x ∈ e) ∧ e ∈ i)) ∧ ∀x (x ∈ i → ∃s (s ∈ i ∧ ∀y (y ∈ s ↔ (y ∈ x ∨ y = x))))) |
| foundation | ∀a ((∃x x ∈ a) → ∃x (x ∈ a ∧ ∀y (y ∈ a → ¬(y ∈ x)))) |
| universal | ∃u ∀x (x ∈ u) |
| self-member | ∃s (s ∈ s) |

`zf` has no axiom of choice. Its fixed axioms and schemas are the standard ones, but it is
searched like every other theory: an `UNKNOWN` says nothing about the consistency of ZF.

## Built-in schemas

A schema instance is given by a condition φ, a source formula whose free variables are the
schema's main variables and any number of parameters. The instance is closed by quantifying
the parameters universally. The meaning of each instance, as defined in Rocq
(`schema_meaning` in `rocq/Source/Language.v`):

| Schema | Main variables | Instance |
| --- | --- | --- |
| comprehension | x | ∃r ∀x (x ∈ r ↔ φ(x)) |
| separation | x | ∀s ∃r ∀x (x ∈ r ↔ (x ∈ s ∧ φ(x))) |
| replacement | x, y | (∀x ∃y (φ(x, y) ∧ ∀z (φ(x, z) → z = y))) → ∀s ∃r ∀y (y ∈ r ↔ ∃x (x ∈ s ∧ φ(x, y))) |
| unrestricted separation | x | ∃r ∀x (x ∈ r ↔ φ(x)): separation with its bounding set removed, a deliberate mutation |

In the source syntax, the main variables are `Free 0` (and `Free 1` for replacement); parameters
are the free variables after them. The bound names `s` and `r` and replacement's uniqueness
variable are chosen fresh. Replacement keeps the functionality premise as part of the axiom; the
search never discharges it by a meta-level judgement.

The checker does not trust the generator: it rebuilds each instance from its condition with code
extracted from `rocq/Source/Language.v`, where the expansion is proved to mean the formula
above.

## Example theories in `theories/`

| File | Content |
| --- | --- |
| `naive-set/russell.p` | The Russell instance of comprehension as a single FOF axiom, for comparison with external provers |
| `zf/separation-universal.p`, `zf/foundation-self.p` | TPTP renderings of the two built-in theories, with the instances the refutation needs |
| `examples/equality.p` | Equality must be interpreted: `a = b`, `p(f(a))`, `¬p(f(b))` |
| `examples/definitions.p`, `examples/equality-factoring.p`, `examples/backward-demodulation.p` | Small problems whose proofs exercise definitional CNF, equality factoring and backward demodulation (`@rocq` checks that they still do) |
| `examples/satisfiable.p` | A satisfiable problem: the answer is `UNKNOWN` |

The built-in theories are not read from these files: `axiom-fuzz --theory` builds them in OCaml and
enumerates the schema instances itself.

## TPTP input

`axiom-fuzz --problem` and `axiom-replay --problem` read single-sorted, uninterpreted first-order
TPTP:

- `fof(...)` and `cnf(...)` formulas;
- variables, constants, functions, predicates, `=` and `!=`;
- `~`, `&`, `|`, `=>`, `<=`, `<=>`, `<~>`, `~&`, `~|`, `![X,...]:`, `?[X,...]:`, `$true`,
  `$false`;
- single-quoted symbols, `%` and `/* ... */` comments;
- the roles `axiom`, `hypothesis`, `definition`, `assumption` and `negated_conjecture`.

Rejected with an error, never reinterpreted: `include`, TFF and THF, arithmetic, distinct
objects, the same symbol with two arities, source and useful-info annotations, the role
`conjecture` (supply the conjecture already negated, as `negated_conjecture`), free variables in
FOF, and unparenthesized mixtures of different binary connectives. Terms and formulas nest at
most 256 levels, and files are at most 32 MiB.

Most TPTP problems use `include`. Expand the included axiom files into the problem first, without
any other change; `benchmarks/corpus.py` does this for the benchmark suites and records the hashes.

Roles never reach the manifest or the certificate. The ported E heuristics use the
`negated_conjecture` symbols as a hint for clause selection; the proof and its check do not
depend on roles.

## Using the OCaml library

The library is public: theories with custom schemas, parameter types or enumerators can only be
built through it. Its module is `Axiom_fuzzer` and its findlib name is `axiom-fuzzer`:

```lisp
; dune
(executable
 (name my_theory)
 (libraries axiom-fuzzer))
```

Inside this repository, the library name is `axiom_fuzzer`. Outside it, install the package first
(`opam install .`, or `opam pin add axiom-fuzzer .`).

### API scope and stability

The library is an unstable 0.x API: the entry points below may change in any 0.x release, and
everything else in it is internal and may change without notice.

| Module | Entry points |
| --- | --- |
| `Theory` | `create` (built-in theories), `custom` (fixed axioms), `Schema.create` and `register_schema` (custom schemas), `of_enumerator` (enumerated theories), `of_definitions`, `copy`, `instantiate_schema`, `instantiate_enumerated`, `validate_axiom`, `name` |
| `Definitions` | `create`, `predicate`, `function_`, `expand`, `signature`, `base_signature` |
| `Kernel` | `check` (the final decision), `rocq_document` (the `--rocq` export) |
| `Certificate_io` | `read`, `write`, `encode` |
| `Tptp` | `parse`, `parse_annotated`, `load`, `problem`, `cnf_problem`, `tstp` |
| `Wire` | the types of source formulas (`Pred`, `Eq`, `Neg`, `App`, `F`, ...), axioms, steps and certificates |
| `Signature`, `Source` | building signatures (`Signature.make`, `Signature.unrestricted`) and, inside a schema's `expand`, source formulas (`Source.apply`, `Source.pred`, ...) |
| `Scheduler` | `run` and `default_config`, to run a search from OCaml |

The examples below use only these entry points. They compile and run against 0.1.0.

### Definitions

`Definitions` is an immutable environment of transparent abbreviations for predicates and
functions. `Theory.of_definitions` expands them into the base language before the theory is
built, so certificates, manifests and Rocq proofs contain only base symbols.

```ocaml
open Axiom_fuzzer
open Wire

let base = Signature.make ~functions:[ ("z", 0); ("s", 1) ] ~predicates:[ ("p", 1) ]
let definitions =
  Definitions.function_ (Definitions.create base) ~name:"twice" ~arity:1
    (App ("s", [ App ("s", [ F 0 ]) ]))
let definitions =
  Definitions.predicate definitions ~name:"holds" ~arity:1
    (Pred ("p", [ App ("twice", [ F 0 ]) ]))
let theory =
  Theory.of_definitions ~name:"definitions-example" definitions
    [
      ("positive", Pred ("holds", [ App ("z", []) ]));
      ("negative", Neg (Pred ("p", [ App ("s", [ App ("s", [ App ("z", []) ]) ]) ])));
    ]

let () = print_endline (Theory.name theory)
```

`holds(z)` expands to `p(s(s(z)))`. Parameters are the free variables `F 0` to `F (arity-1)`;
expansion substitutes them simultaneously and shifts bound variables to avoid capture. A
definition may use only base symbols and earlier definitions, so cycles, recursion and forward
references are impossible; unknown symbols, wrong arities and out-of-range parameters are
rejected. The base signature must be finite (`Signature.unrestricted` is refused). `?budget`
(default 100,000 traversal steps) bounds every expansion. The expansion itself is not
formalized in Rocq; what is checked is the expanded theory.

### A recursively enumerated theory

`Theory.of_enumerator ~name ~revision ~step` takes `step : int -> Wire.source option`. `step n`
must terminate; it returns `Some f` if stage `n` emits the axiom `f`, and `None` otherwise. Every
axiom must appear at some finite stage. Membership need not be decidable: an empty theory,
repeated axioms and arbitrarily long silent stretches are fine. Do not wait for the next axiom
inside one `step` call; simulate a fixed number of steps of your generator instead.

```ocaml
open Axiom_fuzzer

let p = Wire.Pred ("predicate_0", [ Wire.App ("constant_0", []) ])

let theory =
  Theory.of_enumerator ~name:"enumerated-example" ~revision:"current"
    ~step:(function
      | 2 -> Some p
      | 7 -> Some (Wire.Neg p)
      | n when n mod 4 = 3 -> Some (Wire.Pred ("predicate_" ^ string_of_int n, []))
      | _ -> None)

let () =
  let config = { Scheduler.default_config with max_size = 8; reference = false } in
  let result = Scheduler.run config theory in
  match result.certificate with
  | None -> print_endline "UNKNOWN"
  | Some cert ->
      match Kernel.check (Theory.copy theory) cert with
      | Error message -> failwith message
      | Ok _ -> Certificate_io.write "enumerated.cert" cert
```

The symbols come from `Signature.unrestricted`: any name with any finite arity. The certificate
records the stage of each axiom; the checker re-runs that stage and compares the formula. The
Rocq theorems connect the enumerated axioms to standard natural deduction and to the reference
search (`enumeration_check_iff`, `enumeration_eventually_found`); the heuristic search itself
has no completeness guarantee.

### Registering a schema

`Theory.Schema.create` defines a schema with any parameter type; `Theory.register_schema` adds it
to one theory (there is no global registry). This example makes `p(sⁿ(z))` an axiom for every
natural number `n`, next to the fixed axiom `¬p(s(s(z)))`:

```ocaml
open Axiom_fuzzer

let signature =
  Signature.make ~functions:[ ("z", 0); ("s", 1) ] ~predicates:[ ("p", 1) ]

let numerals =
  Theory.Schema.create ~name:"numerals" ~revision:"1"
    ~encode:string_of_int
    ~decode:(fun text ->
      match int_of_string_opt text with Some n when n >= 0 -> Some n | _ -> None)
    ~enumerate:(fun _ bounds ->
      match bounds with
      | None -> Seq.ints 0
      | Some (b : Theory.Schema.bounds) -> List.init b.max_size Fun.id |> List.to_seq)
    ~expand:(fun arena n ->
      let rec term n =
        if n = 0 then Source.apply arena "z" []
        else Source.apply arena "s" [ term (n - 1) ]
      in
      Source.pred arena "p" [ term n ])
    ~check:(fun _ n formula ->
      let rec matches n = function
        | Wire.App ("z", []) -> n = 0
        | Wire.App ("s", [ t ]) when n > 0 -> matches (n - 1) t
        | _ -> false
      in
      match formula with Wire.Pred ("p", [ t ]) -> matches n t | _ -> false)
    ()

let theory =
  let open Wire in
  let counterexample = Neg (Pred ("p", [ App ("s", [ App ("s", [ App ("z", []) ]) ]) ])) in
  Theory.custom ~name:"numeral-example" signature [ ("counterexample", counterexample) ]
  |> fun t -> Theory.register_schema t numerals

let () =
  let config = { Scheduler.default_config with max_size = 3; reference = false } in
  let result = Scheduler.run config theory in
  match result.certificate with
  | None -> print_endline "UNKNOWN"
  | Some certificate ->
      (match Kernel.check (Theory.copy theory) certificate with
      | Error message -> failwith message
      | Ok _ -> Certificate_io.write "numerals.cert" certificate)
```

The contract of a registered schema:

- **Name and revision.** Empty names, two schemas of the same name in one theory and the names
  of built-in schemas are refused. Change `revision` whenever the meaning, the codec or the
  enumeration order changes; nothing detects a changed implementation for you.
- **Codec.** `decode` returns `None` for an invalid parameter, and re-encoding must give back the
  same string (do not accept both `2` and `02`).
- **Expansion.** `expand` builds a closed source formula in the arena it is given; formulas from
  another arena, unknown symbols and open formulas are refused.
- **Checker.** `check` validates the parameter and the stored raw axiom on its own; do not call
  `expand` from it. The common boundary also checks the axiom ID, name, revision, scope, closure
  and signature.
- **State.** Parameters and the schema definition are immutable; callbacks must not share
  mutable state across Domains. Use `Theory.copy` for each worker.
- **Enumeration.** `enumerate signature None` must yield every parameter, one step at a time,
  each in finite time (`None` in the sequence is a silent step). A long computation inside one
  step should call `Enumerate.poll ()` so that time limits and cancellation can interrupt it.
- **Guidance.** The optional `guide` turns formulas found during the search into parameters.

`check` is part of the theory definition and therefore trusted: registering a schema does not
produce a Rocq proof of it, and the soundness theorems treat the set of formulas it accepts as
the schema's axioms. `Kernel.rocq_document` still exports a Rocq refutation of the finite set of
expanded instances that a certificate uses. `axiom-replay` cannot rebuild a theory with a
registered schema, because the callback is OCaml code: re-check such certificates with a program
that registers the same schema and calls `Certificate_io.read` and `Kernel.check`.

The reference enumeration enumerates parameter strings and permits directly, so its
completeness does not depend on `enumerate` being exhaustive.
