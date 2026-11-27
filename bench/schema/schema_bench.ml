(* Benchmark of schema-dependent contradictions (standing regression suite).

   Every case is an inconsistent recursively axiomatized theory whose refutation
   needs at least one schema instance. Cases are encoded with the public APIs:
   built-in theories, Theory.custom + Theory.register_schema, and
   Theory.of_enumerator. Every reported UNSAT is re-checked here with
   Kernel.check on a fresh copy of the theory after a certificate
   encode/decode roundtrip.

   Registering a case: add a [case] record to [cases] (or to a list that
   [all_cases] concatenates). [witness] lists the human proof's instances as
   (schema name, condition) pairs; [schema_bench witness CASE] validates them
   (the schema's own check accepts each instance, and the fixed axioms plus
   exactly these instances are refuted by a plain FO run). The scripts in
   scripts/ read the case list from [schema_bench list]. *)

open Axiom_fuzzer

(* ---------- named syntax, converted to De Bruijn Wire.source ---------- *)

type nt = V of string | A of string * nt list

type nf =
  | Top
  | Bot
  | Mem of nt * nt
  | P of string * nt list
  | Eq of nt * nt
  | Not of nf
  | And of nf list
  | Or of nf list
  | Imp of nf * nf
  | Iff of nf * nf
  | All of string list * nf
  | Ex of string list * nf

let index x l =
  let rec go i = function [] -> None | y :: r -> if y = x then Some i else go (i + 1) r in
  go 0 l

let rec wterm free env = function
  | V x -> (
      match index x env with
      | Some i -> Wire.B i
      | None -> (
          match index x free with Some i -> Wire.F i | None -> failwith ("unbound variable " ^ x)))
  | A (s, ts) -> Wire.App (s, List.map (wterm free env) ts)

let rec wf free env f : Wire.source =
  match f with
  | Top -> Wire.Top
  | Bot -> Wire.Bot
  | Mem (x, y) -> Wire.Pred ("member", [ wterm free env x; wterm free env y ])
  | P (s, ts) -> Wire.Pred (s, List.map (wterm free env) ts)
  | Eq (x, y) -> Wire.Eq (wterm free env x, wterm free env y)
  | Not f -> Wire.Neg (wf free env f)
  | And fs -> Wire.Conj (List.map (wf free env) fs)
  | Or fs -> Wire.Disj (List.map (wf free env) fs)
  | Imp (f, g) -> Wire.Disj [ Wire.Neg (wf free env f); wf free env g ]
  | Iff (f, g) ->
      let a = wf free env f and b = wf free env g in
      Wire.Conj [ Wire.Disj [ Wire.Neg a; b ]; Wire.Disj [ Wire.Neg b; a ] ]
  | All (xs, f) ->
      List.fold_left (fun acc _ -> Wire.All acc) (wf free (List.rev_append xs env) f) xs
  | Ex (xs, f) -> List.fold_left (fun acc _ -> Wire.Ex acc) (wf free (List.rev_append xs env) f) xs

let closed f = wf [] [] f
let mem a b = Mem (V a, V b)

(* ---------- printing ---------- *)

let rec pp_term env = function
  | Wire.B i -> ( try List.nth env i with _ -> "#" ^ string_of_int i)
  | Wire.F 0 -> "x"
  | Wire.F 1 -> "y"
  | Wire.F i -> "w" ^ string_of_int i
  | Wire.App (s, []) -> s
  | Wire.App (s, ts) -> s ^ "(" ^ String.concat "," (List.map (pp_term env) ts) ^ ")"

let rec pp env = function
  | Wire.Top -> "T"
  | Wire.Bot -> "F"
  | Wire.Pred ("member", [ a; b ]) -> pp_term env a ^ " in " ^ pp_term env b
  | Wire.Pred (s, []) -> s
  | Wire.Pred (s, ts) -> s ^ "(" ^ String.concat "," (List.map (pp_term env) ts) ^ ")"
  | Wire.Eq (a, b) -> pp_term env a ^ " = " ^ pp_term env b
  | Wire.Neg f -> "~(" ^ pp env f ^ ")"
  | Wire.Conj fs -> "(" ^ String.concat " & " (List.map (pp env) fs) ^ ")"
  | Wire.Disj fs -> "(" ^ String.concat " | " (List.map (pp env) fs) ^ ")"
  | Wire.All f ->
      let x = "b" ^ string_of_int (List.length env) in
      "!" ^ x ^ ". " ^ pp (x :: env) f
  | Wire.Ex f ->
      let x = "b" ^ string_of_int (List.length env) in
      "?" ^ x ^ ". " ^ pp (x :: env) f

let pp_source f = pp [] f

(* ---------- schema templates (Source level, mirrors Theory.schema_formula) ---------- *)

type kind =
  | Comp
  | Sep
  | Repl
  | Or_sep  (** mutant: x in b <-> (x in a | phi) *)
  | Filter_sep  (** mutant: x in b <-> (a in x & phi) *)
  | Curry of Wire.source  (** x in b <-> (phi -> q) for a fixed sentence q *)

let arity_of = function Repl -> 2 | _ -> 1

let template kind a phi =
  let arity = arity_of kind in
  let params = List.filter (fun i -> i >= arity) (Source.free_vars a phi) in
  let fresh = List.fold_left max (arity - 1) params + 1 in
  let av = fresh and bv = fresh + 1 in
  let x = Source.free a 0 and y = Source.free a 1 in
  let set = Source.free a av and result = Source.free a bv in
  let m = Source.member a in
  let finish f = Source.all a params f in
  let separation body =
    finish
      (Source.all a [ av ]
         (Source.ex a [ bv ] (Source.all a [ 0 ] (Source.iff a (m x result) body))))
  in
  match kind with
  | Comp -> finish (Source.ex a [ bv ] (Source.all a [ 0 ] (Source.iff a (m x result) phi)))
  | Curry q ->
      let q = Wire.import a q in
      finish
        (Source.ex a [ bv ]
           (Source.all a [ 0 ] (Source.iff a (m x result) (Source.implies a phi q))))
  | Sep -> separation (Source.and_ a [ m x set; phi ])
  | Or_sep -> separation (Source.or_ a [ m x set; phi ])
  | Filter_sep -> separation (Source.and_ a [ m set x; phi ])
  | Repl ->
      let zv = fresh + 2 in
      let z = Source.free a zv in
      let unique =
        Source.all a [ zv ] (Source.implies a (Source.subst_free a 1 z phi) (Source.eq a z y))
      in
      let functional = Source.all a [ 0 ] (Source.ex a [ 1 ] (Source.and_ a [ phi; unique ])) in
      let image =
        Source.all a [ av ]
          (Source.ex a [ bv ]
             (Source.all a [ 1 ]
                (Source.iff a (m y result) (Source.ex a [ 0 ] (Source.and_ a [ m x set; phi ])))))
      in
      finish (Source.implies a functional image)

(* ---------- admissibility predicates on the condition ---------- *)

let admit_any (_ : Wire.source) = true

(* Membership graph over variable occurrences (each binder is a distinct node). *)
let membership_edges f =
  let counter = ref 0 and edges = ref [] and has_eq = ref false and other = ref false in
  let node env = function
    | Wire.B i -> ( try Some (`B (List.nth env i)) with _ -> None)
    | Wire.F i -> Some (`F i)
    | Wire.App _ -> None
  in
  let rec go env = function
    | Wire.Top | Wire.Bot -> ()
    | Wire.Pred ("member", [ s; t ]) -> (
        match (node env s, node env t) with
        | Some u, Some v -> edges := (u, v) :: !edges
        | _ -> other := true)
    | Wire.Pred _ -> other := true
    | Wire.Eq _ -> has_eq := true
    | Wire.Neg f -> go env f
    | Wire.Conj fs | Wire.Disj fs -> List.iter (go env) fs
    | Wire.All f | Wire.Ex f ->
        incr counter;
        go (!counter :: env) f
  in
  go [] f;
  (!edges, !has_eq, !other)

(* No equality, no reflexive atom u in u. *)
let admit_irreflexive f =
  let edges, has_eq, _ = membership_edges f in
  (not has_eq) && List.for_all (fun (u, v) -> u <> v) edges

(* No equality, no membership cycle of length <= 2 among variables. *)
let admit_acyclic2 f =
  let edges, has_eq, _ = membership_edges f in
  (not has_eq) && List.for_all (fun (u, v) -> u <> v && not (List.mem (v, u) edges)) edges

(* No equality, no membership cycle of length <= 3 among variables. *)
let admit_acyclic3 f =
  let edges, has_eq, _ = membership_edges f in
  (not has_eq)
  && List.for_all
       (fun (u, v) ->
         u <> v
         && (not (List.mem (v, u) edges))
         && not (List.exists (fun (v', w) -> v' = v && List.mem (w, u) edges) edges))
       edges

(* ---------- registered schemas with formula parameters ---------- *)

let encode p = Sexp.to_string (Certificate_io.source p)
let decode s = try Some (Certificate_io.decode_source (Sexp.parse s)) with _ -> None

let make_schema ?(revision = "1") ~name kind admissible =
  let arity = arity_of kind in
  let ok p = Wire.source_scoped p && admissible p in
  Theory.Schema.create ~name ~revision
    ~guide:(fun a phi ->
      let p = Wire.export a phi in
      if ok p then Some p else None)
    ~encode ~decode
    ~enumerate:(fun sg bounds ->
      let a = Source.create sg in
      let seq =
        match bounds with
        | None -> Enumerate.exhaustive a ~arity
        | Some (b : Theory.Schema.bounds) ->
            Enumerate.bounded a ~arity ~parameters:b.parameters ~max_size:b.max_size
      in
      Seq.filter_map
        (fun phi ->
          let p = Wire.export a phi in
          if ok p then Some p else None)
        seq)
    ~expand:(fun a p -> template kind a (Wire.import a p))
    ~check:(fun sg p f ->
      ok p
      &&
        try
          let a = Source.create sg in
          Wire.import a f = template kind a (Wire.import a p)
        with _ -> false)
    ()

let sep () = make_schema ~name:"sep" Sep admit_any
let repl () = make_schema ~name:"repl" Repl admit_any

let custom name sg axioms schemas =
  let t = Theory.custom ~name sg (List.map (fun (n, f) -> (n, closed f)) axioms) in
  List.fold_left Theory.register_schema t schemas

(* ---------- fixed axioms ---------- *)

let ax_pairing =
  All
    ( [ "a"; "b" ],
      Ex ([ "c" ], All ([ "z" ], Iff (mem "z" "c", Or [ Eq (V "z", V "a"); Eq (V "z", V "b") ]))) )

let ax_union =
  All
    ( [ "a" ],
      Ex ([ "u" ], All ([ "z" ], Iff (mem "z" "u", Ex ([ "y" ], And [ mem "y" "a"; mem "z" "y" ]))))
    )

let ax_empty = Ex ([ "e" ], All ([ "x" ], Not (mem "x" "e")))

let ax_foundation =
  All
    ( [ "a" ],
      Imp
        ( Ex ([ "y" ], mem "y" "a"),
          Ex ([ "y" ], And [ mem "y" "a"; All ([ "z" ], Imp (mem "z" "a", Not (mem "z" "y"))) ]) )
    )

let ax_complement = All ([ "a" ], Ex ([ "b" ], All ([ "x" ], Iff (mem "x" "b", Not (mem "x" "a")))))

let ax_subset_closed =
  Ex ([ "u" ], All ([ "y" ], Imp (All ([ "z" ], Imp (mem "z" "y", mem "z" "u")), mem "y" "u")))

let subset_of_a y = All ([ "z" ], Imp (Mem (V "z", V y), Mem (V "z", A ("a", []))))

let ax_surj_f =
  All
    ( [ "y" ],
      Imp
        ( subset_of_a "y",
          Ex ([ "x" ], And [ Mem (V "x", A ("a", [])); Eq (A ("f", [ V "x" ]), V "y") ]) ) )

let ax_functional_r =
  All
    ( [ "x"; "y"; "z" ],
      Imp (And [ P ("r", [ V "x"; V "y" ]); P ("r", [ V "x"; V "z" ]) ], Eq (V "y", V "z")) )

let ax_surj_r =
  All
    ( [ "y" ],
      Imp
        (subset_of_a "y", Ex ([ "x" ], And [ Mem (V "x", A ("a", [])); P ("r", [ V "x"; V "y" ]) ]))
    )

let ax_singletons =
  Ex
    ( [ "s" ],
      All
        ( [ "x" ],
          Iff (mem "x" "s", Ex ([ "y" ], All ([ "z" ], Iff (mem "z" "x", Eq (V "z", V "y"))))) ) )

let ax_onto_g =
  All ([ "y" ], Ex ([ "x" ], And [ Mem (V "x", A ("a", [])); Eq (A ("g", [ V "x" ]), V "y") ]))

let ax_no_universal = All ([ "z" ], Ex ([ "w" ], Not (mem "w" "z")))
let q_universal = closed (Ex ([ "z" ], All ([ "w" ], mem "w" "z")))

(* g maps every subset of a into a, and g is injective (no injection P(a) -> a). *)
let ax_into_g = All ([ "y" ], Imp (subset_of_a "y", Mem (A ("g", [ V "y" ]), A ("a", []))))

let ax_injective_g =
  All ([ "y"; "z" ], Imp (Eq (A ("g", [ V "y" ]), A ("g", [ V "z" ])), Eq (V "y", V "z")))

(* ZF power set with the inner universal quantifier mutated to an existential. *)
let ax_power_exists =
  All
    ( [ "a" ],
      Ex ([ "b" ], All ([ "x" ], Iff (mem "x" "b", Ex ([ "y" ], Imp (mem "y" "x", mem "y" "a")))))
    )

(* ---------- enumerated theory (Theory.of_enumerator) ---------- *)

(* Domain-local memo of the n-th admissible comprehension instance; deterministic and
   never shared between Domains. *)
let enumerated_comprehension ~name admissible =
  let key =
    Domain.DLS.new_key (fun () ->
        let a = Source.create Signature.sets in
        let seq = ref (Enumerate.exhaustive a ~arity:1) in
        (a, seq, Dynarray.create ()))
  in
  let step n =
    let a, seq, memo = Domain.DLS.get key in
    let rec fill () =
      if Dynarray.length memo <= n then
        match !seq () with
        | Seq.Nil -> ()
        | Seq.Cons (phi, rest) ->
            seq := rest;
            let p = Wire.export a phi in
            Dynarray.add_last memo
              (if admissible p then Some (Wire.export a (template Comp a phi)) else None);
            fill ()
    in
    fill ();
    if n < Dynarray.length memo then Dynarray.get memo n else None
  in
  Theory.of_enumerator ~name ~revision:"1" ~step

(* ---------- cases ---------- *)

type case = {
  name : string;
  needed : string;
  build : unit -> Theory.t;
  witness : (string * nf) list;
}

let sg_f = Signature.make ~functions:[ ("f", 1); ("a", 0) ] ~predicates:[ ("member", 2) ]
let sg_r = Signature.make ~functions:[ ("a", 0) ] ~predicates:[ ("member", 2); ("r", 2) ]
let sg_g = Signature.make ~functions:[ ("g", 1); ("a", 0) ] ~predicates:[ ("member", 2) ]

let zf_fixed () =
  Theory.fixed (Theory.create "zf") |> List.map (fun (ax : Wire.axiom) -> (ax.name, ax.formula))

let custom_wire name sg axioms schemas =
  let t = Theory.custom ~name sg axioms in
  List.fold_left Theory.register_schema t schemas

let cases =
  [
    {
      witness = [ ("comprehension", Not (mem "x" "x")) ];
      name = "naive";
      needed = "comprehension(~x in x)";
      build = (fun () -> Theory.create "naive");
    };
    {
      witness = [ ("separation", Not (mem "x" "x")) ];
      name = "separation-universal";
      needed = "separation(~x in x)";
      build = (fun () -> Theory.create "separation-universal");
    };
    {
      witness = [ ("unrestricted-separation", Not (mem "x" "x")) ];
      name = "mutated-separation";
      needed = "unrestricted-separation(~x in x)";
      build = (fun () -> Theory.create "mutated-separation");
    };
    {
      witness = [ ("sep", Bot); ("sep", Not (mem "x" "x")) ];
      name = "complement-sep";
      needed = "sep(F) or sep(~x in w) [empty set], then sep(~x in x) on its complement";
      build =
        (fun () ->
          custom "b-complement-sep" Signature.sets [ ("complement", ax_complement) ] [ sep () ]);
    };
    {
      witness = [ ("sep", Not (mem "x" "x")) ];
      name = "subset-closed-sep";
      needed = "sep(~x in x) on u, then R subset u gives R in u";
      build =
        (fun () ->
          custom "b-subset-closed" Signature.sets [ ("subset_closed", ax_subset_closed) ] [ sep () ]);
    };
    {
      witness = [ ("sep", Not (Mem (V "x", A ("f", [ V "x" ])))) ];
      name = "cantor-function";
      needed = "sep(~x in f(x)) on a (Cantor diagonal)";
      build = (fun () -> custom "b-cantor-function" sg_f [ ("surjection", ax_surj_f) ] [ sep () ]);
    };
    {
      witness = [ ("sep", Ex ([ "y1" ], And [ P ("r", [ V "x"; V "y1" ]); Not (mem "x" "y1") ])) ];
      name = "cantor-relation";
      needed = "sep(?y.(r(x,y) & ~x in y)) or sep(!y.(r(x,y) -> ~x in y)) on a";
      build =
        (fun () ->
          custom "b-cantor-relation" sg_r
            [ ("functional", ax_functional_r); ("surjection", ax_surj_r) ]
            [ sep () ]);
    };
    {
      witness = [ ("comp-irrefl", Not (Ex ([ "y1" ], And [ mem "x" "y1"; mem "y1" "x" ]))) ];
      name = "russell-2cycle";
      needed = "comp-irrefl(~?y.(x in y & y in x))  [size 5]";
      build =
        (fun () ->
          custom "b-russell-2cycle" Signature.sets []
            [ make_schema ~name:"comp-irrefl" Comp admit_irreflexive ]);
    };
    {
      witness =
        [
          ( "comp-acyclic2",
            Not (Ex ([ "y1"; "z1" ], And [ mem "x" "y1"; mem "y1" "z1"; mem "z1" "x" ])) );
        ];
      name = "russell-3cycle";
      needed = "comp-acyclic2(~?y z.(x in y & y in z & z in x))  [size 7]";
      build =
        (fun () ->
          custom "b-russell-3cycle" Signature.sets []
            [ make_schema ~name:"comp-acyclic2" Comp admit_acyclic2 ]);
    };
    {
      witness = [ ("sep", Not (mem "x" "x")) ];
      name = "singletons-union";
      needed = "sep(~x in x) on union of the set of all singletons (universal)";
      build =
        (fun () ->
          custom "b-singletons-union" Signature.sets
            [ ("pairing", ax_pairing); ("union", ax_union); ("singletons", ax_singletons) ]
            [ sep () ]);
    };
    {
      witness = [ ("repl", Eq (V "y", A ("g", [ V "x" ]))); ("sep", Not (mem "x" "x")) ];
      name = "replacement-onto";
      needed = "repl(y = g(x)) on a (image is universal), then sep(~x in x)";
      build =
        (fun () -> custom "b-replacement-onto" sg_g [ ("onto", ax_onto_g) ] [ repl (); sep () ]);
    };
    {
      witness = [ ("curry", mem "x" "x") ];
      name = "curry";
      needed = "curry(x in x): C = {x | x in x -> ?z!w. w in z}";
      build =
        (fun () ->
          custom "b-curry" Signature.sets
            [ ("no_universal", ax_no_universal) ]
            [ make_schema ~name:"curry" (Curry q_universal) admit_any ]);
    };
    {
      witness = [ ("or-sep", Not (mem "x" "x")) ];
      name = "or-sep-empty";
      needed = "or-sep(~x in x) on the empty set";
      build =
        (fun () ->
          custom "b-or-sep-empty" Signature.sets
            [ ("empty", ax_empty) ]
            [ make_schema ~name:"or-sep" Or_sep admit_any ]);
    };
    {
      witness = [ ("filter-sep", Top) ];
      name = "filter-sep-zf";
      needed = "filter-sep(T): {x | a in x}; its union is universal; foundation on {V}";
      build =
        (fun () ->
          custom "b-filter-sep" Signature.sets
            [ ("pairing", ax_pairing); ("union", ax_union); ("foundation", ax_foundation) ]
            [ make_schema ~name:"filter-sep" Filter_sep admit_any ]);
    };
    {
      witness = [ ("sep", Not (mem "x" "x")) ];
      name = "zf-power-exists";
      needed = "sep(~x in x) on the mutated power set P'(a) = {x | ?y.(y in x -> y in a)}";
      build =
        (fun () ->
          let fixed =
            List.map
              (fun (n, f) -> if n = "power" then (n, closed ax_power_exists) else (n, f))
              (zf_fixed ())
          in
          custom_wire "b-zf-power-exists" Signature.sets fixed [ sep (); repl () ]);
    };
    {
      witness = [];
      name = "enumerated-naive";
      needed = "stage of comprehension(~x in x)";
      build = (fun () -> enumerated_comprehension ~name:"b-enumerated-naive" admit_any);
    };
    {
      witness = [];
      name = "enumerated-2cycle";
      needed = "stage of comprehension(~?y.(x in y & y in x)) among irreflexive conditions";
      build = (fun () -> enumerated_comprehension ~name:"b-enumerated-2cycle" admit_irreflexive);
    };
  ]

(* Held-out cases written by the M06 skeptic (not by the prototype author). *)
let skeptic_cases =
  [
    {
      witness =
        [
          ( "comp-acyclic3",
            Not
              (Ex
                 ( [ "y1"; "z1"; "u1" ],
                   And [ mem "x" "y1"; mem "y1" "z1"; mem "z1" "u1"; mem "u1" "x" ] )) );
        ];
      name = "russell-4cycle";
      needed =
        "comp-acyclic3(~?y z u.(x in y & y in z & z in u & u in x))  [size 9; skeptic held-out]";
      build =
        (fun () ->
          custom "b-russell-4cycle" Signature.sets []
            [ make_schema ~name:"comp-acyclic3" Comp admit_acyclic3 ]);
    };
    {
      witness =
        [ ("sep", Ex ([ "y1" ], And [ Eq (A ("g", [ V "y1" ]), V "x"); Not (mem "x" "y1") ])) ];
      name = "cantor-injection";
      needed = "sep(?y.(g(y) = x & ~x in y)) on a (no injection P(a) -> a; skeptic held-out)";
      build =
        (fun () ->
          custom "b-cantor-injection" sg_g
            [ ("into", ax_into_g); ("injective", ax_injective_g) ]
            [ sep () ]);
    };
  ]

(* Independent test set (independent.ml, written by an author other than the
   prototype's and the lane's): run/list/snapshot by name here; witnesses live
   there. *)
let independent_cases =
  List.map
    (fun (c : Independent.case) ->
      { name = c.name; needed = c.needed; build = c.build; witness = [] })
    Independent.all

let all_cases = cases @ skeptic_cases @ independent_cases

(* ---------- running ---------- *)

let parameter_text (ax : Wire.axiom) =
  match ax.origin with
  | Wire.Instance (_, phi) -> Some (pp_source phi)
  | Wire.Registered_instance (name, _, data) when name = Natural_checker.enumeration_name ->
      Some ("stage " ^ data)
  | Wire.Registered_instance (_, _, data) -> (
      match decode data with Some p -> Some (pp_source p) | None -> Some data)
  | _ -> None

(* Probe-lane configuration for this process (flags --lane PRESET and
   --lane-... overrides); the default is the library default used by axiom-fuzz
   (Probe_lane.default: no condition prior). *)
let lane = ref Scheduler.default_config.lane

(* The experimental Lawvere-style diagonal prior (lawvere.ml), handed to the
   lane through its generic [prior] hook by the *-diag presets only; its
   grammar bounds are bench flags, read when a lane is created. *)
let prior_length = ref 4
let prior_equality = ref true
let prior_binary = ref true

let lawvere_prior : Probe_lane.prior =
 fun sg ->
  Lawvere.diagonals ~max_length:!prior_length ~equality:!prior_equality ~binary:!prior_binary sg

(* pool-diag reproduces the lane's first default (arrival order, pool, Lawvere
   prior); default-diag adds the prior to the current default; breadth is the
   default without the observational source. *)
let lane_presets =
  [
    ("off", Probe_lane.disabled);
    ("fifo", Probe_lane.fifo);
    ("fixed", Probe_lane.fixed_escalate);
    ("pool", Probe_lane.with_pool);
    ("pool-diag", { Probe_lane.with_pool with prior = Some lawvere_prior });
    ("fixed-diag", { Probe_lane.fixed_escalate with prior = Some lawvere_prior });
    ("default-diag", { Probe_lane.default with prior = Some lawvere_prior });
    (* The previous default: the default without the observational source, at the phase-5
       clock rate (main_weight 1; the ladder keeps it). *)
    ("breadth", Probe_lane.with_breadth);
    (* The phase-6 evaluation candidate: re-probes of non-killers and SAT finite models. *)
    ("candidate", Probe_lane.candidate);
    ("default", Scheduler.default_config.lane);
  ]

let preset name = List.assoc name lane_presets

let config ~seconds ~reference =
  {
    Scheduler.default_config with
    engine =
      {
        Engine.default_config with
        limits = { max_given = max_int; max_generated = max_int; max_retained = max_int; seconds };
      };
    reference;
    reference_config =
      { Scheduler.default_config.reference_config with seconds; max_trials = max_int };
    lane = !lane;
    (* The bench measures the schema lane: a single worker never runs the CLI's time share,
       also on the no-schema mutant controls. *)
    slices = Some Slices.off;
  }

let run_theory ?(quiet = true) ?(cert_path = "") ?(rocq_path = "") ~seconds ~workers ~reference
    label theory =
  let t0 = Unix.gettimeofday () in
  let available = ref true in
  let make_theory () =
    if !available then (
      available := false;
      theory)
    else Theory.copy ~preserve_arena:true theory
  in
  let on_instance (tr : Scheduler.trace) =
    if not quiet then
      Printf.printf "[%d] %s%s: %s\n%!" tr.axiom.axiom_id
        (match tr.generator with Exhaustive -> "" | Guided -> "guided ")
        tr.axiom.name
        (Option.value ~default:tr.predicate (parameter_text tr.axiom))
  in
  let result = Scheduler.portfolio ~workers ~on_instance (config ~seconds ~reference) make_theory in
  let t1 = Unix.gettimeofday () in
  match result.certificate with
  | None ->
      Printf.printf "case=%s result=UNKNOWN seconds=%.3f reason=%s\n%!" label (t1 -. t0)
        result.reason;
      false
  | Some cert -> (
      let decoded = Certificate_io.decode (Certificate_io.encode cert) in
      match Kernel.check (Theory.copy theory) decoded with
      | Error e ->
          Printf.printf "case=%s result=REJECTED seconds=%.3f error=%s\n%!" label (t1 -. t0) e;
          false
      | Ok _ ->
          let t2 = Unix.gettimeofday () in
          if cert_path <> "" then Certificate_io.write cert_path cert;
          (* Audit output: the refutation of the finite Source axiom set the
             certificate uses, checkable by Rocq itself. *)
          (if rocq_path <> "" then
             match Kernel.rocq_document (Theory.copy theory) decoded with
             | Ok text -> Sexp.write_file rocq_path text
             | Error e -> Printf.printf "rocq export failed: %s\n%!" e);
          let instances = List.filter_map parameter_text cert.axioms in
          Printf.printf
            "case=%s result=UNSAT seconds=%.3f check_seconds=%.3f source=%s reason=%s axioms=%s \
             instances=[%s]\n\
             %!"
            label (t1 -. t0) (t2 -. t1) result.proof_source
            (String.map (fun c -> if c = ' ' then '_' else c) result.reason)
            (String.concat "," (List.map (fun (a : Wire.axiom) -> a.name) cert.axioms))
            (String.concat "; " instances);
          true)

let find_case name =
  match List.find_opt (fun c -> c.name = name) all_cases with
  | Some c -> c
  | None -> failwith ("unknown case " ^ name)

(* Validate a case's human-proof instances: authority (validate_axiom) and FO
   refutability of fixed axioms + exactly these instances, without schemas. *)
let witness ~seconds ~tptp_out c =
  let t = c.build () in
  let a = Theory.arena t in
  let next = ref (List.length (Theory.fixed t)) in
  let instances =
    List.map
      (fun (schema_name, f) ->
        let schema =
          match List.find_opt (fun k -> Wire.schema_name k = schema_name) (Theory.schemas t) with
          | Some k -> k
          | None -> failwith ("no schema " ^ schema_name)
        in
        let phi = Wire.import a (wf [ "x"; "y"; "w"; "w2" ] [] f) in
        let p =
          match Theory.guided_parameter t schema phi with
          | Some p -> p
          | None -> failwith ("inadmissible witness for " ^ schema_name)
        in
        let ax = Theory.instantiate_parameter t ~id:!next schema p in
        incr next;
        if not (Theory.validate_axiom t ax) then
          failwith ("witness rejected by schema check: " ^ ax.name);
        Printf.printf "witness %s := %s  (validated)\n%!" ax.name
          (Option.value ~default:"?" (parameter_text ax));
        (ax.name, ax.formula))
      c.witness
  in
  let fixed = List.map (fun (ax : Wire.axiom) -> (ax.name, ax.formula)) (Theory.fixed t) in
  let fo = Theory.custom ~name:("witness-" ^ c.name) (Source.signature a) (fixed @ instances) in
  (* --tptp-out FILE writes the witness theory as a TPTP problem instead of searching it. *)
  if tptp_out <> "" then Sexp.write_file tptp_out (Tptp.problem (Theory.fixed fo))
  else ignore (run_theory ~seconds ~workers:1 ~reference:false ("witness-" ^ c.name) fo)

(* ZF fixed-axiom mutants that keep the separation and replacement schemas. *)
let mutants ~seconds ~start ~limit ~schemas ~reference =
  let fixed = zf_fixed () in
  let all =
    List.concat
      (List.mapi
         (fun k (name, f) ->
           Mutation.mutations f |> List.of_seq
           |> List.map (fun (c : Mutation.change) -> (k, name, c)))
         fixed)
  in
  Printf.printf "total mutants=%d\n%!" (List.length all);
  List.iteri
    (fun i (k, name, (c : Mutation.change)) ->
      if i >= start && i < start + limit then (
        let axioms = List.mapi (fun j (n, f) -> if j = k then (n, c.formula) else (n, f)) fixed in
        let t =
          custom_wire (Printf.sprintf "zf-mutant-%d" i) Signature.sets axioms
            (if schemas then [ sep (); repl () ] else [])
        in
        Printf.printf "mutant=%d axiom=%s operator=%s path=%s formula=%s\n%!" i name c.operator
          (String.concat "." (List.map string_of_int c.path))
          (pp_source c.formula);
        ignore (run_theory ~seconds ~workers:1 ~reference (Printf.sprintf "mutant-%d" i) t)))
    all

(* The observational source's order on a case, stand-alone (no lane, no
   counter-model refinement): the pool the lane builds (same budget), the
   condition classes in discovery order, and every class whose instance is a
   pool killer, probed in isolation (fixed axioms + that instance, one worker,
   [seconds] each, at most [limit] probes). Diagnostic only. *)
let observational ~limit ~seconds c =
  let theory = c.build () in
  let a = Theory.arena theory in
  let sg = Source.signature a in
  let fixed = Theory.fixed theory in
  let t0 = Unix.gettimeofday () in
  let formulas = List.map (fun (ax : Wire.axiom) -> ax.formula) fixed in
  let pool =
    if !lane.mace then Mace.pool ~budget:!lane.pool_budget sg formulas
    else Semantic.pool ~budget:!lane.pool_budget sg formulas
  in
  let rejected = ref 0 in
  Printf.printf "pool: models=%d axioms_used=%d/%d (%.3fs)\n%!" (List.length pool.models)
    pool.axioms_used pool.axioms_total
    (Unix.gettimeofday () -. t0);
  let e = Observational.create ~bucket_cap:!lane.oe_bucket ~word_cap:!lane.oe_words sg pool in
  Printf.printf "levels=%d\n%!" (Observational.levels e);
  let probe_id = List.length fixed in
  let rank = ref 0 and probes = ref 0 and solved = ref false in
  let limit = if limit = max_int then 40 else limit in
  Observational.advance e ~quota:max_int ~emit:(fun form _ ->
      incr rank;
      let w = Observational.condition form in
      (match Wire.import a w with
      | exception Invalid_argument _ -> ()
      | phi ->
          List.iter
            (fun schema ->
              match Theory.guided_parameter theory schema phi with
              | None -> ()
              | Some p -> (
                  match Theory.instantiate_parameter theory ~id:probe_id schema p with
                  | exception Invalid_argument _ -> ()
                  | ax ->
                      let precheck () =
                        (* SEM-MACE: a killer with a small model is dropped unprobed. *)
                        !lane.mace && !lane.mace_precheck > 0
                        &&
                        match
                          Mace.find_model ~budget:!lane.mace_precheck sg pool.active ax.formula
                        with
                        | Some _ ->
                            incr rejected;
                            Printf.printf "rejected %d: rank=%d %s(%s)\n%!" !rejected !rank
                              (Wire.schema_name schema) (pp_source w);
                            true
                        | None -> false
                      in
                      if
                        Semantic.killer pool ax.formula && !probes < limit && (not !solved)
                        && not (precheck ())
                      then (
                        incr probes;
                        Printf.printf
                          "killer %d: rank=%d diagonal=%d size=%d steps=%d at=%.3fs %s(%s)\n%!"
                          !probes !rank (Observational.diagonal e) (Observational.size form)
                          (Observational.steps e)
                          (Unix.gettimeofday () -. t0)
                          (Wire.schema_name schema) (pp_source w);
                        (if !probes = 1 then
                           let m = Semantic.meter () and t1 = Unix.gettimeofday () in
                           let found =
                             Semantic.find_model ~budget:4_000_000 ~meter:m sg pool.active
                               ax.formula
                           in
                           Printf.printf "find_model: %s steps=%d seconds=%.3f (%.1f ns/step)\n%!"
                             (if found = None then "none" else "model")
                             m.steps
                             (Unix.gettimeofday () -. t1)
                             (1e9 *. (Unix.gettimeofday () -. t1) /. float_of_int (max 1 m.steps)));
                        let fo =
                          Theory.custom ~name:"oe-probe" sg
                            (List.map (fun (x : Wire.axiom) -> (x.name, x.formula)) fixed
                            @ [ (ax.name, ax.formula) ])
                        in
                        if run_theory ~seconds ~workers:1 ~reference:false "oe-probe" fo then
                          solved := true)))
            (Theory.schemas theory));
      !solved || !probes >= limit || !rank >= 200_000);
  Printf.printf "rejected=%d\n" !rejected;
  Printf.printf "classes=%d examined=%d kept=%d words=%d steps=%d finished=%b (%.3fs)\n%!" !rank
    (Observational.examined e) (Observational.kept e) (Observational.words e)
    (Observational.steps e) (Observational.finished e)
    (Unix.gettimeofday () -. t0)

(* Fast cases for [dune runtest]: each is solved in milliseconds by the
   default configuration, so a generous wall budget keeps the check robust
   under load while the whole subset takes about a second. The lane-off run
   of [naive] keeps the plain main search covered as well. *)
let smoke_cases =
  [
    ("naive", Probe_lane.disabled);
    ("naive", Scheduler.default_config.lane);
    ("separation-universal", Scheduler.default_config.lane);
    ("mutated-separation", Scheduler.default_config.lane);
    ("subset-closed-sep", Scheduler.default_config.lane);
    ("cantor-function", Scheduler.default_config.lane);
    ("russell-2cycle", Scheduler.default_config.lane);
    ("or-sep-empty", Scheduler.default_config.lane);
    ("enumerated-naive", Scheduler.default_config.lane);
    (* The experimental prior hook stays covered (bench preset only). *)
    ("russell-3cycle", preset "pool-diag");
  ]

let smoke ~seconds =
  let failures =
    List.filter
      (fun (name, l) ->
        lane := l;
        let c = find_case name in
        not (run_theory ~seconds ~workers:1 ~reference:false c.name (c.build ())))
      smoke_cases
  in
  if failures <> [] then (
    Printf.printf "smoke: %d failures: %s\n%!" (List.length failures)
      (String.concat ", " (List.map fst failures));
    exit 1)
  else Printf.printf "smoke: %d/%d UNSAT\n%!" (List.length smoke_cases) (List.length smoke_cases)

(* Slow regression checks (seconds each, not part of [dune runtest]): cases a
   simpler lane preset solved and the default once lost. i-linear-singleton:
   the fifo preset solved it in about 4 s at 10 s / 1 worker, while the
   finite-model pool starved arrival-order probes behind a weak pool's
   killers (0/3 at 10 s before the arrival share and weak-pool demotion).
   russell-3cycle: only the observational source reaches its condition
   (about 1 s at 10 s / 1 worker; the default without it never did). *)
let regression_cases = [ "i-linear-singleton"; "russell-3cycle" ]

let regress ~seconds =
  let failures =
    List.filter
      (fun name ->
        lane := Scheduler.default_config.lane;
        let c = find_case name in
        not (run_theory ~seconds ~workers:1 ~reference:true c.name (c.build ())))
      regression_cases
  in
  if failures <> [] then (
    Printf.printf "regress: %d failures: %s\n%!" (List.length failures)
      (String.concat ", " failures);
    exit 1)
  else
    Printf.printf "regress: %d/%d UNSAT\n%!" (List.length regression_cases)
      (List.length regression_cases)

let usage =
  "usage: schema_bench list | run CASE [--seconds S] [--workers W] [--no-reference] [--verbose] \
   [--certificate F] [--rocq F] [LANE] | witness CASE [--tptp-out F] | snapshot CASE \
   [--observations N] [--out F] | mutants [--seconds S] [--start I] [--limit N] [--no-schemas] \
   [LANE] | smoke [--seconds S] | regress [--seconds S] | diagonals CASE [--limit N] [LANE] | \
   prior-check | count FILTER N | oe CASE [--limit N] [--seconds S] | independent | \
   independent-check | independent-depth CASE [--seconds S] [--limit N]\n\
   LANE: --lane off|fifo|fixed|pool|pool-diag|fixed-diag|default-diag|breadth|candidate|default, \
   then overrides --lane-share F --lane-budget N --lane-fixed-slice N --lane-escalations N \
   --lane-killer-level N --lane-pool-budget N --lane-breadth --lane-no-breadth --lane-shape-cap F \
   --lane-no-oe --lane-oe-share F --lane-diagonal-length K --lane-diagonal-cap N \
   --lane-no-equality --lane-no-binary --lane-no-inject (the diagonal flags only affect the *-diag \
   presets) --lane-set key=value,... (evaluation options, Probe_lane.parse_overrides: \
   clock=alloc|events, main_weight=F, ev_main=F, ev_engine=F, ev_raw=F, luby=F, luby_levels=N, \
   pad=T:A, oe=on|off, share=F)"

let () =
  (* The CLI's measurement switch (Eval): a stopped clock for the scheduling costs makes a bounded
     search depend on its input alone (the time limit still reads the wall clock). The benchmark
     reads no other evaluation switch. *)
  Option.iter (fun clock -> Engine.cost_clock := clock) (Eval.cost_clock Sys.getenv_opt);
  let args = Array.to_list Sys.argv |> List.tl in
  let seconds = ref 10. and workers = ref 1 and reference = ref true and quiet = ref true in
  let cert = ref "" and rocq = ref "" and observations = ref 8 and out = ref "" in
  let tptp_out = ref "" in
  let start = ref 0 and limit = ref max_int and schemas = ref true in
  let set f = lane := f !lane in
  let rec flags = function
    | "--seconds" :: s :: r ->
        seconds := float_of_string s;
        flags r
    | "--workers" :: s :: r ->
        workers := int_of_string s;
        flags r
    | "--no-reference" :: r ->
        reference := false;
        flags r
    | "--verbose" :: r ->
        quiet := false;
        flags r
    | "--certificate" :: s :: r ->
        cert := s;
        flags r
    | "--rocq" :: s :: r ->
        rocq := s;
        flags r
    | "--observations" :: s :: r ->
        observations := int_of_string s;
        flags r
    | "--out" :: s :: r ->
        out := s;
        flags r
    | "--tptp-out" :: s :: r ->
        tptp_out := s;
        flags r
    | "--start" :: s :: r ->
        start := int_of_string s;
        flags r
    | "--limit" :: s :: r ->
        limit := int_of_string s;
        flags r
    | "--no-schemas" :: r ->
        schemas := false;
        flags r
    | "--lane" :: s :: r ->
        (match List.assoc_opt s lane_presets with
        | Some l -> lane := l
        | None -> failwith ("unknown lane preset " ^ s));
        flags r
    | "--lane-share" :: s :: r ->
        set (fun l -> { l with share = float_of_string s });
        flags r
    | "--lane-budget" :: s :: r ->
        set (fun l -> { l with instance_budget = int_of_string s });
        flags r
    | "--lane-fixed-slice" :: s :: r ->
        set (fun l -> { l with fixed_slice = int_of_string s });
        flags r
    | "--lane-killer-level" :: s :: r ->
        set (fun l -> { l with killer_level = int_of_string s });
        flags r
    | "--lane-pool-budget" :: s :: r ->
        set (fun l -> { l with pool_budget = int_of_string s });
        flags r
    | "--lane-escalations" :: s :: r ->
        set (fun l -> { l with escalations = int_of_string s });
        flags r
    | "--lane-breadth" :: r ->
        set (fun l -> { l with breadth = true });
        flags r
    | "--lane-no-breadth" :: r ->
        set (fun l -> { l with breadth = false });
        flags r
    | "--lane-shape-cap" :: s :: r ->
        set (fun l -> { l with shape_cap = float_of_string s });
        flags r
    | "--lane-diagonal-length" :: s :: r ->
        prior_length := int_of_string s;
        flags r
    | "--lane-diagonal-cap" :: s :: r ->
        set (fun l -> { l with prior_cap = int_of_string s });
        flags r
    | "--lane-no-equality" :: r ->
        prior_equality := false;
        flags r
    | "--lane-no-binary" :: r ->
        prior_binary := false;
        flags r
    | "--lane-oe-share" :: f :: r ->
        set (fun l -> { l with oe_share = float_of_string f });
        flags r
    | "--lane-no-oe" :: r ->
        set (fun l -> { l with observational = false });
        flags r
    | "--lane-set" :: text :: r ->
        set (fun l -> Probe_lane.parse_overrides l text);
        flags r
    | "--lane-no-inject" :: r ->
        set (fun l -> { l with inject_failed = false });
        flags r
    | x :: r -> x :: flags r
    | [] -> []
  in
  match flags args with
  | [ "list" ] -> List.iter (fun c -> Printf.printf "%-22s %s\n" c.name c.needed) all_cases
  | [ "run"; name ] ->
      let c = find_case name in
      ignore
        (run_theory ~quiet:!quiet ~cert_path:!cert ~rocq_path:!rocq ~seconds:!seconds
           ~workers:!workers ~reference:!reference c.name (c.build ()))
  | [ "snapshot"; name ] ->
      let c = find_case name in
      let axioms = Mutation.snapshot ~observations:!observations (c.build ()) in
      let text = Tptp.problem axioms in
      if !out = "" then print_string text else Sexp.write_file !out text
  | [ "witness"; name ] when Option.is_some (Independent.find name) ->
      let fo = Independent.witness_theory (Option.get (Independent.find name)) in
      if !tptp_out <> "" then Sexp.write_file !tptp_out (Tptp.problem (Theory.fixed fo))
      else ignore (run_theory ~seconds:!seconds ~workers:1 ~reference:false ("witness-" ^ name) fo)
  | [ "witness"; name ] -> witness ~seconds:!seconds ~tptp_out:!tptp_out (find_case name)
  | [ "smoke" ] -> smoke ~seconds:!seconds
  | [ "prior-check" ] -> Lawvere.check ()
  | [ "oe"; name ] -> observational ~limit:!limit ~seconds:!seconds (find_case name)
  | [ "regress" ] -> regress ~seconds:!seconds
  | [ "diagonals"; name ] ->
      (* The diagonal prior's order for this case: raw index, admitting
         schema and condition (only admissible ones are printed). *)
      let t = (find_case name).build () in
      let a = Theory.arena t in
      let l = !lane in
      let seq = lawvere_prior (Source.signature a) in
      Printf.printf "relations=%d total=%d\n"
        (Lawvere.diagonal_relations ~equality:!prior_equality ~binary:!prior_binary
           (Source.signature a))
        (Lawvere.diagonal_count ~max_length:!prior_length ~equality:!prior_equality
           ~binary:!prior_binary (Source.signature a));
      let admissible = ref 0 in
      Seq.iteri
        (fun i d ->
          if i < l.prior_cap then
            List.iter
              (fun schema ->
                match Theory.guided_parameter t schema (Wire.import a d) with
                | Some _ ->
                    if !admissible < !limit then
                      Printf.printf "%d raw=%d %s %s\n" !admissible i (Wire.schema_name schema)
                        (pp_source d);
                    incr admissible
                | None -> ())
              (Theory.schemas t))
        seq;
      Printf.printf "admissible=%d\n" !admissible
  | [ "count"; filter; limit ] ->
      let limit = int_of_string limit in
      let a = Source.create Signature.sets in
      let ok p =
        match filter with
        | "irrefl" -> admit_irreflexive p
        | "acyclic2" -> admit_acyclic2 p
        | _ -> true
      in
      let targets =
        [
          "~(?b0. (x in b0 & b0 in x))"; "~(?b0. ?b1. (x in b0 & b0 in b1 & b1 in x))"; "~(x in x)";
        ]
      in
      let t0 = Unix.gettimeofday () in
      let rec go i k s last =
        if i >= limit then
          Printf.printf "stopped at raw %d admissible %d (%.1fs)\n" i k (Unix.gettimeofday () -. t0)
        else
          match s () with
          | Seq.Nil -> ()
          | Seq.Cons (phi, rest) ->
              let p = Wire.export a phi in
              let sz = Source.size a phi + (10 * List.length (Source.free_vars a phi)) in
              let last =
                if sz <> last then (
                  Printf.printf "size %d params %d first at raw %d admissible %d (%.1fs)\n%!"
                    (Source.size a phi)
                    (List.length (Source.free_vars a phi))
                    i k
                    (Unix.gettimeofday () -. t0);
                  sz)
                else last
              in
              if ok p then (
                let txt = pp_source p in
                if List.mem txt targets then
                  Printf.printf "TARGET %s at raw %d admissible %d (%.1fs)\n%!" txt i k
                    (Unix.gettimeofday () -. t0);
                go (i + 1) (k + 1) rest last)
              else go (i + 1) k rest last
      in
      go 0 0 (Enumerate.exhaustive a ~arity:1) (-1)
  | [ "mutants" ] ->
      mutants ~seconds:!seconds ~start:!start ~limit:!limit ~schemas:!schemas ~reference:!reference
  | [ "independent" ] -> Independent.print_table ()
  | [ "independent-check" ] -> Independent.check_all ()
  | [ "independent-depth"; name ] -> (
      match Independent.find name with
      | Some c -> Independent.depth ~limit:!limit ~seconds:!seconds c
      | None -> failwith ("unknown independent case " ^ name))
  | _ ->
      prerr_endline usage;
      exit 2
