(* Independent schema-contradiction cases (test set for bench/schema).

   Written from the public Theory / Source / Wire / Enumerate interfaces and the case conventions of
   schema_bench.ml only, without reference to the search code under test, so that the set is not
   tuned to any search. Names start with "i-" and never collide with the original cases.

   Inconsistent cases ([Unsat]) carry a witness: schema conditions (or enumeration stages) whose
   validated instances, together with the fixed axioms, have a first-order refutation. Unless stated
   otherwise the fixed axioms alone are consistent (each record says why). Controls ([Consistent])
   are believed satisfiable and carry a model sketch; they must stay UNKNOWN.

   Schema conditions use the schema_bench conventions: x = Free 0 is the principal variable (y =
   Free 1 is the second principal variable of binary schemas), further free variables are
   parameters that the instance closes universally. In the named syntax below, free condition
   variables are x, y, w, w2 (Free 0..3); every other variable must be bound.

   CLI (dune exec bench/schema/schema_bench.exe -- ...):
     independent                 TSV: name, expected, family, needed instances, note
     independent-check           validate every witness instance (also run by dune runtest)
     run CASE [--seconds S] [--workers W]       schema search, as for the original cases
     witness CASE [--seconds S] [--tptp-out F]  refute (or export) fixed axioms + witness instances
     independent-depth CASE [--seconds S] [--limit N]   raw/admissible enumeration index
   The cases are also listed by [list] and accepted by [snapshot]. *)

open Axiom_fuzzer

(* ---------- named syntax, converted to De Bruijn Wire.source ---------- *)

type term = V of string | Fn of string * term list

type form =
  | Top
  | Bot
  | In of term * term
  | P of string * term list
  | Eq of term * term
  | Not of form
  | And of form list
  | Or of form list
  | Imp of form * form
  | Iff of form * form
  | All of string list * form
  | Ex of string list * form

let position x l =
  let rec go i = function [] -> None | y :: r -> if y = x then Some i else go (i + 1) r in
  go 0 l

let rec wterm free env = function
  | V x -> (
      match position x env with
      | Some i -> Wire.B i
      | None -> (
          match position x free with
          | Some i -> Wire.F i
          | None -> failwith ("independent: unbound variable " ^ x)))
  | Fn (s, ts) -> Wire.App (s, List.map (wterm free env) ts)

let rec wform free env : form -> Wire.source = function
  | Top -> Wire.Top
  | Bot -> Wire.Bot
  | In (s, t) -> Wire.Pred ("member", [ wterm free env s; wterm free env t ])
  | P (s, ts) -> Wire.Pred (s, List.map (wterm free env) ts)
  | Eq (s, t) -> Wire.Eq (wterm free env s, wterm free env t)
  | Not f -> Wire.Neg (wform free env f)
  | And fs -> Wire.Conj (List.map (wform free env) fs)
  | Or fs -> Wire.Disj (List.map (wform free env) fs)
  | Imp (f, g) -> Wire.Disj [ Wire.Neg (wform free env f); wform free env g ]
  | Iff (f, g) ->
      let a = wform free env f and b = wform free env g in
      Wire.Conj [ Wire.Disj [ Wire.Neg a; b ]; Wire.Disj [ Wire.Neg b; a ] ]
  | All (xs, f) ->
      List.fold_left (fun acc _ -> Wire.All acc) (wform free (List.rev_append xs env) f) xs
  | Ex (xs, f) ->
      List.fold_left (fun acc _ -> Wire.Ex acc) (wform free (List.rev_append xs env) f) xs

let closed f = wform [] [] f
let condition f = wform [ "x"; "y"; "w"; "w2" ] [] f
let mem a b = In (V a, V b)
let c0 s = Fn (s, [])

(* ---------- printing ---------- *)

let rec pp_term env = function
  | Wire.B i -> ( match List.nth_opt env i with Some n -> n | None -> "#" ^ string_of_int i)
  | Wire.F 0 -> "x"
  | Wire.F 1 -> "y"
  | Wire.F 2 -> "w"
  | Wire.F i -> "w" ^ string_of_int (i - 1)
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

(* ---------- schema templates ---------- *)

(* How "x is an element of b" is written in a comprehension template. *)
type encoding =
  | Member  (** member(x, b) *)
  | Sat_first  (** sat(b, x): the "set" is the first argument *)
  | Chi  (** ev(b, x) = tt: characteristic-function encoding, equality only *)

type kind =
  | Comp of encoding  (** ?b. !x. (x in' b <-> phi) *)
  | Sep  (** !a. ?b. !x. (x in b <-> (x in a & phi)) *)
  | Iff_sep  (** mutant: !a. ?b. !x. (x in b <-> (x in a <-> phi)) *)
  | Repl of bool
      (** replacement; [true] = ZF form (!x ?y (phi & unique)) -> image, [false] = mutant that keeps
          totality but drops uniqueness *)
  | Lambda
      (** term comprehension: phi must be y = t with y not in t; instance ?f. !x. ap(f,x) = t *)
  | Fixpoint  (** diagonal-lemma schema: ?c. (t(c) <-> phi(c)) for the unary predicate t *)

let arity_of = function Repl _ | Lambda -> 2 | Comp _ | Sep | Iff_sep | Fixpoint -> 1

let encode_membership a enc x b =
  match enc with
  | Member -> Source.member a x b
  | Sat_first -> Source.pred a "sat" [ b; x ]
  | Chi -> Source.eq a (Source.apply a "ev" [ b; x ]) (Source.apply a "tt" [])

let template kind a phi =
  let arity = arity_of kind in
  let params = List.filter (fun i -> i >= arity) (Source.free_vars a phi) in
  let fresh = List.fold_left max (arity - 1) params + 1 in
  let sv = fresh and rv = fresh + 1 in
  let x = Source.free a 0 and y = Source.free a 1 in
  let set = Source.free a sv and result = Source.free a rv in
  let m = Source.member a in
  let finish f = Source.all a params f in
  let separation body =
    finish
      (Source.all a [ sv ]
         (Source.ex a [ rv ] (Source.all a [ 0 ] (Source.iff a (m x result) body))))
  in
  match kind with
  | Comp enc ->
      finish
        (Source.ex a [ rv ]
           (Source.all a [ 0 ] (Source.iff a (encode_membership a enc x result) phi)))
  | Sep -> separation (Source.and_ a [ m x set; phi ])
  | Iff_sep -> separation (Source.iff a (m x set) phi)
  | Repl unique ->
      let zv = fresh + 2 in
      let z = Source.free a zv in
      let total =
        if unique then
          let only =
            Source.all a [ zv ] (Source.implies a (Source.subst_free a 1 z phi) (Source.eq a z y))
          in
          Source.all a [ 0 ] (Source.ex a [ 1 ] (Source.and_ a [ phi; only ]))
        else Source.all a [ 0 ] (Source.ex a [ 1 ] phi)
      in
      let image =
        Source.all a [ sv ]
          (Source.ex a [ rv ]
             (Source.all a [ 1 ]
                (Source.iff a (m y result) (Source.ex a [ 0 ] (Source.and_ a [ m x set; phi ])))))
      in
      finish (Source.implies a total image)
  | Lambda ->
      (* sv names the function object f; phi(x, y) is y = t(x), so phi(x, ap(f,x)) is ap(f,x) = t(x). *)
      finish
        (Source.ex a [ sv ]
           (Source.all a [ 0 ] (Source.subst_free a 1 (Source.apply a "ap" [ set; x ]) phi)))
  | Fixpoint ->
      (* rv names the fixed point c: t(c) <-> phi(c). *)
      finish
        (Source.ex a [ rv ]
           (Source.iff a (Source.pred a "t" [ result ]) (Source.subst_free a 0 result phi)))

(* ---------- admissibility predicates on the (exported) condition ---------- *)

let admit_any (_ : Wire.source) = true

let rec occurrences_term i = function
  | Wire.F j -> if i = j then 1 else 0
  | Wire.B _ -> 0
  | Wire.App (_, ts) -> List.fold_left (fun n t -> n + occurrences_term i t) 0 ts

let rec occurrences i = function
  | Wire.Top | Wire.Bot -> 0
  | Wire.Pred (_, ts) -> List.fold_left (fun n t -> n + occurrences_term i t) 0 ts
  | Wire.Eq (s, t) -> occurrences_term i s + occurrences_term i t
  | Wire.Neg f | Wire.All f | Wire.Ex f -> occurrences i f
  | Wire.Conj fs | Wire.Disj fs -> List.fold_left (fun n f -> n + occurrences i f) 0 fs

let rec has_equality = function
  | Wire.Eq _ -> true
  | Wire.Top | Wire.Bot | Wire.Pred _ -> false
  | Wire.Neg f | Wire.All f | Wire.Ex f -> has_equality f
  | Wire.Conj fs | Wire.Disj fs -> List.exists has_equality fs

(* Positive: no negation and no falsity (implication is a negated disjunct, so it is excluded). *)
let rec admit_positive = function
  | Wire.Top | Wire.Pred _ | Wire.Eq _ -> true
  | Wire.Bot | Wire.Neg _ -> false
  | Wire.Conj fs | Wire.Disj fs -> List.for_all admit_positive fs
  | Wire.All f | Wire.Ex f -> admit_positive f

(* Curry class: a syntactic sufficient condition for being true in every structure where every atom
   is true. A disjunction needs one such disjunct, so implications A -> B with B in the class are
   admitted whatever A is; a bare negation is not. *)
let rec admit_verum = function
  | Wire.Top | Wire.Pred _ | Wire.Eq _ -> true
  | Wire.Bot | Wire.Neg _ -> false
  | Wire.Conj fs -> List.for_all admit_verum fs
  | Wire.Disj fs -> List.exists admit_verum fs
  | Wire.All f | Wire.Ex f -> admit_verum f

(* Membership edges between variable nodes; every binder is its own node. *)
let membership_edges f =
  let counter = ref 0 and edges = ref [] in
  let node env = function
    | Wire.B i -> Option.map (fun n -> `B n) (List.nth_opt env i)
    | Wire.F i -> Some (`F i)
    | Wire.App _ -> None
  in
  let rec go env = function
    | Wire.Top | Wire.Bot | Wire.Eq _ -> ()
    | Wire.Pred ("member", [ s; t ]) -> (
        match (node env s, node env t) with Some u, Some v -> edges := (u, v) :: !edges | _ -> ())
    | Wire.Pred _ -> ()
    | Wire.Neg f -> go env f
    | Wire.Conj fs | Wire.Disj fs -> List.iter (go env) fs
    | Wire.All f | Wire.Ex f ->
        incr counter;
        go (!counter :: env) f
  in
  go [] f;
  !edges

(* No equality and no membership cycle of length <= k between variables. *)
let admit_acyclic k f =
  (not (has_equality f))
  &&
  let edges = membership_edges f in
  let successors u = List.filter_map (fun (s, t) -> if s = u then Some t else None) edges in
  let rec back u target n =
    n > 0 && List.exists (fun v -> v = target || back v target (n - 1)) (successors u)
  in
  List.for_all (fun (u, _) -> not (back u u k)) edges

(* Sorted (two-sorted in one sort) conditions over sat/2 and ext/1: the first argument of sat is a
   "concept" variable, ext applies only to concept variables, every other position is an object
   (a variable or ext(v)); no variable is used in both sorts, and the principal variable x is an
   object. So sat(x, x) and every other self-application are excluded. *)
let admit_sorted f =
  let counter = ref 0 and concept = ref [] and objects = ref [] and ok = ref true in
  let node env = function
    | Wire.B i -> Option.map (fun n -> `B n) (List.nth_opt env i)
    | Wire.F i -> Some (`F i)
    | Wire.App _ -> None
  in
  let as_concept env v =
    match node env v with Some n -> concept := n :: !concept | None -> ok := false
  in
  let as_object env = function
    | Wire.App ("ext", [ v ]) -> as_concept env v
    | Wire.App _ -> ok := false
    | v -> ( match node env v with Some n -> objects := n :: !objects | None -> ok := false)
  in
  let rec go env = function
    | Wire.Top | Wire.Bot -> ()
    | Wire.Pred ("sat", [ c; o ]) ->
        as_concept env c;
        as_object env o
    | Wire.Pred _ -> ok := false
    | Wire.Eq (u, v) ->
        as_object env u;
        as_object env v
    | Wire.Neg g -> go env g
    | Wire.Conj gs | Wire.Disj gs -> List.iter (go env) gs
    | Wire.All g | Wire.Ex g ->
        incr counter;
        go (!counter :: env) g
  in
  go [] f;
  !ok
  && (not (List.mem (`F 0) !concept))
  && List.for_all (fun n -> not (List.mem n !objects)) !concept

(* Stratified membership conditions (Quine): integer types with type(v) = type(u) + 1 for every
   atom u in v and type(u) = type(v) for every u = v between variables; no function symbols. *)
let admit_stratified f =
  let counter = ref 0 and edges = ref [] and ok = ref true in
  let node env = function
    | Wire.B i -> Option.map (fun n -> `B n) (List.nth_opt env i)
    | Wire.F i -> Some (`F i)
    | Wire.App _ -> None
  in
  let edge env u v d =
    match (node env u, node env v) with
    | Some a, Some b -> edges := (a, b, d) :: !edges
    | _ -> ok := false
  in
  let rec go env = function
    | Wire.Top | Wire.Bot -> ()
    | Wire.Pred ("member", [ u; v ]) -> edge env u v 1
    | Wire.Pred _ -> ok := false
    | Wire.Eq (u, v) -> edge env u v 0
    | Wire.Neg g -> go env g
    | Wire.Conj gs | Wire.Disj gs -> List.iter (go env) gs
    | Wire.All g | Wire.Ex g ->
        incr counter;
        go (!counter :: env) g
  in
  go [] f;
  !ok
  &&
  (* Propagate potentials along the constraint graph (both directions). *)
  let level = Hashtbl.create 8 in
  let rec settle changed =
    let changed' =
      List.fold_left
        (fun changed (a, b, d) ->
          match (Hashtbl.find_opt level a, Hashtbl.find_opt level b) with
          | Some x, None ->
              Hashtbl.replace level b (x + d);
              true
          | None, Some y ->
              Hashtbl.replace level a (y - d);
              true
          | _ -> changed)
        false !edges
    in
    if changed' then settle true
    else
      match List.find_opt (fun (a, _, _) -> not (Hashtbl.mem level a)) !edges with
      | Some (a, _, _) ->
          Hashtbl.replace level a 0;
          settle true
      | None -> changed
  in
  ignore (settle false);
  List.for_all
    (fun (a, b, d) ->
      Hashtbl.find_opt level b = Option.map (fun x -> x + d) (Hashtbl.find_opt level a))
    !edges

(* The principal variable occurs at most once, and there is no equality. *)
let admit_linear f = occurrences 0 f <= 1 && not (has_equality f)

(* y = t or t = y, where t does not contain y. *)
let admit_lambda = function
  | Wire.Eq (Wire.F 1, t) | Wire.Eq (t, Wire.F 1) -> occurrences_term 1 t = 0
  | _ -> false

(* ---------- registered schemas ---------- *)

let encode p = Sexp.to_string (Certificate_io.source p)
let decode s = try Some (Certificate_io.decode_source (Sexp.parse s)) with _ -> None
let admissible_in admissible p = Wire.source_scoped p && admissible p

let schema ~name kind admissible =
  let arity = arity_of kind in
  let ok = admissible_in admissible in
  Theory.Schema.create ~name ~revision:"1"
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

let custom name sg axioms schemas =
  let t = Theory.custom ~name sg (List.map (fun (n, f) -> (n, closed f)) axioms) in
  List.fold_left Theory.register_schema t schemas

(* ---------- enumerated theories (Theory.of_enumerator) ---------- *)

type stage = Emit of Wire.source | Raw of int | Quiet

(* [plan n] decides what stage n emits: a fixed axiom, the instance of the k-th raw condition of
   [Enumerate.exhaustive] over [sg] (quiet when that condition is inadmissible), or nothing. The
   memo of raw conditions is Domain-local and deterministic. *)
let enumerated ~name ~sg ~kind ~admissible ~plan =
  let arity = arity_of kind in
  let ok = admissible_in admissible in
  let key =
    Domain.DLS.new_key (fun () ->
        let a = Source.create sg in
        (a, ref (Enumerate.exhaustive a ~arity), Dynarray.create ()))
  in
  let nth k =
    let a, seq, memo = Domain.DLS.get key in
    let rec fill () =
      if Dynarray.length memo <= k then
        match !seq () with
        | Seq.Nil -> ()
        | Seq.Cons (phi, rest) ->
            seq := rest;
            let p = Wire.export a phi in
            Dynarray.add_last memo
              (if ok p then Some (Wire.export a (template kind a phi)) else None);
            fill ()
    in
    fill ();
    if k < Dynarray.length memo then Dynarray.get memo k else None
  in
  let step n = match plan n with Emit f -> Some f | Quiet -> None | Raw k -> nth k in
  Theory.of_enumerator ~name ~revision:"1" ~step

(* Raw index of a condition (named syntax) in [Enumerate.exhaustive] over [sg], exact match. *)
let raw_index ?(limit = 5_000_000) sg ~arity f =
  let a = Source.create sg in
  let target = Wire.import a (condition f) in
  let rec go i s =
    if i >= limit then failwith "independent: witness condition not found within the limit"
    else
      match s () with
      | Seq.Nil -> failwith "independent: witness condition not enumerated"
      | Seq.Cons (phi, rest) -> if phi = target then i else go (i + 1) rest
  in
  go 0 (Enumerate.exhaustive a ~arity)

let isqrt n =
  let r = int_of_float (sqrt (float_of_int n)) in
  let rec fix r =
    if r * r > n then fix (r - 1) else if (r + 1) * (r + 1) <= n then fix (r + 1) else r
  in
  fix r

(* ---------- fixed axioms ---------- *)

let transitive t =
  All ([ "t1" ], Imp (In (V "t1", t), All ([ "t2" ], Imp (In (V "t2", V "t1"), In (V "t2", t)))))

let ax_empty = Ex ([ "e" ], All ([ "z" ], Not (mem "z" "e")))
let ax_nonempty = Ex ([ "s"; "z" ], mem "z" "s")
let ax_universal = Ex ([ "u" ], All ([ "z" ], mem "z" "u"))
let ax_singletons = All ([ "s" ], Ex ([ "t" ], All ([ "z" ], Iff (mem "z" "t", Eq (V "z", V "s")))))
let ax_distinct = Ex ([ "u"; "v" ], Not (Eq (V "u", V "v")))

let ax_pairing =
  All
    ( [ "p"; "q" ],
      Ex ([ "c" ], All ([ "z" ], Iff (mem "z" "c", Or [ Eq (V "z", V "p"); Eq (V "z", V "q") ]))) )

let ax_foundation =
  All
    ( [ "s" ],
      Imp
        ( Ex ([ "y" ], mem "y" "s"),
          Ex ([ "y" ], And [ mem "y" "s"; All ([ "z" ], Imp (mem "z" "s", Not (mem "z" "y"))) ]) )
    )

let ord t = P ("ord", [ t ])
let ax_ord_hereditary = All ([ "p"; "q" ], Imp (And [ ord (V "p"); mem "q" "p" ], ord (V "q")))

let ax_ord_closure =
  All
    ( [ "p" ],
      Imp (And [ All ([ "q" ], Imp (mem "q" "p", ord (V "q"))); transitive (V "p") ], ord (V "p"))
    )

let ax_ord_irreflexive = All ([ "p" ], Imp (ord (V "p"), Not (mem "p" "p")))
let h t = Fn ("h", [ t ])
let ax_h_into = All ([ "p" ], In (h (V "p"), c0 "a"))
let ax_h_injective = All ([ "p"; "q" ], Imp (Eq (h (V "p"), h (V "q")), Eq (V "p", V "q")))
let n t = Fn ("n", [ t ])
let ax_fixpoint_free = All ([ "p" ], Not (Eq (n (V "p"), V "p")))
let ax_moves = Ex ([ "p" ], Not (Eq (n (V "p"), V "p")))

(* Every set s is decoded by some index i in a: e(i,z) <-> z in s. *)
let ax_coding =
  All
    ( [ "s" ],
      Ex
        ( [ "i" ],
          And [ In (V "i", c0 "a"); All ([ "z" ], Iff (P ("e", [ V "i"; V "z" ]), mem "z" "s")) ] )
    )

(* ---------- signatures ---------- *)

let sg_sat = Signature.make ~functions:[] ~predicates:[ ("sat", 2) ]
let sg_chi = Signature.make ~functions:[ ("ev", 2); ("tt", 0) ] ~predicates:[]
let sg_h = Signature.make ~functions:[ ("h", 1); ("a", 0) ] ~predicates:[ ("member", 2) ]
let sg_lambda = Signature.make ~functions:[ ("ap", 2); ("n", 1) ] ~predicates:[]
let sg_ord = Signature.make ~functions:[] ~predicates:[ ("member", 2); ("ord", 1) ]
let sg_coding = Signature.make ~functions:[ ("a", 0) ] ~predicates:[ ("member", 2); ("e", 2) ]

(* Signatures of the breadth cases. *)
let sg_frege = Signature.make ~functions:[ ("ext", 1) ] ~predicates:[ ("sat", 2) ]
let sg_liar = Signature.make ~functions:[ ("neg", 1) ] ~predicates:[ ("t", 1) ]
let sg_wf = Signature.make ~functions:[] ~predicates:[ ("member", 2); ("wf", 1) ]
let sg_comp = Signature.make ~functions:[ ("comp", 1) ] ~predicates:[ ("member", 2) ]

(* Frege's Basic Law V: ext(f) = ext(g) <-> f and g hold of the same objects. *)
let ax_basic_law_v =
  All
    ( [ "f"; "g" ],
      Iff
        ( Eq (Fn ("ext", [ V "f" ]), Fn ("ext", [ V "g" ])),
          All ([ "z" ], Iff (P ("sat", [ V "f"; V "z" ]), P ("sat", [ V "g"; V "z" ]))) ) )

(* Compositional truth for negation, and its truth-preserving near miss. *)
let t_ x = P ("t", [ x ])
let ax_neg_flips = All ([ "p" ], Iff (t_ (Fn ("neg", [ V "p" ])), Not (t_ (V "p"))))
let ax_neg_keeps = All ([ "p" ], Iff (t_ (Fn ("neg", [ V "p" ])), t_ (V "p")))

(* Well-founded sets: a set of well-founded sets is well-founded, and none is a self-member. *)
let wf x = P ("wf", [ x ])
let ax_wf_closure = All ([ "p" ], Imp (All ([ "q" ], Imp (mem "q" "p", wf (V "q"))), wf (V "p")))
let ax_wf_irreflexive = All ([ "p" ], Imp (wf (V "p"), Not (mem "p" "p")))

(* Complement as an operation: x in comp(a) <-> x notin a. *)
let ax_complement_op =
  All ([ "s"; "z" ], Iff (In (V "z", Fn ("comp", [ V "s" ])), Not (mem "z" "s")))

(* An unstratified separation instance as a fixed axiom: {z in a | z notin z} exists. *)
let ax_russell_part =
  All
    ([ "s" ], Ex ([ "b" ], All ([ "z" ], Iff (mem "z" "b", And [ mem "z" "s"; Not (mem "z" "z") ]))))

let ax_self_member = Ex ([ "s" ], mem "s" "s")

(* ---------- witness conditions ---------- *)

let w_grelling = Not (P ("sat", [ V "x"; V "x" ]))
let w_chi = Not (Eq (Fn ("ev", [ V "x"; V "x" ]), c0 "tt"))

let w_4cycle =
  Not (Ex ([ "b1"; "b2"; "b3" ], And [ mem "x" "b1"; mem "b1" "b2"; mem "b2" "b3"; mem "b3" "x" ]))

let w_linear = Ex ([ "s" ], And [ mem "x" "s"; All ([ "v" ], Imp (mem "v" "s", Not (mem "v" "v"))) ])
let w_cantor = Ex ([ "v" ], And [ Eq (V "x", h (V "v")); Not (mem "x" "v") ])
let w_lambda = Eq (V "y", n (Fn ("ap", [ V "x"; V "x" ])))
let w_curry = Imp (mem "x" "x", All ([ "u"; "v" ], Eq (V "u", V "v")))

(* ---------- cases ---------- *)

type expected = Unsat | Consistent
type witness = Inst of string * form | Stage of int Lazy.t

type case = {
  name : string;
  family : string;
  expected : expected;
  needed : string;  (** instances of the witness (Unsat) or "-" (controls) *)
  note : string;  (** why the case is interesting; for controls, the model sketch *)
  signature : Signature.t;
  build : unit -> Theory.t;
  witness : witness list;
}

let pos () = schema ~name:"pos" (Comp Member) admit_positive
let sep () = schema ~name:"sep" Sep admit_any

let square_plan n =
  let k = isqrt n in
  if k * k = n then Raw k else Quiet

let chi_square_stage =
  lazy
    (let k = raw_index sg_chi ~arity:1 w_chi in
     k * k)

let lambda_stage = lazy (1 + raw_index sg_lambda ~arity:2 w_lambda)

let cases =
  [
    {
      name = "i-grelling-sat";
      family = "Russell / relation encoding";
      expected = Unsat;
      needed = "comp-sat(~sat(x,x))";
      note =
        "Grelling-Nelson heterological paradox: membership is an arbitrary binary relation \
         sat(w,x) whose 'set' argument comes FIRST; no member symbol in the signature.";
      signature = sg_sat;
      build =
        (fun () ->
          custom "i-grelling-sat" sg_sat [] [ schema ~name:"comp-sat" (Comp Sat_first) admit_any ]);
      witness = [ Inst ("comp-sat", w_grelling) ];
    };
    {
      name = "i-chi-russell";
      family = "Russell / function-symbol (characteristic function) encoding";
      expected = Unsat;
      needed = "comp-ev(~ev(x,x) = tt)";
      note =
        "Membership is ev(b,x) = tt for a binary function ev and constant tt; the language has no \
         predicate at all, so the diagonal lives entirely in equality reasoning.";
      signature = sg_chi;
      build =
        (fun () -> custom "i-chi-russell" sg_chi [] [ schema ~name:"comp-ev" (Comp Chi) admit_any ]);
      witness = [ Inst ("comp-ev", w_chi) ];
    };
    {
      name = "i-russell-4cycle";
      family = "Russell / k-step membership cycles (k = 4)";
      expected = Unsat;
      needed = "comp-acyclic3(~?b1 b2 b3.(x in b1 & b1 in b2 & b2 in b3 & b3 in x))";
      note =
        "Comprehension for equality-free conditions without membership cycles of length <= 3. The \
         4-cycle diagonal is the shortest Russell-type condition left (size 9, three bound \
         variables): needle deep in enumeration order.";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i-russell-4cycle" Signature.sets []
            [ schema ~name:"comp-acyclic3" (Comp Member) (admit_acyclic 3) ]);
      witness = [ Inst ("comp-acyclic3", w_4cycle) ];
    };
    {
      name = "i-linear-singleton";
      family = "guarded comprehension still admitting a diagonal";
      expected = Unsat;
      needed = "comp-linear(?s.(x in s & !v.(v in s -> ~v in v)))";
      note =
        "Comprehension only for equality-free conditions in which x occurs at most once, which \
         excludes ~x in x and every k-cycle. With singletons, {x | some set containing x has only \
         non-self-membered elements} is still the Russell class.";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i-linear-singleton" Signature.sets
            [ ("singletons", ax_singletons) ]
            [ schema ~name:"comp-linear" (Comp Member) admit_linear ]);
      witness = [ Inst ("comp-linear", w_linear) ];
    };
    {
      name = "i-cantor-injection";
      family = "Cantor / injection";
      expected = Unsat;
      needed = "sep(?v.(x = h(v) & ~x in v)) on a";
      note =
        "Cantor's theorem in injective form: h maps every set injectively into the set a. The \
         diagonal D = {h(v) in a | h(v) notin v} gives h(D) in D <-> h(D) notin D; needs equality \
         and the injectivity axiom, not a surjection.";
      signature = sg_h;
      build =
        (fun () ->
          custom "i-cantor-injection" sg_h
            [ ("into", ax_h_into); ("injective", ax_h_injective) ]
            [ sep () ]);
      witness = [ Inst ("sep", w_cantor) ];
    };
    {
      name = "i-lawvere-fixpoint";
      family = "Cantor / Lawvere fixed point (term comprehension)";
      expected = Unsat;
      needed = "lambda(y = n(ap(x,x)))";
      note =
        "Combinatory completeness (every term t(x) is represented by some f with ap(f,x) = t(x)) \
         plus a fixed-point-free n: f = [x] n(ap(x,x)) gives ap(f,f) = n(ap(f,f)). Pure equality, \
         schema parameter is a term equation.";
      signature = sg_lambda;
      build =
        (fun () ->
          custom "i-lawvere-fixpoint" sg_lambda
            [ ("fixpoint_free", ax_fixpoint_free) ]
            [ schema ~name:"lambda" Lambda admit_lambda ]);
      witness = [ Inst ("lambda", w_lambda) ];
    };
    {
      name = "i-curry-distinct";
      family = "Curry";
      expected = Unsat;
      needed = "comp-verum(x in x -> !u v. u = v)";
      note =
        "Comprehension restricted to conditions true in the one-point all-true structure (no bare \
         negation, no falsity), which alone is consistent. Two distinct objects make the \
         consequent of Curry's set C = {x | x in x -> !u v. u = v} false.";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i-curry-distinct" Signature.sets
            [ ("distinct", ax_distinct) ]
            [ schema ~name:"comp-verum" (Comp Member) admit_verum ]);
      witness = [ Inst ("comp-verum", w_curry) ];
    };
    {
      name = "i-mirimanoff-foundation";
      family = "Mirimanoff-lite / positive comprehension vs foundation";
      expected = Unsat;
      needed = "pos(T) [V], pos(x = w) with w := V [{V}]; foundation on {V}";
      note =
        "Positive comprehension (consistent alone) yields the universal set V and its singleton; \
         the ZF foundation axiom applied to {V} contradicts V in V. The witness uses two \
         instances; that two are necessary is not claimed (a parameterized single instance can \
         suffice).";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i-mirimanoff-foundation" Signature.sets
            [ ("foundation", ax_foundation) ]
            [ pos () ]);
      witness = [ Inst ("pos", Top); Inst ("pos", Eq (V "x", V "w")) ];
    };
    {
      name = "i-burali-forti-pred";
      family = "Burali-Forti-lite (ordinal predicate)";
      expected = Unsat;
      needed = "pos(ord(x))";
      note =
        "Positive comprehension of the ordinal class Omega = {x | ord(x)}. Fixed axioms say ord is \
         hereditary, every transitive set of ords is an ord, and no ord is a self-member; so Omega \
         is an ord, Omega in Omega. Atomic condition, multi-step first-order argument.";
      signature = sg_ord;
      build =
        (fun () ->
          custom "i-burali-forti-pred" sg_ord
            [
              ("ord_hereditary", ax_ord_hereditary);
              ("ord_closure", ax_ord_closure);
              ("ord_irreflexive", ax_ord_irreflexive);
            ]
            [ pos () ]);
      witness = [ Inst ("pos", ord (V "x")) ];
    };
    {
      name = "i-cantor-coding";
      family = "Cantor / decoding relation";
      expected = Unsat;
      needed = "sep(~e(x,x)) on a";
      note =
        "Every set is decoded by an index i in a through a relation e (e(i,z) <-> z in s). The \
         diagonal is stated in the decoding relation, not in membership: D = {x in a | ~e(x,x)} \
         has an index i with e(i,i) <-> ~e(i,i).";
      signature = sg_coding;
      build = (fun () -> custom "i-cantor-coding" sg_coding [ ("coding", ax_coding) ] [ sep () ]);
      witness = [ Inst ("sep", Not (P ("e", [ V "x"; V "x" ]))) ];
    };
    {
      name = "i-iff-sep-empty";
      family = "mutated separation (And -> Iff)";
      expected = Unsat;
      needed = "iffsep(x in x) on the empty set";
      note =
        "Single-site mutation of separation: x in b <-> (x in a <-> phi). On the empty set this is \
         {x | ~phi}, so the POSITIVE condition x in x yields the Russell set; ~x in x does not.";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i-iff-sep-empty" Signature.sets
            [ ("empty", ax_empty) ]
            [ schema ~name:"iffsep" Iff_sep admit_any ]);
      witness = [ Inst ("iffsep", mem "x" "x") ];
    };
    {
      name = "i-repl-total";
      family = "mutated replacement (uniqueness dropped)";
      expected = Unsat;
      needed = "repl-total(~y in y): antecedent by the empty set, image of a nonempty set";
      note =
        "Replacement whose antecedent keeps totality !x ?y phi but drops uniqueness. The condition \
         ignores x; discharging the antecedent needs the empty set, and the image of a nonempty \
         set is the Russell class.";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i-repl-total" Signature.sets
            [ ("empty", ax_empty); ("nonempty", ax_nonempty) ]
            [ schema ~name:"repl-total" (Repl false) admit_any ]);
      witness = [ Inst ("repl-total", Not (mem "y" "y")) ];
    };
    {
      name = "i-pos-plus-sep";
      family = "two schemas, two instances (positive comprehension + separation)";
      expected = Unsat;
      needed = "pos(T) [V], sep(~x in x) on V";
      note =
        "Each schema alone is consistent (one-point model u = {u}; V_2), so every refutation uses \
         at least one instance of each. No fixed axioms.";
      signature = Signature.sets;
      build = (fun () -> custom "i-pos-plus-sep" Signature.sets [] [ pos (); sep () ]);
      witness = [ Inst ("pos", Top); Inst ("sep", Not (mem "x" "x")) ];
    };
    {
      name = "i-enum-chi-sparse";
      family = "Theory.of_enumerator / quiet stages";
      expected = Unsat;
      needed = "stage k^2 where k = raw index of ~ev(x,x) = tt";
      note =
        "Recursively enumerated presentation of i-chi-russell: the k-th raw condition's \
         comprehension instance is emitted only at stage k*k and every other stage is quiet, so \
         the single needed axiom sits at a large stage number.";
      signature = sg_chi;
      build =
        (fun () ->
          enumerated ~name:"i-enum-chi-sparse" ~sg:sg_chi ~kind:(Comp Chi) ~admissible:admit_any
            ~plan:square_plan);
      witness = [ Stage chi_square_stage ];
    };
    {
      name = "i-enum-lawvere";
      family = "Theory.of_enumerator / term comprehension";
      expected = Unsat;
      needed = "stage 0 (n has no fixed point) and stage 1 + raw index of y = n(ap(x,x))";
      note =
        "Enumerated presentation of i-lawvere-fixpoint: stage 0 emits the fixed axiom, stage k+1 \
         the instance of the k-th raw binary condition when it has the form y = t (quiet \
         otherwise).";
      signature = sg_lambda;
      build =
        (fun () ->
          enumerated ~name:"i-enum-lawvere" ~sg:sg_lambda ~kind:Lambda ~admissible:admit_lambda
            ~plan:(fun n -> if n = 0 then Emit (closed ax_fixpoint_free) else Raw (n - 1)));
      witness = [ Stage (lazy 0); Stage lambda_stage ];
    };
    (* ---------- consistent controls ---------- *)
    {
      name = "i-ctl-positive";
      family = "control: positive comprehension";
      expected = Consistent;
      needed = "-";
      note =
        "Model: one point u with u in u. Every atom is true there, so every positive condition \
         holds of u and b := u satisfies each instance.";
      signature = Signature.sets;
      build = (fun () -> custom "i-ctl-positive" Signature.sets [] [ pos () ]);
      witness = [];
    };
    {
      name = "i-ctl-verum-universal";
      family = "control: Curry class with a universal set";
      expected = Consistent;
      needed = "-";
      note =
        "Near miss of i-curry-distinct (no falsity source). Model: one point u = {u}; u is \
         universal and every admitted condition is true of u.";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i-ctl-verum-universal" Signature.sets
            [ ("universal", ax_universal) ]
            [ schema ~name:"comp-verum" (Comp Member) admit_verum ]);
      witness = [];
    };
    {
      name = "i-ctl-cantor-noninjective";
      family = "control: Cantor without injectivity";
      expected = Consistent;
      needed = "-";
      note =
        "Near miss of i-cantor-injection. Model: V_2 = {0, 1} with 0 = {}, 1 = {0}, a = 1, h \
         constantly 0; every subset of every extension is an element, so all separation instances \
         hold.";
      signature = sg_h;
      build = (fun () -> custom "i-ctl-cantor-noninjective" sg_h [ ("into", ax_h_into) ] [ sep () ]);
      witness = [];
    };
    {
      name = "i-ctl-lambda-moving";
      family = "control: term comprehension with a non-identity n";
      expected = Consistent;
      needed = "-";
      note =
        "Near miss of i-lawvere-fixpoint (!p. n(p) != p weakened to ?p). Model: closed lambda \
         terms modulo beta, ap = application, n(p) = K p; t(x) is represented by [x] t, and K I != \
         I by Church-Rosser.";
      signature = sg_lambda;
      build =
        (fun () ->
          custom "i-ctl-lambda-moving" sg_lambda
            [ ("moves", ax_moves) ]
            [ schema ~name:"lambda" Lambda admit_lambda ]);
      witness = [];
    };
    {
      name = "i-ctl-repl-functional";
      family = "control: ZF replacement with uniqueness";
      expected = Consistent;
      needed = "-";
      note =
        "Near miss of i-repl-total (uniqueness kept). Model: the hereditarily finite sets V_omega; \
         the image of a finite set under a definable function is a finite set of HF sets.";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i-ctl-repl-functional" Signature.sets
            [ ("empty", ax_empty); ("nonempty", ax_nonempty) ]
            [ schema ~name:"repl" (Repl true) admit_any ]);
      witness = [];
    };
    {
      name = "i-ctl-burali-forti-reflexive";
      family = "control: Burali-Forti without irreflexivity";
      expected = Consistent;
      needed = "-";
      note =
        "Near miss of i-burali-forti-pred (ord_irreflexive dropped). Model: one point u with u in \
         u and ord(u); all atoms are true, so every positive condition holds of u.";
      signature = sg_ord;
      build =
        (fun () ->
          custom "i-ctl-burali-forti-reflexive" sg_ord
            [ ("ord_hereditary", ax_ord_hereditary); ("ord_closure", ax_ord_closure) ]
            [ pos () ]);
      witness = [];
    };
    {
      name = "i-ctl-enum-separation";
      family = "control: Theory.of_enumerator separation";
      expected = Consistent;
      needed = "-";
      note =
        "Stage 0 emits the empty set, stage 1 pairing, stage k+2 the separation instance of the \
         k-th raw condition. Model: the hereditarily finite sets V_omega.";
      signature = Signature.sets;
      build =
        (fun () ->
          enumerated ~name:"i-ctl-enum-separation" ~sg:Signature.sets ~kind:Sep
            ~admissible:admit_any ~plan:(function
            | 0 -> Emit (closed ax_empty)
            | 1 -> Emit (closed ax_pairing)
            | n -> Raw (n - 2)));
      witness = [];
    };
  ]

(* Breadth cases (phase 3): contradictions of directions the 22 cases above do not cover, written
   for the breadth measurement of the default lane (no condition prior). Same conventions; each
   inconsistent case's fixed axioms alone are consistent (the note says why). *)
let breadth_cases =
  [
    {
      name = "i2-frege-blv";
      family = "Frege / Basic Law V (abstraction principle)";
      expected = Unsat;
      needed = "comp-sorted(~?f.(x = ext(f) & sat(f,x)))";
      note =
        "Concept comprehension ?r. !x. (sat(r,x) <-> phi(x)) for sorted conditions (concept \
         variables only in sat's first argument and under ext, never as objects, so no \
         self-application sat(x,x)), plus Basic Law V. Russell's class of extensions not falling \
         under their concept refutes it through ext(r). Basic Law V alone: one point, ext the \
         identity, sat empty.";
      signature = sg_frege;
      build =
        (fun () ->
          custom "i2-frege-blv" sg_frege
            [ ("basic_law_v", ax_basic_law_v) ]
            [ schema ~name:"comp-sorted" (Comp Sat_first) admit_sorted ]);
      witness =
        [
          Inst
            ( "comp-sorted",
              Not
                (Ex ([ "f" ], And [ Eq (V "x", Fn ("ext", [ V "f" ])); P ("sat", [ V "f"; V "x" ]) ]))
            );
        ];
    };
    {
      name = "i2-liar-fixpoint";
      family = "liar / diagonal lemma for a truth predicate";
      expected = Unsat;
      needed = "fixpoint(t(neg(x)))";
      note =
        "A diagonal-lemma schema ?c. (t(c) <-> phi(c)) for positive conditions (consistent alone: \
         one point, t true) and compositional truth for negation t(neg(p)) <-> ~t(p) (consistent \
         alone: two points swapped by neg). The fixed point of t(neg(x)) is a liar sentence. No \
         membership relation at all.";
      signature = sg_liar;
      build =
        (fun () ->
          custom "i2-liar-fixpoint" sg_liar
            [ ("neg_flips", ax_neg_flips) ]
            [ schema ~name:"fixpoint" Fixpoint admit_positive ]);
      witness = [ Inst ("fixpoint", t_ (Fn ("neg", [ V "x" ]))) ];
    };
    {
      name = "i2-strat-unstratified";
      family = "stratification violation (NFU comprehension + one unstratified axiom)";
      expected = Unsat;
      needed = "comp-strat(T) [the universal set]; the fixed axiom on it is Russell's set";
      note =
        "Comprehension for stratified conditions only (Jensen's NFU without extensionality: \
         consistent) yields the universal set; the unstratified fixed axiom {z in s | z notin z} \
         (a ZF separation instance: consistent alone) applied to it gives Russell's set.";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i2-strat-unstratified" Signature.sets
            [ ("russell_part", ax_russell_part) ]
            [ schema ~name:"comp-strat" (Comp Member) admit_stratified ]);
      witness = [ Inst ("comp-strat", Top) ];
    };
    {
      name = "i2-mirimanoff-wf";
      family = "Mirimanoff (class of well-founded sets) via positive separation";
      expected = Unsat;
      needed = "pos-sep(wf(x)) on the universal set";
      note =
        "Separation for positive conditions from a universal set gives W = {x | wf(x)}; every \
         member of W is well-founded, so wf(W), so W in W, against irreflexivity. Fixed axioms \
         alone: one point u in u with wf false.";
      signature = sg_wf;
      build =
        (fun () ->
          custom "i2-mirimanoff-wf" sg_wf
            [
              ("universal", ax_universal);
              ("wf_closure", ax_wf_closure);
              ("wf_irreflexive", ax_wf_irreflexive);
            ]
            [ schema ~name:"pos-sep" Sep admit_positive ]);
      witness = [ Inst ("pos-sep", wf (V "x")) ];
    };
    {
      name = "i2-positive-complement";
      family = "positive comprehension + a complement operation (GPK-style)";
      expected = Unsat;
      needed = "pos(x in comp(x))";
      note =
        "Positive comprehension alone is consistent (one point, all atoms true); with a complement \
         operation x in comp(s) <-> x notin s (consistent alone: 0 = {}, 1 = {0,1}, comp swaps \
         them) the POSITIVE condition x in comp(x) is Russell's condition.";
      signature = sg_comp;
      build =
        (fun () ->
          custom "i2-positive-complement" sg_comp
            [ ("complement_op", ax_complement_op) ]
            [ schema ~name:"pos" (Comp Member) admit_positive ]);
      witness = [ Inst ("pos", In (V "x", Fn ("comp", [ V "x" ]))) ];
    };
    {
      name = "i2-ctl-liar-preserving";
      family = "control: diagonal lemma with a truth-preserving operation";
      expected = Consistent;
      needed = "-";
      note =
        "Near miss of i2-liar-fixpoint (t(neg(p)) <-> t(p)). Model: one point, t true; every \
         positive condition is true there.";
      signature = sg_liar;
      build =
        (fun () ->
          custom "i2-ctl-liar-preserving" sg_liar
            [ ("neg_keeps", ax_neg_keeps) ]
            [ schema ~name:"fixpoint" Fixpoint admit_positive ]);
      witness = [];
    };
    {
      name = "i2-ctl-strat-self-member";
      family = "control: stratified comprehension with a harmless unstratified axiom";
      expected = Consistent;
      needed = "-";
      note =
        "Near miss of i2-strat-unstratified: the unstratified axiom ?s. s in s holds in NFU models \
         (the universal set is a member of itself), and stratified comprehension without \
         extensionality is consistent (Jensen).";
      signature = Signature.sets;
      build =
        (fun () ->
          custom "i2-ctl-strat-self-member" Signature.sets
            [ ("self_member", ax_self_member) ]
            [ schema ~name:"comp-strat" (Comp Member) admit_stratified ]);
      witness = [];
    };
  ]

let all = cases @ breadth_cases
let find name = List.find_opt (fun c -> c.name = name) all
let expected_text = function Unsat -> "UNSAT" | Consistent -> "UNKNOWN"

let print_table () =
  List.iter
    (fun c ->
      Printf.printf "%s\t%s\t%s\t%s\t%s\n" c.name (expected_text c.expected) c.family c.needed
        c.note)
    all

(* ---------- witnesses ---------- *)

let parameter_text (ax : Wire.axiom) =
  match ax.origin with
  | Wire.Registered_instance (name, _, data) when name = Natural_checker.enumeration_name ->
      "stage " ^ data
  | Wire.Registered_instance (_, _, data) -> (
      match decode data with Some p -> pp_source p | None -> data)
  | Wire.Instance (_, phi) -> pp_source phi
  | _ -> "?"

(* Validated witness instances: each is admitted by its schema check (or is an emitted stage) and
   accepted by Theory.validate_axiom. Raises Failure otherwise. *)
let witness_instances ?(quiet = false) c =
  let t = c.build () in
  let a = Theory.arena t in
  let next = ref (List.length (Theory.fixed t)) in
  let fresh () =
    let id = !next in
    incr next;
    id
  in
  let accept (ax : Wire.axiom) =
    if not (Theory.validate_axiom t ax) then
      failwith ("witness rejected by schema check: " ^ ax.name);
    if not quiet then Printf.printf "witness %s := %s  (validated)\n%!" ax.name (parameter_text ax);
    (ax.name, ax.formula)
  in
  let instance = function
    | Inst (schema_name, f) ->
        let schema =
          match List.find_opt (fun k -> Wire.schema_name k = schema_name) (Theory.schemas t) with
          | Some k -> k
          | None -> failwith ("no schema " ^ schema_name ^ " in " ^ c.name)
        in
        let p =
          match Theory.guided_parameter t schema (Wire.import a (condition f)) with
          | Some p -> p
          | None -> failwith ("inadmissible witness for " ^ schema_name ^ " in " ^ c.name)
        in
        accept (Theory.instantiate_parameter t ~id:(fresh ()) schema p)
    | Stage n -> accept (Theory.instantiate_enumerated t ~id:(fresh ()) (Lazy.force n))
  in
  let instances = List.map instance c.witness in
  (t, instances)

(* First-order witness problem: fixed axioms plus the validated instances, without schemas. *)
let witness_theory c =
  let t, instances = witness_instances c in
  let fixed = List.map (fun (ax : Wire.axiom) -> (ax.name, ax.formula)) (Theory.fixed t) in
  Theory.custom ~name:("witness-" ^ c.name) c.signature (fixed @ instances)

(* Fast structural check of the whole set (no proof search); used by the runtest rule. *)
let check_all () =
  let names = List.map (fun c -> c.name) all in
  if List.length (List.sort_uniq compare names) <> List.length names then
    failwith "duplicate case name";
  List.iter
    (fun c ->
      (match (c.expected, c.witness) with
      | Unsat, [] -> failwith (c.name ^ ": inconsistent case without witness")
      | Consistent, _ :: _ -> failwith (c.name ^ ": control with a witness")
      | _ -> ());
      let _, instances = witness_instances ~quiet:true c in
      Printf.printf "ok %s (%s, %d witness instances)\n%!" c.name (expected_text c.expected)
        (List.length instances))
    all

(* ---------- needle depth in the exhaustive enumeration ---------- *)

let rename_free map p =
  let rec term = function
    | Wire.F i -> Wire.F (map i)
    | Wire.B i -> Wire.B i
    | Wire.App (s, ts) -> Wire.App (s, List.map term ts)
  in
  let rec go = function
    | (Wire.Top | Wire.Bot) as f -> f
    | Wire.Pred (s, ts) -> Wire.Pred (s, List.map term ts)
    | Wire.Eq (s, t) -> Wire.Eq (term s, term t)
    | Wire.Neg f -> Wire.Neg (go f)
    | Wire.Conj fs -> Wire.Conj (List.map go fs)
    | Wire.Disj fs -> Wire.Disj (List.map go fs)
    | Wire.All f -> Wire.All (go f)
    | Wire.Ex f -> Wire.Ex (go f)
  in
  go p

let rec permutations = function
  | [] -> [ [] ]
  | l ->
      List.concat_map
        (fun x -> List.map (fun r -> x :: r) (permutations (List.filter (( <> ) x) l)))
        l

(* All variants of a condition with its parameters renamed onto arity, arity+1, ... *)
let variants a ~arity phi =
  let params = List.filter (fun i -> i >= arity) (Source.free_vars a phi) in
  let p = Wire.export a phi in
  List.map
    (fun perm ->
      let table = List.combine perm (List.init (List.length perm) (fun i -> arity + i)) in
      Wire.export a
        (Wire.import a (rename_free (fun i -> Option.value ~default:i (List.assoc_opt i table)) p)))
    (permutations params)

let schema_arity = function "repl-total" | "repl" | "lambda" -> 2 | _ -> 1

(* Raw and admissible positions of each witness condition (up to parameter renaming) in its
   schema's exhaustive enumeration ([Enumerate.exhaustive] over the case signature, the stream the
   registered schemas use for unbounded enumeration), bounded by [limit] raw conditions and
   [seconds]. Stage witnesses print their stage number. *)
let depth ~limit ~seconds c =
  let t = c.build () in
  let admitted schema a phi =
    Theory.guided_parameter t schema (Wire.import (Theory.arena t) (Wire.export a phi)) <> None
  in
  List.iter
    (function
      | Stage n -> Printf.printf "case=%s stage=%d\n%!" c.name (Lazy.force n)
      | Inst (schema_name, f) ->
          let schema = List.find (fun k -> Wire.schema_name k = schema_name) (Theory.schemas t) in
          let arity = schema_arity schema_name in
          let a = Source.create c.signature in
          let target = Wire.import a (condition f) in
          if not (admitted schema a target) then failwith ("inadmissible witness in " ^ c.name);
          let goal = variants a ~arity target in
          let t0 = Unix.gettimeofday () in
          let report found i k phi =
            Printf.printf
              "case=%s schema=%s condition=%s size=%d found=%s raw=%d admissible=%d seconds=%.1f\n\
               %!"
              c.name schema_name
              (pp_source (Wire.export a phi))
              (Source.size a phi) found i k
              (Unix.gettimeofday () -. t0)
          in
          let rec go i k s =
            if i >= limit || Unix.gettimeofday () -. t0 > seconds then report "no(limit)" i k target
            else
              match s () with
              | Seq.Nil -> report "no(exhausted)" i k target
              | Seq.Cons (phi, rest) ->
                  let ok = admitted schema a phi in
                  if ok && List.exists (fun v -> List.mem v goal) (variants a ~arity phi) then
                    report "yes" i k phi
                  else go (i + 1) (if ok then k + 1 else k) rest
          in
          go 0 0 (Enumerate.exhaustive a ~arity))
    c.witness
