type term = T of int * int
type formula = F of int * int
type term_node = Bound of int | Free of int | Apply of string * term list

type formula_node =
  | True
  | False
  | Pred of string * term list
  | Eq of term * term
  | Not of formula
  | And of formula list
  | Or of formula list
  | Forall of formula
  | Exists of formula

(* Node tables with explicit hash and structural equality instead of the polymorphic ones. An
   arena's IDs are its allocation order and its table only finds nodes already interned, so the IDs
   are those the generic arena gave. *)
module Hash = struct
  let[@inline] mix h x = h lxor x * 0x100000001b3
  let seed = 0x2545f4914f6cdd1d

  let[@inline] finish h =
    let h = h lxor (h lsr 32) in
    let h = h * 0x3f51afd7ed558ccd in
    h lxor (h lsr 29) land max_int

  let terms h ts = List.fold_left (fun h (T (o, i)) -> mix (mix h o) i) h ts
  let formulas h fs = List.fold_left (fun h (F (o, i)) -> mix (mix h o) i) h fs
end

let[@inline] same_term (T (o, i)) (T (p, j)) = Int.equal o p && Int.equal i j
let[@inline] same_formula (F (o, i)) (F (p, j)) = Int.equal o p && Int.equal i j

module Terms = Arena.Make (struct
  type t = term_node

  let equal a b =
    match (a, b) with
    | Bound i, Bound j | Free i, Free j -> Int.equal i j
    | Apply (s, ts), Apply (r, us) -> String.equal s r && List.equal same_term ts us
    | _ -> false

  let hash = function
    | Bound i -> Hash.(finish (mix (mix seed 1) i))
    | Free i -> Hash.(finish (mix (mix seed 2) i))
    | Apply (s, ts) -> Hash.(finish (terms (mix (mix seed 3) (String.hash s)) ts))
end)

module Formulas = Arena.Make (struct
  type t = formula_node

  let equal a b =
    match (a, b) with
    | True, True | False, False -> true
    | Pred (s, ts), Pred (r, us) -> String.equal s r && List.equal same_term ts us
    | Eq (x, y), Eq (u, v) -> same_term x u && same_term y v
    | Not f, Not g | Forall f, Forall g | Exists f, Exists g -> same_formula f g
    | And fs, And gs | Or fs, Or gs -> List.equal same_formula fs gs
    | _ -> false

  let hash = function
    | True -> 1
    | False -> 2
    | Pred (s, ts) -> Hash.(finish (terms (mix (mix seed 3) (String.hash s)) ts))
    | Eq (x, y) -> Hash.(finish (terms (mix seed 4) [ x; y ]))
    | Not f -> Hash.(finish (formulas (mix seed 5) [ f ]))
    | And fs -> Hash.(finish (formulas (mix seed 6) fs))
    | Or fs -> Hash.(finish (formulas (mix seed 7) fs))
    | Forall f -> Hash.(finish (formulas (mix seed 8) [ f ]))
    | Exists f -> Hash.(finish (formulas (mix seed 9) [ f ]))
end)

type t = { owner : int; signature : Signature.t; terms : Terms.t; formulas : Formulas.t }

let owners = Atomic.make 0

let create signature =
  {
    owner = Atomic.fetch_and_add owners 1;
    signature;
    terms = Terms.create ();
    formulas = Formulas.create ();
  }

let signature a = a.signature

(* Preserve allocation order without repeating formula construction or
   normalization. Every handle is rebound to the new arena's owner. *)
let copy a =
  let b = create a.signature in
  let term (T (_, id)) = T (b.owner, id) and formula (F (_, id)) = F (b.owner, id) in
  for id = 0 to Terms.length a.terms - 1 do
    let copied =
      Terms.intern b.terms
        (match Terms.get a.terms id with
        | (Bound _ | Free _) as node -> node
        | Apply (s, ts) -> Apply (s, List.map term ts))
    in
    assert (copied = id)
  done;
  let copy_formulas map =
    for id = 0 to Formulas.length a.formulas - 1 do
      let copied = Formulas.intern b.formulas (map (Formulas.get a.formulas id)) in
      assert (copied = id)
    done
  in
  copy_formulas (function
    | (True | False) as node -> node
    | Pred (s, ts) -> Pred (s, List.map term ts)
    | Eq (x, y) -> Eq (term x, term y)
    | Not f -> Not (formula f)
    | And fs -> And (List.map formula fs)
    | Or fs -> Or (List.map formula fs)
    | Forall f -> Forall (formula f)
    | Exists f -> Exists (formula f));
  b

let term_view a (T (o, i)) =
  if o <> a.owner then invalid_arg "Source: foreign term arena";
  Terms.get a.terms i

let view a (F (o, i)) =
  if o <> a.owner then invalid_arg "Source: foreign formula arena";
  Formulas.get a.formulas i

let term a n = T (a.owner, Terms.intern a.terms n)
let formula a n = F (a.owner, Formulas.intern a.formulas n)

let bound a i =
  if i < 0 then invalid_arg "negative bound index";
  term a (Bound i)

let free a i =
  if i < 0 then invalid_arg "negative free index";
  term a (Free i)

let apply a s ts =
  Signature.check_function a.signature s (List.length ts);
  List.iter (fun t -> ignore (term_view a t)) ts;
  term a (Apply (s, ts))

let truth a = formula a True
let falsity a = formula a False

let pred a s ts =
  Signature.check_predicate a.signature s (List.length ts);
  List.iter (fun t -> ignore (term_view a t)) ts;
  formula a (Pred (s, ts))

let member a x y = pred a "member" [ x; y ]

let eq a x y =
  ignore (term_view a x);
  ignore (term_view a y);
  formula a (Eq (x, y))

(* Boolean normalization works on shallow, arena-local handles. The extracted
   merge sort retains exactly the former ID order without copying whole ASTs. *)
let boolean_id a (F (owner, id)) =
  if owner <> a.owner then invalid_arg "Source: foreign formula arena";
  id

let boolean_view a id =
  let handle (F (_, id)) = id in
  match Formulas.get a.formulas id with
  | True -> Source_checker.BTrue
  | False -> BFalse
  | Not f -> BNot (handle f)
  | And fs -> BAnd (List.map handle fs)
  | Or fs -> BOr (List.map handle fs)
  | Pred _ | Eq _ | Forall _ | Exists _ -> BKeep id

let boolean_result a = function
  | Source_checker.BTrue -> truth a
  | BFalse -> falsity a
  | BKeep id -> F (a.owner, id)
  | BNot id -> formula a (Not (F (a.owner, id)))
  | BAnd ids -> formula a (And (List.map (fun id -> F (a.owner, id)) ids))
  | BOr ids -> formula a (Or (List.map (fun id -> F (a.owner, id)) ids))

let not_ a f = Source_checker.boolean_not (boolean_view a) (boolean_id a f) |> boolean_result a

let and_ a fs =
  Source_checker.boolean_and (boolean_view a) (List.map (boolean_id a) fs) |> boolean_result a

let or_ a fs =
  Source_checker.boolean_or (boolean_view a) (List.map (boolean_id a) fs) |> boolean_result a

let implies a f g = or_ a [ not_ a f; g ]
let iff a f g = and_ a [ implies a f g; implies a g f ]

let well_scoped a ~depth f =
  let rec t d x =
    match term_view a x with
    | Bound i -> i < d
    | Free _ -> true
    | Apply (_, ts) -> List.for_all (t d) ts
  in
  let rec go d f =
    match view a f with
    | True | False -> true
    | Pred (_, ts) -> List.for_all (t d) ts
    | Eq (x, y) -> t d x && t d y
    | Not g -> go d g
    | And fs | Or fs -> List.for_all (go d) fs
    | Forall g | Exists g -> go (d + 1) g
  in
  depth >= 0 && go depth f

let quant a depth node f =
  if depth < 0 || not (well_scoped a ~depth:(depth + 1) f) then
    invalid_arg "Source: dangling De Bruijn index";
  formula a (node f)

let forall a ~depth f = quant a depth (fun f -> Forall f) f
let exists a ~depth f = quant a depth (fun f -> Exists f) f

let rec shift_term a ~delta ~cutoff x =
  match term_view a x with
  | Bound i when i >= cutoff ->
      if i + delta < cutoff then invalid_arg "Source.shift_term: index escapes scope";
      bound a (i + delta)
  | Bound _ | Free _ -> x
  | Apply (s, ts) -> apply a s (List.map (shift_term a ~delta ~cutoff) ts)

(* Abstraction and substitution are extracted from Rocq. These bridges only
   preserve the constructors and symbols; the usual arena builders retain
   sharing and Boolean normalization. *)
let rec checked_term a t =
  match term_view a t with
  | Bound i -> Wire_types.B i
  | Free i -> Wire_types.F i
  | Apply (s, ts) -> Wire_types.App (s, List.map (checked_term a) ts)

let rec checked_formula a f =
  match view a f with
  | True -> Wire_types.Top
  | False -> Wire_types.Bot
  | Pred (s, ts) -> Wire_types.Pred (s, List.map (checked_term a) ts)
  | Eq (x, y) -> Wire_types.Eq (checked_term a x, checked_term a y)
  | Not f -> Wire_types.Neg (checked_formula a f)
  | And fs -> Wire_types.Conj (List.map (checked_formula a) fs)
  | Or fs -> Wire_types.Disj (List.map (checked_formula a) fs)
  | Forall f -> Wire_types.All (checked_formula a f)
  | Exists f -> Wire_types.Ex (checked_formula a f)

let rec from_checked_term a = function
  | Wire_types.B i -> bound a i
  | Wire_types.F i -> free a i
  | Wire_types.App (s, ts) -> apply a s (List.map (from_checked_term a) ts)

let rec from_checked_formula a = function
  | Wire_types.Top -> truth a
  | Wire_types.Bot -> falsity a
  | Wire_types.Pred (s, ts) -> pred a s (List.map (from_checked_term a) ts)
  | Wire_types.Eq (x, y) -> eq a (from_checked_term a x) (from_checked_term a y)
  | Wire_types.Neg f -> not_ a (from_checked_formula a f)
  | Wire_types.Conj fs -> and_ a (List.map (from_checked_formula a) fs)
  | Wire_types.Disj fs -> or_ a (List.map (from_checked_formula a) fs)
  | Wire_types.All f -> formula a (Forall (from_checked_formula a f))
  | Wire_types.Ex f -> formula a (Exists (from_checked_formula a f))

let bind a v f =
  if v < 0 then invalid_arg "Source.bind: negative free variable";
  checked_formula a f |> Source_checker.bind_formula 0 v |> from_checked_formula a

let subst_free a v replacement f =
  if v < 0 then invalid_arg "Source.subst_free: negative free variable";
  let replacement = checked_term a replacement in
  checked_formula a f |> Source_checker.substitute_formula 0 v replacement |> from_checked_formula a

let all a vs f = List.fold_right (fun v f -> forall a ~depth:0 (bind a v f)) vs f
let ex a vs f = List.fold_right (fun v f -> exists a ~depth:0 (bind a v f)) vs f

let free_vars a f =
  let vars = ref [] and terms = Hashtbl.create 16 and formulas = Hashtbl.create 16 in
  let rec term t =
    if not (Hashtbl.mem terms t) then (
      Hashtbl.add terms t ();
      match term_view a t with
      | Free v -> vars := v :: !vars
      | Apply (_, ts) -> List.iter term ts
      | Bound _ -> ())
  in
  let rec visit f =
    if not (Hashtbl.mem formulas f) then (
      Hashtbl.add formulas f ();
      match view a f with
      | True | False -> ()
      | Pred (_, ts) -> List.iter term ts
      | Eq (x, y) ->
          term x;
          term y
      | Not f | Forall f | Exists f -> visit f
      | And fs | Or fs -> List.iter visit fs)
  in
  visit f;
  List.sort_uniq compare !vars

let close a f = all a (free_vars a f) f
let is_closed a f = well_scoped a ~depth:0 f && free_vars a f = []

let rec size a f =
  match view a f with
  | True | False | Pred _ | Eq _ -> 1
  | Not f | Forall f | Exists f -> 1 + size a f
  | And fs | Or fs -> 1 + List.fold_left (fun n f -> n + size a f) 0 fs

let to_string a f =
  let rec term env t =
    match term_view a t with
    | Bound i -> ( try List.nth env i with Failure _ -> "#" ^ string_of_int i)
    | Free i -> if i = 0 then "x" else if i = 1 then "y" else "p" ^ string_of_int i
    | Apply (s, []) -> s
    | Apply (s, ts) -> s ^ "(" ^ String.concat ", " (List.map (term env) ts) ^ ")"
  in
  let rec go env f =
    match view a f with
    | True -> "true"
    | False -> "false"
    | Pred ("member", [ x; y ]) -> term env x ^ " in " ^ term env y
    | Pred (s, ts) -> s ^ "(" ^ String.concat ", " (List.map (term env) ts) ^ ")"
    | Eq (x, y) -> term env x ^ " = " ^ term env y
    | Not f -> "not (" ^ go env f ^ ")"
    | And fs -> "(" ^ String.concat " and " (List.map (go env) fs) ^ ")"
    | Or fs -> "(" ^ String.concat " or " (List.map (go env) fs) ^ ")"
    | Forall f -> q env "forall" f
    | Exists f -> q env "exists" f
  and q env op f =
    let x = "b" ^ string_of_int (List.length env) in
    op ^ " " ^ x ^ ". (" ^ go (x :: env) f ^ ")"
  in
  go [] f

let counts a = (Terms.length a.terms, Formulas.length a.formulas)
