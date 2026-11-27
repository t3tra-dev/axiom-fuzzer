(** Portable, allocation-independent proof syntax. No executable payloads. *)
type 'f symbol_repr = 'f Source_checker.wire_symbol = Original of 'f | Skolem of int * int

type symbol = string symbol_repr
type variable = int * int

type 'f term_repr = 'f Source_checker.wire_term =
  | V of variable
  | Fn of 'f symbol_repr * 'f term_repr list

type term = string term_repr

type ('f, 'p) atom_repr = ('f, 'p) Source_checker.wire_atom =
  | P of 'p * 'f term_repr list
  | E of 'f term_repr * 'f term_repr
  | D of (int * int) * 'f term_repr list

type atom = (string, string) atom_repr

type ('f, 'p) literal_repr = ('f, 'p) Source_checker.wire_literal = {
  positive : bool;
  atom : ('f, 'p) atom_repr;
}

type literal = (string, string) literal_repr
type clause = literal list
type substitution = (variable * term) list

type 'f source_term_repr = 'f Wire_types.source_term =
  | B of int
  | F of int
  | App of 'f * 'f source_term_repr list

type source_term = string source_term_repr

type ('f, 'p) source_repr = ('f, 'p) Wire_types.source_formula =
  | Top
  | Bot
  | Pred of 'p * 'f source_term_repr list
  | Eq of 'f source_term_repr * 'f source_term_repr
  | Neg of ('f, 'p) source_repr
  | Conj of ('f, 'p) source_repr list
  | Disj of ('f, 'p) source_repr list
  | All of ('f, 'p) source_repr
  | Ex of ('f, 'p) source_repr

type source = (string, string) source_repr

type schema = Wire_types.schema =
  | Comprehension
  | Separation
  | Replacement
  | Unrestricted_separation
  | Registered of string * string

type origin = Wire_types.origin =
  | Fixed of string
  | Instance of schema * source
  | Imported of string
  | Registered_instance of string * string * string

type axiom = Wire_types.axiom = { axiom_id : int; name : string; origin : origin; formula : source }

let schema_name = function
  | Comprehension -> "comprehension"
  | Separation -> "separation"
  | Replacement -> "replacement"
  | Unrestricted_separation -> "unrestricted-separation"
  | Registered (name, _) -> name

let is_instance = function Instance _ | Registered_instance _ -> true | _ -> false

type rule =
  | Input of int * int
  | Component of int
  | Resolve of int * int * int * int * substitution
  | Factor of int * int * int * substitution
  | Equality_resolve of int * int * substitution
  | Equality_factor of int * int * bool * int * bool * substitution
  | Paramodulate of int * int * bool * int * int * int list * substitution

type step = { id : int; clause : clause; rule : rule }
type boolean_rule = Split of int | Conflict of int | Boolean_resolve of int * int * int
type boolean_step = { boolean_id : int; boolean_clause : int list; boolean_rule : boolean_rule }

type avatar_certificate = {
  components : clause list;
  splits : (int * int list) list;
  boolean_steps : boolean_step list;
  boolean_root : int;
}

type cnf_mode = Distributive | Definitional | Hybrid

(* Shared by search and independent reconstruction of the current CNF policy. *)
let hybrid_cnf_limit = 32

let cnf_mode_name = function
  | Distributive -> "distributive"
  | Definitional -> "definitional"
  | Hybrid -> "hybrid"

let cnf_mode_of_string = function
  | "distributive" -> Distributive
  | "definitional" -> Definitional
  | "hybrid" -> Hybrid
  | _ -> invalid_arg "CNF mode must be distributive, definitional, or hybrid"

type certificate = {
  natural : Wire_types.code option;
  avatar : avatar_certificate option;
  cnf_mode : cnf_mode;
  theory : string;
  axioms : axiom list;
  steps : step list;
  root : int;
}

let parents = function
  | Input _ | Component _ -> []
  | Factor (p, _, _, _) | Equality_resolve (p, _, _) | Equality_factor (p, _, _, _, _, _) -> [ p ]
  | Resolve (p, _, q, _, _) | Paramodulate (p, _, _, q, _, _, _) -> [ p; q ]

let rule_substitution = function
  | Input _ | Component _ -> []
  | Resolve (_, _, _, _, s)
  | Factor (_, _, _, s)
  | Equality_resolve (_, _, s)
  | Equality_factor (_, _, _, _, _, s)
  | Paramodulate (_, _, _, _, _, _, s) ->
      s

let variables c =
  let rec term acc = function V v -> v :: acc | Fn (_, ts) -> List.fold_left term acc ts in
  List.fold_left
    (fun acc l ->
      match l.atom with
      | P (_, ts) | D (_, ts) -> List.fold_left term acc ts
      | E (x, y) -> term (term acc x) y)
    [] c
  |> List.sort_uniq compare

let rec export_term a t =
  match Source.term_view a t with
  | Bound i -> B i
  | Free i -> F i
  | Apply (s, ts) -> App (s, List.map (export_term a) ts)

let rec export a f =
  match Source.view a f with
  | True -> Top
  | False -> Bot
  | Pred (s, ts) -> Pred (s, List.map (export_term a) ts)
  | Eq (x, y) -> Eq (export_term a x, export_term a y)
  | Not g -> Neg (export a g)
  | And fs -> Conj (List.map (export a) fs)
  | Or fs -> Disj (List.map (export a) fs)
  | Forall g -> All (export a g)
  | Exists g -> Ex (export a g)

let rec import_term a = function
  | B i -> Source.bound a i
  | F i -> Source.free a i
  | App (s, ts) -> Source.apply a s (List.map (import_term a) ts)

(* Validate the raw input before arena simplification can erase a bad branch.
   Natural-number extraction assumes nonnegative machine integers. *)
let checked_source_term ?(guard = fun () -> ()) t =
  let rec visit = function
    | B i | F i ->
        guard ();
        if i < 0 then invalid_arg "negative source index"
    | App (_, ts) ->
        guard ();
        List.iter visit ts
  in
  visit t;
  t

let checked_source ?(guard = fun () -> ()) f =
  let term t = ignore (checked_source_term ~guard t) in
  let rec visit f =
    guard ();
    match f with
    | Top | Bot -> ()
    | Pred (_, ts) -> List.iter term ts
    | Eq (x, y) ->
        term x;
        term y
    | Neg f | All f | Ex f -> visit f
    | Conj fs | Disj fs -> List.iter visit fs
  in
  visit f;
  f

let source_term_of_checked t = t
let source_of_checked f = f

let source_scoped ?(closed = false) f =
  try Source_checker.formula_scoped 0 closed (checked_source f) with Invalid_argument _ -> false

let import a f =
  if not (source_scoped f) then invalid_arg "Wire.import: dangling or negative variable";
  let rec go depth = function
    | Top -> Source.truth a
    | Bot -> Source.falsity a
    | Pred (s, ts) -> Source.pred a s (List.map (import_term a) ts)
    | Eq (x, y) -> Source.eq a (import_term a x) (import_term a y)
    | Neg f -> Source.not_ a (go depth f)
    | Conj fs -> Source.and_ a (List.map (go depth) fs)
    | Disj fs -> Source.or_ a (List.map (go depth) fs)
    | All f -> Source.forall a ~depth (go (depth + 1) f)
    | Ex f -> Source.exists a ~depth (go (depth + 1) f)
  in
  let result = go 0 f in
  if not (Source.well_scoped a ~depth:0 result) then invalid_arg "Wire.import: dangling variable";
  result

let symbol_string = function Original s -> s | Skolem (a, n) -> Printf.sprintf "sk_%d_%d" a n

let rec term_string = function
  | V (0, i) -> "v" ^ string_of_int i
  | V (s, i) -> Printf.sprintf "v%d_%d" s i
  | Fn (s, []) -> symbol_string s
  | Fn (s, ts) -> symbol_string s ^ "(" ^ String.concat "," (List.map term_string ts) ^ ")"

let atom_string = function
  | P ("member", [ x; y ]) -> term_string x ^ " in " ^ term_string y
  | P (p, ts) -> p ^ "(" ^ String.concat "," (List.map term_string ts) ^ ")"
  | E (x, y) -> term_string x ^ " = " ^ term_string y
  | D ((a, i), ts) ->
      Printf.sprintf "def_%d_%d(%s)" a i (String.concat "," (List.map term_string ts))

let literal_string l = (if l.positive then "" else "~") ^ "(" ^ atom_string l.atom ^ ")"
let clause_string c = if c = [] then "BOTTOM" else String.concat " | " (List.map literal_string c)
