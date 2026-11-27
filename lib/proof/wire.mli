(** Portable proof data. Source syntax cannot contain Skolem or auxiliary symbols; proof terms share
    the Rocq-extracted representation. *)
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

val schema_name : schema -> string
val is_instance : origin -> bool

type rule =
  | Input of int * int
  | Component of int
  | Resolve of int * int * int * int * substitution
  | Factor of int * int * int * substitution
  | Equality_resolve of int * int * substitution
  | Equality_factor of int * int * bool * int * bool * substitution
  | Paramodulate of int * int * bool * int * int * int list * substitution

type step = { id : int; clause : clause; rule : rule }

type boolean_rule =
  | Split of int
  | Conflict of int
  | Boolean_resolve of int * int * int
      (** Resolution stores the two earlier Boolean step IDs and the zero-based component ID. *)

type boolean_step = { boolean_id : int; boolean_clause : int list; boolean_rule : boolean_rule }
(** Boolean literals are signed [component ID + 1]; zero is invalid. *)

type avatar_certificate = {
  components : clause list;
  splits : (int * int list) list;
  boolean_steps : boolean_step list;
  boolean_root : int;
}
(** Components use shared alpha representatives with disjoint variables. Each split lists a parent
    FO step and component IDs. Replay checks an instance of the parent before checking their union.
*)

type cnf_mode = Distributive | Definitional | Hybrid

type certificate = {
  natural : Wire_types.code option;
  avatar : avatar_certificate option;
  cnf_mode : cnf_mode;
  theory : string;
  axioms : axiom list;
  steps : step list;
  root : int;
}

val hybrid_cnf_limit : int
(** Current CNF threshold shared by search and independent reconstruction. *)

val cnf_mode_name : cnf_mode -> string
val cnf_mode_of_string : string -> cnf_mode
val parents : rule -> int list
val rule_substitution : rule -> substitution

val variables : clause -> variable list
(** Distinct scoped variables in lexicographic order. No renaming is performed. *)

val export_term : Source.t -> Source.term -> source_term
val export : Source.t -> Source.formula -> source
val import_term : Source.t -> source_term -> Source.term
val import : Source.t -> source -> Source.formula
val checked_source_term : ?guard:(unit -> unit) -> source_term -> string Wire_types.source_term
val checked_source : ?guard:(unit -> unit) -> source -> (string, string) Wire_types.source_formula
val source_term_of_checked : string Wire_types.source_term -> source_term
val source_of_checked : (string, string) Wire_types.source_formula -> source
val source_scoped : ?closed:bool -> source -> bool
val symbol_string : symbol -> string
val term_string : term -> string
val atom_string : atom -> string
val literal_string : literal -> string
val clause_string : clause -> string
