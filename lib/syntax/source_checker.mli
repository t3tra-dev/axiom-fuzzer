
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val eqb : bool -> bool -> bool

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module Nat :
 sig
  val max : int -> int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val nth_error : 'a1 list -> int -> 'a1 option

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

module Sort :
 functor (X:TotalLeBool') ->
 sig
  val merge : X.t list -> X.t list -> X.t list

  val merge_list_to_stack :
    X.t list option list -> X.t list -> X.t list option list

  val merge_stack : X.t list option list -> X.t list

  val iter_merge : X.t list option list -> X.t list -> X.t list

  val sort : X.t list -> X.t list

  val flatten_stack : X.t list option list -> X.t list
 end

val term_scoped : int -> bool -> 'a1 Wire_types.source_term -> bool

val formula_scoped :
  int -> bool -> ('a1, 'a2) Wire_types.source_formula -> bool

val bind_term :
  int -> int -> 'a1 Wire_types.source_term -> 'a1 Wire_types.source_term

val bind_formula :
  int -> int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val lift_term :
  int -> 'a1 Wire_types.source_term -> 'a1 Wire_types.source_term

val substitute_term :
  int -> int -> 'a1 Wire_types.source_term -> 'a1 Wire_types.source_term ->
  'a1 Wire_types.source_term

val substitute_formula :
  int -> int -> 'a1 Wire_types.source_term -> ('a1, 'a2)
  Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula

type boolean_node =
| BTrue
| BFalse
| BKeep of int
| BNot of int
| BAnd of int list
| BOr of int list

module HandleOrder :
 sig
  type t = int

  val leb : int -> int -> bool
 end

module HandleSort :
 sig
  val merge : int list -> int list -> int list

  val merge_list_to_stack :
    int list option list -> int list -> int list option list

  val merge_stack : int list option list -> int list

  val iter_merge : int list option list -> int list -> int list

  val sort : int list -> int list

  val flatten_stack : int list option list -> int list
 end

val unique_after : int -> int list -> int list

val unique_sorted : int list -> int list

val sort_handles : int list -> int list

val flatten_and : (int -> boolean_node) -> int list -> int list

val flatten_or : (int -> boolean_node) -> int list -> int list

val is_false : (int -> boolean_node) -> int -> bool

val is_true : (int -> boolean_node) -> int -> bool

val boolean_not : (int -> boolean_node) -> int -> boolean_node

val boolean_and : (int -> boolean_node) -> int list -> boolean_node

val boolean_or : (int -> boolean_node) -> int list -> boolean_node

type schema_kind =
| Comprehension
| Separation
| Replacement
| UnrestrictedSeparation

val schema_arity : schema_kind -> int

val term_parameters_below : int -> 'a1 Wire_types.source_term -> bool

val parameters_below : int -> ('a1, 'a2) Wire_types.source_formula -> bool

val implication :
  ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula
  -> ('a1, 'a2) Wire_types.source_formula

val equivalence :
  ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula
  -> ('a1, 'a2) Wire_types.source_formula

val all_free :
  int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val ex_free :
  int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val close_parameters :
  int list -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val replacement_unique :
  int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val replacement_functional :
  int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val replacement_image :
  'a2 -> int -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2)
  Wire_types.source_formula

val schema_core :
  schema_kind -> 'a2 -> int -> ('a1, 'a2) Wire_types.source_formula -> ('a1,
  'a2) Wire_types.source_formula

val expand_schema :
  schema_kind -> 'a2 -> int list -> int -> ('a1, 'a2)
  Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula

val checked_schema :
  schema_kind -> 'a2 -> int list -> int -> ('a1, 'a2)
  Wire_types.source_formula -> ('a1, 'a2) Wire_types.source_formula option

type ('f, 'p) normal =
| NPred of bool * 'p * 'f Wire_types.source_term list
| NEqual of bool * 'f Wire_types.source_term * 'f Wire_types.source_term
| NConj of ('f, 'p) normal list
| NDisj of ('f, 'p) normal list
| NAll of ('f, 'p) normal
| NEx of ('f, 'p) normal

val nnf : bool -> ('a1, 'a2) Wire_types.source_formula -> ('a1, 'a2) normal

val normal_scoped : int -> bool -> ('a1, 'a2) normal -> bool

type 'l matrix =
| MLiteral of 'l
| MConj of 'l matrix list
| MDisj of 'l matrix list

val distribute : 'a1 list list -> 'a1 list list -> 'a1 list list

val product_fits : int -> int -> int -> bool

val bounded_distribute :
  int -> 'a1 list list -> 'a1 list list -> 'a1 list list option

val bounded_identity : int -> 'a1 list list -> 'a1 list list option

val bounded_cnf : (unit -> bool) -> int -> 'a1 matrix -> 'a1 list list option

type 'a definition_literal =
| DBase of bool * 'a
| DAux of bool * int * int list

type 'a definition = { conjunction : bool; arguments : int list;
                       children : 'a definition_literal list }

val opposite : 'a1 definition_literal -> 'a1 definition_literal

val definition_root : int -> 'a1 definition -> 'a1 definition_literal

val definition_clauses :
  int -> 'a1 definition -> 'a1 definition_literal list list

val literal_variables :
  ('a1 -> int list) -> 'a1 definition_literal -> int list

val definition_variables :
  ('a1 -> int list) -> 'a1 definition_literal list -> int list

val literal_before : int -> 'a1 definition_literal -> bool

val definition_valid : ('a1 -> int list) -> int -> 'a1 definition -> bool

val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val valid_prefix :
  (int -> 'a1 definition option) -> ('a1 -> int list) -> int -> bool

val match_connective :
  (int -> 'a1 definition option) -> bool -> ('a1 definition_literal list ->
  bool) -> int -> 'a1 definition_literal -> bool

val matches_matrix :
  (int -> 'a1 definition option) -> ('a1 -> 'a1 -> bool) -> int ->
  (bool * 'a1) matrix -> 'a1 definition_literal -> bool

val emit_definitions :
  (int -> 'a1 definition option) -> (unit -> bool) -> int -> int -> int -> 'a1
  definition_literal list list option

val checked_definitions :
  (int -> 'a1 definition option) -> (unit -> bool) -> ('a1 -> 'a1 -> bool) ->
  ('a1 -> int list) -> int -> int -> (bool * 'a1) matrix -> 'a1
  definition_literal -> 'a1 definition_literal list list option

val map_option : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option

val instantiate_bound :
  (unit -> bool) -> ('a1 -> 'a2 list -> 'a2) -> 'a2 list -> 'a1
  Wire_types.source_term -> 'a2 option

type 'l universal =
| ULiteral of 'l
| UConj of 'l universal list
| UDisj of 'l universal list
| UAll of int * 'l universal

val scope_list : (int -> 'a1 -> int option) -> int -> 'a1 list -> int option

val erase_universals : 'a1 universal -> 'a1 matrix

val universal_scope :
  ('a1 -> int list) -> int list -> int -> int -> 'a1 universal -> int option

val checked_universals :
  ('a1 -> int list) -> int -> 'a1 universal -> 'a1 matrix option

type 'x supplied = { supplied_value : 'x; next_variable : int;
                     next_symbol : int }

val supply : 'a1 -> int -> int -> 'a1 supplied

val map_supply :
  (int -> int -> 'a1 -> 'a2 supplied option) -> int -> int -> 'a1 list -> 'a2
  list supplied option

val eliminate_quantifiers :
  (unit -> bool) -> ('a1 -> 'a3 list -> 'a3) -> (int -> 'a3) -> (int -> 'a3
  list -> 'a3) -> (bool -> 'a2 -> 'a3 list -> 'a4) -> (bool -> 'a3 -> 'a3 ->
  'a4) -> int -> 'a3 list -> 'a3 list -> int -> int -> ('a1, 'a2) normal ->
  'a4 universal supplied option

type 'f wire_symbol =
| Original of 'f
| Skolem of int * int

type 'pT wire_predicate =
| Named of 'pT
| Auxiliary of (int * int)

type 'f wire_term =
| V of (int * int)
| Fn of 'f wire_symbol * 'f wire_term list

type ('f, 'pT) wire_atom =
| P of 'pT * 'f wire_term list
| E of 'f wire_term * 'f wire_term
| D of (int * int) * 'f wire_term list

type ('f, 'pT) wire_literal = { positive : bool; atom : ('f, 'pT) wire_atom }

val term_indices_acc : 'a1 wire_term -> int list -> int list

val atom_indices_acc : ('a1, 'a2) wire_atom -> int list

val wire_support : ('a1, 'a2) wire_atom -> int list

val local_variable : (int * int) -> bool

val wire_term_local : 'a1 wire_term -> bool

val wire_base_valid : ('a1, 'a2) wire_atom -> bool

val checked_wire_support : ('a1, 'a2) wire_atom -> int list option

val wire_quantifiers :
  (unit -> bool) -> int -> int -> ('a1, 'a2) normal -> (bool * ('a1, 'a2)
  wire_atom) universal supplied option

val wire_universal_scope :
  (unit -> bool) -> int list -> int -> int -> (bool * ('a1, 'a2) wire_atom)
  universal -> int option

val wire_checked_universals :
  (unit -> bool) -> int -> (bool * ('a1, 'a2) wire_atom) universal ->
  (bool * ('a1, 'a2) wire_atom) matrix option

val pack_literal : (bool * ('a1, 'a2) wire_atom) -> ('a1, 'a2) wire_literal

val wire_distributive_cnf :
  (unit -> bool) -> int -> (bool * ('a1, 'a2) wire_atom) matrix -> ('a1, 'a2)
  wire_literal list list option

val wire_definition_valid : ('a1, 'a2) wire_atom definition_literal -> bool

val wire_lookup :
  (int -> ('a1, 'a2) wire_atom definition option) -> int -> ('a1, 'a2)
  wire_atom definition option

val wire_definitions_valid :
  (int -> ('a1, 'a2) wire_atom definition option) -> int -> bool

val pack_definition :
  int -> ('a1, 'a2) wire_atom definition_literal -> ('a1, 'a2) wire_literal

val wire_definitional_cnf :
  (int -> ('a1, 'a2) wire_atom definition option) -> (unit -> bool) -> (('a1,
  'a2) wire_atom -> ('a1, 'a2) wire_atom -> bool) -> int -> int -> int ->
  (bool * ('a1, 'a2) wire_atom) matrix -> ('a1, 'a2) wire_atom
  definition_literal -> ('a1, 'a2) wire_literal list list option

type formula = (string, string) Wire_types.source_formula

type term = string Wire_types.source_term

val term_equal : term -> term -> bool

val formula_equal : formula -> formula -> bool

val deduplicate : formula list -> formula list

val and_parts : formula -> formula list

val or_parts : formula -> formula list

val is_bottom : formula -> bool

val is_top : formula -> bool

val smart_and : formula list -> (string, string) Wire_types.source_formula

val smart_or : formula list -> (string, string) Wire_types.source_formula

val smart_not : formula -> (string, string) Wire_types.source_formula

val simplify : formula -> formula

val formula_identical : formula -> formula -> bool

val equivalent : formula -> formula -> bool

val symbol_present : (string * int) list -> string -> int -> bool

val term_signature : (string * int) list -> term -> bool

val formula_signature :
  (string * int) list -> (string * int) list -> formula -> bool

val term_parameters : term -> int list

val formula_parameters : formula -> int list

val builtin : Wire_types.schema -> schema_kind option

val schema_equal : Wire_types.schema -> Wire_types.schema -> bool

val admitted : Wire_types.schema list -> Wire_types.schema -> bool

type theory = { theory_name : string; unrestricted_signature : bool;
                function_symbols : (string * int) list;
                predicate_symbols : (string * int) list;
                fixed_axioms : Wire_types.axiom list;
                allowed_schemas : Wire_types.schema list;
                registered_check : (string -> string -> string -> formula ->
                                   bool) }

val signature_ok : theory -> formula -> bool

val fixed_origin_equal : Wire_types.origin -> Wire_types.origin -> bool

val schema_expansion :
  int -> schema_kind -> formula -> (string, string) Wire_types.source_formula
  option

val validate_axiom : int -> theory -> Wire_types.axiom -> bool
