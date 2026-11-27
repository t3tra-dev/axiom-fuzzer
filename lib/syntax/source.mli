type t
(** Source terms and formulas cannot contain search-only Skolem symbols. IDs are abstract, distinct,
    and carry arena ownership. *)

type term
type formula
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

val create : Signature.t -> t

val copy : t -> t
(** Copy hash-cons storage in allocation order, with a fresh owner and independent mutable tables.
    Existing handles are not portable to the copy. *)

val signature : t -> Signature.t
val term_view : t -> term -> term_node
val view : t -> formula -> formula_node
val bound : t -> int -> term
val free : t -> int -> term
val apply : t -> string -> term list -> term
val truth : t -> formula
val falsity : t -> formula
val pred : t -> string -> term list -> formula
val member : t -> term -> term -> formula
val eq : t -> term -> term -> formula
val not_ : t -> formula -> formula
val and_ : t -> formula list -> formula
val or_ : t -> formula list -> formula
val implies : t -> formula -> formula -> formula
val iff : t -> formula -> formula -> formula
val forall : t -> depth:int -> formula -> formula
val exists : t -> depth:int -> formula -> formula
val all : t -> int list -> formula -> formula
val ex : t -> int list -> formula -> formula
val shift_term : t -> delta:int -> cutoff:int -> term -> term
val subst_free : t -> int -> term -> formula -> formula
val well_scoped : t -> depth:int -> formula -> bool
val free_vars : t -> formula -> int list
val close : t -> formula -> formula
val is_closed : t -> formula -> bool
val size : t -> formula -> int
val to_string : t -> formula -> string
val counts : t -> int * int
