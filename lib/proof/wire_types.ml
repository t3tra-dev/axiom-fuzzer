(** Shared portable Source data. Rocq extraction uses these constructors directly; no arena or
    syntax translation lies on the acceptance path. *)
type 'f source_term = B of int | F of int | App of 'f * 'f source_term list

type ('f, 'p) source_formula =
  | Top
  | Bot
  | Pred of 'p * 'f source_term list
  | Eq of 'f source_term * 'f source_term
  | Neg of ('f, 'p) source_formula
  | Conj of ('f, 'p) source_formula list
  | Disj of ('f, 'p) source_formula list
  | All of ('f, 'p) source_formula
  | Ex of ('f, 'p) source_formula

type source = (string, string) source_formula

type schema =
  | Comprehension
  | Separation
  | Replacement
  | Unrestricted_separation
  | Registered of string * string

type origin =
  | Fixed of string
  | Instance of schema * source
  | Imported of string
  | Registered_instance of string * string * string

type axiom = { axiom_id : int; name : string; origin : origin; formula : source }

(** Finite data for the independently checked natural-deduction branch. *)
type code = Number of int | Pair of code * code
