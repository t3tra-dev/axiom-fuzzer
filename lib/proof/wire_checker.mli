
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2



val eqb : bool -> bool -> bool

module Nat :
 sig
 end

type literal = bool * Rocq_checker.atom

val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val variable_equal : (int * int) -> (int * int) -> bool

val symbol_equal :
  ('a1 -> 'a1 -> bool) -> 'a1 Source_checker.wire_symbol -> 'a1
  Source_checker.wire_symbol -> bool

val predicate_equal :
  ('a1 -> 'a1 -> bool) -> 'a1 Source_checker.wire_predicate -> 'a1
  Source_checker.wire_predicate -> bool

val encoded_term :
  ('a1 -> 'a1 -> bool) -> ((int * int) -> int) -> (int -> 'a1
  Source_checker.wire_symbol option) -> 'a1 Source_checker.wire_term ->
  Rocq_checker.term -> bool

val encoded_predicate :
  ('a1 -> 'a1 -> bool) -> (int -> 'a1 Source_checker.wire_predicate option) ->
  'a1 Source_checker.wire_predicate -> int -> bool

val encoded_atom :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) -> (int
  -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
  Source_checker.wire_predicate option) -> ('a1, 'a2) Source_checker.wire_atom
  -> Rocq_checker.atom -> bool

val encoded_literal :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) -> (int
  -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
  Source_checker.wire_predicate option) -> ('a1, 'a2)
  Source_checker.wire_literal -> literal -> bool

val encoded_clause :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) -> (int
  -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
  Source_checker.wire_predicate option) -> ('a1, 'a2)
  Source_checker.wire_literal list -> literal list -> bool

val encoded_inputs :
  ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) -> (int
  -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
  Source_checker.wire_predicate option) -> ('a1, 'a2)
  Source_checker.wire_literal list list -> literal list list -> bool
