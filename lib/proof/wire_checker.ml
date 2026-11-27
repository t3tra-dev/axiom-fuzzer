
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y



(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
 end

type literal = bool * Rocq_checker.atom

(** val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec forallb2 test xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs0 ->
    (match ys with
     | [] -> false
     | y :: ys0 -> (&&) (test x y) (forallb2 test xs0 ys0))

(** val variable_equal : (int * int) -> (int * int) -> bool **)

let variable_equal x y =
  (&&) ((=) (fst x) (fst y)) ((=) (snd x) (snd y))

(** val symbol_equal :
    ('a1 -> 'a1 -> bool) -> 'a1 Source_checker.wire_symbol -> 'a1
    Source_checker.wire_symbol -> bool **)

let symbol_equal equal_function x y =
  match x with
  | Source_checker.Original f ->
    (match y with
     | Source_checker.Original g -> equal_function f g
     | Source_checker.Skolem (_, _) -> false)
  | Source_checker.Skolem (a, i) ->
    (match y with
     | Source_checker.Original _ -> false
     | Source_checker.Skolem (b, j) ->
       (&&) ((&&) ((<=) 0 a) ((<=) 0 i)) (variable_equal (a, i) (b, j)))

(** val predicate_equal :
    ('a1 -> 'a1 -> bool) -> 'a1 Source_checker.wire_predicate -> 'a1
    Source_checker.wire_predicate -> bool **)

let predicate_equal equal_predicate x y =
  match x with
  | Source_checker.Named p ->
    (match y with
     | Source_checker.Named q -> equal_predicate p q
     | Source_checker.Auxiliary _ -> false)
  | Source_checker.Auxiliary i ->
    (match y with
     | Source_checker.Named _ -> false
     | Source_checker.Auxiliary j ->
       (&&) ((&&) ((<=) 0 (fst i)) ((<=) 0 (snd i))) (variable_equal i j))

(** val encoded_term :
    ('a1 -> 'a1 -> bool) -> ((int * int) -> int) -> (int -> 'a1
    Source_checker.wire_symbol option) -> 'a1 Source_checker.wire_term ->
    Rocq_checker.term -> bool **)

let rec encoded_term equal_function encode_variable decode_function t numeric =
  match t with
  | Source_checker.V v ->
    (match numeric with
     | Rocq_checker.Var n ->
       (&&) ((&&) ((&&) ((<=) 0 (fst v)) ((<=) 0 (snd v))) ((<=) 0 n))
         ((=) (encode_variable v) n)
     | Rocq_checker.Fun (_, _) -> false)
  | Source_checker.Fn (s, ts) ->
    (match numeric with
     | Rocq_checker.Var _ -> false
     | Rocq_checker.Fun (n, args) ->
       (&&) ((<=) 0 n)
         (match decode_function n with
          | Some decoded ->
            (&&) (symbol_equal equal_function s decoded)
              (forallb2
                (encoded_term equal_function encode_variable decode_function)
                ts args)
          | None -> false))

(** val encoded_predicate :
    ('a1 -> 'a1 -> bool) -> (int -> 'a1 Source_checker.wire_predicate option)
    -> 'a1 Source_checker.wire_predicate -> int -> bool **)

let encoded_predicate equal_predicate decode_predicate p n =
  (&&) ((<=) 0 n)
    (match decode_predicate n with
     | Some decoded -> predicate_equal equal_predicate p decoded
     | None -> false)

(** val encoded_atom :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) ->
    (int -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
    Source_checker.wire_predicate option) -> ('a1, 'a2)
    Source_checker.wire_atom -> Rocq_checker.atom -> bool **)

let encoded_atom equal_function equal_predicate encode_variable decode_function decode_predicate a numeric =
  match a with
  | Source_checker.P (p, ts) ->
    (match numeric with
     | Rocq_checker.Pred (n, args) ->
       (&&)
         (encoded_predicate equal_predicate decode_predicate
           (Source_checker.Named p) n)
         (forallb2
           (encoded_term equal_function encode_variable decode_function) ts
           args)
     | Rocq_checker.Eq0 (_, _) -> false)
  | Source_checker.E (x, y) ->
    (match numeric with
     | Rocq_checker.Pred (_, _) -> false
     | Rocq_checker.Eq0 (u, v) ->
       (&&) (encoded_term equal_function encode_variable decode_function x u)
         (encoded_term equal_function encode_variable decode_function y v))
  | Source_checker.D (id, ts) ->
    (match numeric with
     | Rocq_checker.Pred (n, args) ->
       (&&)
         (encoded_predicate equal_predicate decode_predicate
           (Source_checker.Auxiliary id) n)
         (forallb2
           (encoded_term equal_function encode_variable decode_function) ts
           args)
     | Rocq_checker.Eq0 (_, _) -> false)

(** val encoded_literal :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) ->
    (int -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
    Source_checker.wire_predicate option) -> ('a1, 'a2)
    Source_checker.wire_literal -> literal -> bool **)

let encoded_literal equal_function equal_predicate encode_variable decode_function decode_predicate l numeric =
  (&&) (eqb ((fun l -> l.Source_checker.positive) l) (fst numeric))
    (encoded_atom equal_function equal_predicate encode_variable
      decode_function decode_predicate ((fun l -> l.Source_checker.atom) l)
      (snd numeric))

(** val encoded_clause :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) ->
    (int -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
    Source_checker.wire_predicate option) -> ('a1, 'a2)
    Source_checker.wire_literal list -> literal list -> bool **)

let encoded_clause equal_function equal_predicate encode_variable decode_function decode_predicate =
  forallb2
    (encoded_literal equal_function equal_predicate encode_variable
      decode_function decode_predicate)

(** val encoded_inputs :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ((int * int) -> int) ->
    (int -> 'a1 Source_checker.wire_symbol option) -> (int -> 'a2
    Source_checker.wire_predicate option) -> ('a1, 'a2)
    Source_checker.wire_literal list list -> literal list list -> bool **)

let encoded_inputs equal_function equal_predicate encode_variable decode_function decode_predicate =
  forallb2
    (encoded_clause equal_function equal_predicate encode_variable
      decode_function decode_predicate)
