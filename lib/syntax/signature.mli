type t

val make : functions:(string * int) list -> predicates:(string * int) list -> t
val sets : t

val unrestricted : t
(** Countable vocabulary of all string names and finite arities. A symbol is identified by its name
    and arity. The finite lists below are empty; use an axiom enumerator instead of the
    finite-signature formula generator. *)

val is_unrestricted : t -> bool
val functions : t -> (string * int) list
val predicates : t -> (string * int) list
val check_function : t -> string -> int -> unit
val check_predicate : t -> string -> int -> unit
