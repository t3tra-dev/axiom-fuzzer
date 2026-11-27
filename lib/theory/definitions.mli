type t

val create : Signature.t -> t
(** An immutable environment of acyclic, transparent abbreviations over a finite signature. Base
    symbols cannot be redefined. *)

val signature : t -> Signature.t
val base_signature : t -> Signature.t

val predicate : ?budget:int -> t -> name:string -> arity:int -> Wire.source -> t
(** Free indices 0..arity-1 are formal parameters. Bodies may refer to earlier declarations only. No
    existence/uniqueness assumption is introduced. *)

val function_ : ?budget:int -> t -> name:string -> arity:int -> Wire.source_term -> t
(** Explicit term definitions; implicit functions and recursive definitions are rejected. *)

val expand : ?budget:int -> t -> Wire.source -> Wire.source
(** Capture-avoiding simultaneous expansion into the base language. Preserves free parameters and
    checks scope, arities and a finite expansion budget. *)
