type change = { operator : string; path : int list; formula : Wire.source }

val size : Wire.source -> int

val mutations : ?closed:bool -> Wire.source -> change Seq.t
(** Deterministic single-site edits. Closed axioms remain closed. Each call returns a fresh stream;
    edits are proposals, not logical equivalences. *)

val shrinks : Wire.source -> change Seq.t
(** Strictly smaller conditions, including capture-avoiding binder removal. *)

val snapshot : ?observations:int -> Theory.t -> Wire.axiom list
(** Fixed axioms and a bounded number of observations per schema. *)

type mutant = { axiom_id : int; change : change; problem : string }

val theories : Wire.axiom list -> mutant Seq.t
(** Each TPTP problem is a separate mutated finite theory, with no authority inherited from its
    original axiom metadata. *)
