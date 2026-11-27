type t

val create : unit -> t
val add : t -> Wire.clause -> Wire.rule -> Wire.step
val get : t -> int -> Wire.step

val length : t -> int
(** Monotone next ID; reclaimed IDs are never reused. *)

val stored : t -> int
val steps : t -> Wire.step list

val statistics : Wire.certificate -> int * int
(** Proof steps and axioms; AVATAR includes both FO and Boolean steps. *)

val reclaim : t -> int list -> int
(** Keep roots and all transitive proof ancestors. Return reclaimed node count. Call only between
    inferences, with every live search root supplied. *)

val reclaim_with : ?dropped:(int -> unit) -> t -> ((int -> unit) -> unit) -> int
(** [reclaim] with the roots given as [roots push], which passes every root to [push]: the same
    nodes are kept, without a list of the roots. [dropped] is called with each node it drops. *)

val reclaim_list : t -> int list -> int
(** The previous implementation of [reclaim] (a list of roots and a [Stack]): the reference of the
    unit tests. *)

val extract :
  ?cnf_mode:Wire.cnf_mode ->
  ?avatar:Wire.avatar_certificate ->
  t ->
  theory:string ->
  axioms:Wire.axiom list ->
  root:int ->
  Wire.certificate

val prune : Wire.certificate -> Wire.certificate
val used_axioms : Wire.certificate -> Wire.axiom list
