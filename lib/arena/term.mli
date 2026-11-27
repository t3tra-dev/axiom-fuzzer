type t
type arena
type node = Var of Wire.variable | App of Wire.symbol * t list

val create : unit -> arena
val view : arena -> t -> node
val var : arena -> Wire.variable -> t
val app : arena -> Wire.symbol -> t list -> t
val of_wire : arena -> Wire.term -> t
val to_wire : arena -> t -> Wire.term
val compare : t -> t -> int
val equal : t -> t -> bool
val count : arena -> int

val clear : arena -> unit
(** Invalidate all old handles; only portable Wire terms survive this boundary. *)
