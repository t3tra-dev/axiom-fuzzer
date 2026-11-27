type 'a t
(** Append-only, structurally hash-consed storage. Hash collisions are compared structurally by
    [Hashtbl]; a hash alone never establishes identity. *)

val create : unit -> 'a t
val intern : 'a t -> 'a -> int
val get : 'a t -> int -> 'a
val length : 'a t -> int
val clear : 'a t -> unit

module type S = sig
  type node
  type t

  val create : unit -> t
  val intern : t -> node -> int
  val get : t -> int -> node
  val length : t -> int
  val clear : t -> unit
end

(** The same storage with a monomorphic node table: [N.hash] must agree with [N.equal]. *)
module Make (N : Hashtbl.HashedType) : S with type node = N.t
