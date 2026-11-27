type 'a t = { table : ('a, int) Hashtbl.t; mutable data : 'a option array; mutable used : int }

let create () = { table = Hashtbl.create 256; data = Array.make 64 None; used = 0 }

let intern a node =
  match Hashtbl.find_opt a.table node with
  | Some id -> id
  | None ->
      if a.used = Array.length a.data then (
        let data = Array.make (2 * a.used) None in
        Array.blit a.data 0 data 0 a.used;
        a.data <- data);
      let id = a.used in
      a.data.(id) <- Some node;
      a.used <- id + 1;
      Hashtbl.add a.table node id;
      id

let get a id =
  if id < 0 || id >= a.used then invalid_arg "Arena.get";
  Option.get a.data.(id)

let length a = a.used

let clear a =
  Hashtbl.reset a.table;
  a.data <- Array.make 64 None;
  a.used <- 0

module type S = sig
  type node
  type t

  val create : unit -> t
  val intern : t -> node -> int
  val get : t -> int -> node
  val length : t -> int
  val clear : t -> unit
end

(* The same storage with a monomorphic node table (explicit hash and
   equality) for hot search-side arenas. *)
module Make (N : Hashtbl.HashedType) = struct
  module H = Hashtbl.Make (N)

  type node = N.t
  type t = { table : int H.t; mutable data : node option array; mutable used : int }

  let create () = { table = H.create 256; data = Array.make 64 None; used = 0 }

  let intern a node =
    match H.find_opt a.table node with
    | Some id -> id
    | None ->
        if a.used = Array.length a.data then (
          let data = Array.make (2 * a.used) None in
          Array.blit a.data 0 data 0 a.used;
          a.data <- data);
        let id = a.used in
        a.data.(id) <- Some node;
        a.used <- id + 1;
        H.add a.table node id;
        id

  let get a id =
    if id < 0 || id >= a.used then invalid_arg "Arena.get";
    Option.get a.data.(id)

  let length a = a.used

  (* Empty again, as [create] leaves it: [H.reset] keeps or restores the initial bucket array, and
     the initial data array is refilled rather than allocated again. *)
  let clear a =
    H.reset a.table;
    if Array.length a.data = 64 then Array.fill a.data 0 64 None else a.data <- Array.make 64 None;
    a.used <- 0
end
