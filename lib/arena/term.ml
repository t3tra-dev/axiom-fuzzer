type t = T of int * int
type node = Var of Wire.variable | App of Wire.symbol * t list

let equal (T (o1, i1)) (T (o2, i2)) = Int.equal i1 i2 && Int.equal o1 o2

module Nodes = Arena.Make (struct
  type t = node

  let rec handles xs ys =
    match (xs, ys) with
    | [], [] -> true
    | x :: xs, y :: ys -> equal x y && handles xs ys
    | _ -> false

  let equal a b =
    match (a, b) with
    | Var x, Var y -> Sym.var x y
    | App (f, xs), App (g, ys) -> Sym.equal f g && handles xs ys
    | _ -> false

  let hash = function
    | Var (s, i) -> Tbl.Hash.(finish (mix (mix (mix seed 3) s) i))
    | App (f, ts) ->
        let open Tbl.Hash in
        finish (List.fold_left (fun h (T (o, i)) -> mix (mix h o) i) (symbol seed f) ts)
end)

module Handles = Hashtbl.Make (struct
  type nonrec t = t

  let equal = equal
  let hash (T (o, i)) = Tbl.Hash.(finish (mix (mix seed o) i))
end)

type arena = { mutable owner : int; nodes : Nodes.t; wire : Wire.term Handles.t }

let owners = Atomic.make 0

let create () =
  { owner = Atomic.fetch_and_add owners 1; nodes = Nodes.create (); wire = Handles.create 256 }

let view a (T (owner, i)) =
  if owner <> a.owner then invalid_arg "Term: foreign arena";
  Nodes.get a.nodes i

let make a n = T (a.owner, Nodes.intern a.nodes n)

let var a ((s, i) as v) =
  if s < 0 || i < 0 then invalid_arg "Term: negative variable";
  make a (Var v)

let app a s ts =
  List.iter (fun t -> ignore (view a t)) ts;
  make a (App (s, ts))

let rec of_wire a = function
  | Wire.V v -> var a v
  | Wire.Fn (s, ts) -> app a s (List.map (of_wire a) ts)

let rec to_wire a t =
  match Handles.find_opt a.wire t with
  | Some wire -> wire
  | None ->
      let wire =
        match view a t with Var v -> Wire.V v | App (s, ts) -> Wire.Fn (s, List.map (to_wire a) ts)
      in
      Handles.add a.wire t wire;
      wire

let compare = Stdlib.compare
let count a = Nodes.length a.nodes

let clear a =
  a.owner <- Atomic.fetch_and_add owners 1;
  Nodes.clear a.nodes;
  Handles.reset a.wire
