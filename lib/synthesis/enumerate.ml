(** Lazy finite levels. Each level is finite even when the signature has functions. The unbounded
    diagonal grows both syntax and parameter budget. *)
let singleton = Seq.return

let concat = List.to_seq |> fun of_list xs -> Seq.flat_map Fun.id (of_list xs)

let rec product = function
  | [] -> singleton []
  | xs :: rest -> Seq.flat_map (fun x -> Seq.map (fun ys -> x :: ys) (product rest)) xs

let rec compositions total count =
  if count = 0 then if total = 0 then [ [] ] else []
  else if total < count then []
  else
    List.init (total - count + 1) (fun k -> k + 1)
    |> List.concat_map (fun n ->
        List.map (fun rest -> n :: rest) (compositions (total - n) (count - 1)))

let rec terms a ~free ~depth size () =
  let variables =
    if size = 1 then
      List.init free (Source.free a) @ List.init depth (Source.bound a) |> List.to_seq
    else Seq.empty
  in
  let applications =
    Source.signature a |> Signature.functions |> List.to_seq
    |> Seq.flat_map (fun (symbol, arity) ->
        compositions (size - 1) arity
        |> List.to_seq
        |> Seq.flat_map (fun sizes ->
            product (List.map (terms a ~free ~depth) sizes) |> Seq.map (Source.apply a symbol)))
  in
  Seq.append variables applications ()

let rec formulas a ~free ~depth size () =
  if size <= 0 then Seq.Nil
  else
    let atoms =
      List.map (fun (s, n) -> (Some s, n)) (Signature.predicates (Source.signature a))
      @ [ (None, 2) ]
      |> List.to_seq
      |> Seq.flat_map (fun (symbol, arity) ->
          compositions (size - 1 + arity) arity
          |> List.to_seq
          |> Seq.flat_map (fun sizes ->
              product (List.map (terms a ~free ~depth) sizes)
              |> Seq.map (fun ts ->
                  match (symbol, ts) with
                  | None, [ x; y ] -> Source.eq a x y
                  | Some symbol, _ -> Source.pred a symbol ts
                  | _ -> assert false)))
    in
    let constants =
      if size = 1 then List.to_seq [ Source.truth a; Source.falsity a ] else Seq.empty
    in
    let unary =
      if size < 2 then Seq.empty
      else
        concat
          [
            Seq.map (Source.not_ a) (formulas a ~free ~depth (size - 1));
            Seq.map (Source.forall a ~depth) (formulas a ~free ~depth:(depth + 1) (size - 1));
            Seq.map (Source.exists a ~depth) (formulas a ~free ~depth:(depth + 1) (size - 1));
          ]
    in
    let binary =
      if size < 3 then Seq.empty
      else
        List.init (size - 2) (fun i -> i + 1)
        |> List.to_seq
        |> Seq.flat_map (fun n ->
            Seq.flat_map
              (fun x ->
                Seq.flat_map
                  (fun y -> List.to_seq [ Source.and_ a [ x; y ]; Source.or_ a [ x; y ] ])
                  (formulas a ~free ~depth (size - 1 - n)))
              (formulas a ~free ~depth n))
    in
    concat [ atoms; constants; unary; binary ] ()

(* Cooperative interruption of one stream step. A step of [bounded]/[exhaustive] may pass over
   many raw candidates before it returns: [unique] drops repeats, and a registered schema built on
   these streams usually keeps only its admissible conditions. Whoever forces a step under a
   deadline installs its guard with [with_guard]; every [poll_stride]-th raw candidate polls it
   before the candidate enters [unique]'s table, so the guard may raise to abandon the step; for a
   stream that only filters or maps [unique]'s output (no memoizing or counting combinator in
   between), forcing the same node again later yields the same element. The scheduler, the script
   reference and the probe lane's look-ahead never force an abandoned step again. The stride keeps
   the guard's clock read (about 60 ns) below 0.2% of the cost of a raw candidate. The default
   guard does nothing. Guards are Domain-local. *)
let guard_key : (unit -> unit) Domain.DLS.key = Domain.DLS.new_key (fun () -> ignore)
let poll () = Domain.DLS.get guard_key ()
let poll_stride = 16

let with_guard guard f =
  let previous = Domain.DLS.get guard_key in
  Domain.DLS.set guard_key guard;
  Fun.protect ~finally:(fun () -> Domain.DLS.set guard_key previous) f

let unique seq =
  let seen = Hashtbl.create 256 and candidates = ref 0 in
  Seq.filter
    (fun f ->
      incr candidates;
      if !candidates mod poll_stride = 0 then poll ();
      if Hashtbl.mem seen f then false
      else (
        Hashtbl.add seen f ();
        true))
    seq

let bounded a ~arity ~parameters ~max_size =
  if Signature.is_unrestricted (Source.signature a) then
    invalid_arg "Enumerate: formula synthesis requires a finite signature";
  if arity < 0 || parameters < 0 || max_size < 0 then invalid_arg "Enumerate: negative bound";
  List.init max_size (fun i -> i + 1)
  |> List.to_seq
  |> Seq.flat_map (formulas a ~free:(arity + parameters) ~depth:0)
  |> unique

let exhaustive a ~arity =
  if Signature.is_unrestricted (Source.signature a) then
    invalid_arg "Enumerate: formula synthesis requires a finite signature";
  Seq.ints 1
  |> Seq.flat_map (fun diagonal ->
      List.init diagonal Fun.id |> List.to_seq
      |> Seq.flat_map (fun parameters ->
          formulas a ~free:(arity + parameters) ~depth:0 (diagonal - parameters)))
  |> unique
