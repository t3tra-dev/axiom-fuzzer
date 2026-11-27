type t = {
  arena : Term.arena;
  bindings : Term.t Tbl.Pair.t;
  mutable trail : Wire.variable list;
  mutable length : int;
  guard : unit -> unit;
}
(** Only the searcher uses this mutable unifier. The replay kernel applies and checks the supplied
    substitution, without invoking unification. *)

let create ?(guard = fun () -> ()) arena =
  { arena; bindings = Tbl.Pair.create 32; trail = []; length = 0; guard }

let mark u = u.length

let rollback u mark =
  if mark < 0 || mark > u.length then invalid_arg "Unify.rollback";
  while u.length > mark do
    match u.trail with
    | [] -> assert false
    | v :: rest ->
        Tbl.Pair.remove u.bindings v;
        u.trail <- rest;
        u.length <- u.length - 1
  done

let rec deref u t =
  u.guard ();
  match Term.view u.arena t with
  | Var v -> ( match Tbl.Pair.find_opt u.bindings v with None -> t | Some t -> deref u t)
  | App _ -> t

let rec occurs u v t =
  match Term.view u.arena (deref u t) with
  | Var w -> Sym.var v w
  | App (_, ts) -> List.exists (occurs u v) ts

let bind u v t =
  if occurs u v t then false
  else (
    Tbl.Pair.add u.bindings v t;
    u.trail <- v :: u.trail;
    u.length <- u.length + 1;
    true)

let rec unify u s t =
  let s = deref u s and t = deref u t in
  Term.equal s t
  ||
  match (Term.view u.arena s, Term.view u.arena t) with
  | Var v, _ -> bind u v t
  | _, Var v -> bind u v s
  | App (f, ss), App (g, ts) ->
      Sym.equal f g && List.length ss = List.length ts && List.for_all2 (unify u) ss ts

let rec apply u t =
  u.guard ();
  match Term.view u.arena (deref u t) with
  | Var v -> Wire.V v
  | App (s, ts) -> Wire.Fn (s, List.map (apply u) ts)

let capture u =
  Tbl.Pair.fold (fun v t acc -> (v, apply u t) :: acc) u.bindings [] |> List.sort compare

(* A necessary condition only: variables are wildcards, including repeated ones.
   Reject incompatible symbols before interning either term. *)
let rec compatible x y =
  match (x, y) with
  | Wire.V _, _ | _, Wire.V _ -> true
  | Wire.Fn (f, xs), Wire.Fn (g, ys) ->
      Sym.equal f g && List.length xs = List.length ys && List.for_all2 compatible xs ys

let solve ?accept u equations k =
  let m = mark u in
  (* The optional read-only filter runs while bindings are live. Its application
     function must not escape or reenter the unifier. Only accepted inferences
     need an immutable substitution; the emitting callback still runs after rollback. *)
  let rec apply_live = function
    | Wire.V v as term -> (
        u.guard ();
        match Tbl.Pair.find_opt u.bindings v with None -> term | Some t -> apply u t)
    | Wire.Fn (s, ts) ->
        u.guard ();
        Wire.Fn (s, List.map apply_live ts)
  in
  let solved =
    Fun.protect
      ~finally:(fun () -> rollback u m)
      (fun () ->
        if
          List.for_all
            (fun (x, y) ->
              compatible x y && unify u (Term.of_wire u.arena x) (Term.of_wire u.arena y))
            equations
          && match accept with None -> true | Some accept -> accept apply_live
        then Some (capture u)
        else None)
  in
  Option.iter
    (fun sigma ->
      (* Callbacks may immediately factor an emitted clause using this unifier.
       Release the trail first, and give them an immutable, idempotent snapshot. *)
      let rec apply_snapshot = function
        | Wire.V v as t ->
            u.guard ();
            Option.value ~default:t (Sym.assoc_opt v sigma)
        | Wire.Fn (s, ts) ->
            u.guard ();
            Wire.Fn (s, List.map apply_snapshot ts)
      in
      k sigma apply_snapshot)
    solved
