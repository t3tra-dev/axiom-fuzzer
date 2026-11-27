open Wire
(** Exact alpha-variant checks after a coarse, renaming-invariant bucket key. A bijection is
    required; unification or one-way matching is insufficient. *)

exception Mismatch
exception Exhausted

let renaming ?(budget = 2000) ?(symmetric = false) c d =
  if List.length c <> List.length d then None
  else
    let left = ref budget in
    let rec term ((forward, backward) as env) x y =
      match (x, y) with
      | V x, V y -> (
          match (List.assoc_opt x forward, List.assoc_opt y backward) with
          | None, None -> ((x, y) :: forward, (y, x) :: backward)
          | Some y', Some x' when x = x' && y = y' -> env
          | _ -> raise Mismatch)
      | Fn (f, xs), Fn (g, ys) when Sym.equal f g && List.compare_lengths xs ys = 0 ->
          List.fold_left2 term env xs ys
      | _ -> raise Mismatch
    in
    let atom env p t =
      match (p, t) with
      | P (p, xs), P (q, ys) when Sym.name p q && List.compare_lengths xs ys = 0 ->
          List.fold_left2 term env xs ys
      | D (p, xs), D (q, ys) when Sym.def p q && List.compare_lengths xs ys = 0 ->
          List.fold_left2 term env xs ys
      | E (x, y), E (u, v) -> term (term env x u) y v
      | _ -> raise Mismatch
    in
    let rec search env patterns targets =
      match patterns with
      | [] -> Some (fst env)
      | p :: ps ->
          List.find_map
            (fun (j, t) ->
              decr left;
              if !left < 0 then raise Exhausted;
              if p.positive <> t.positive then None
              else
                let attempt target =
                  try search (atom env p.atom target) ps (Clause.remove j targets)
                  with Mismatch -> None
                in
                match attempt t.atom with
                | Some _ as found -> found
                | None -> (
                    match t.atom with E (u, v) when symmetric -> attempt (E (v, u)) | _ -> None))
            (List.mapi (fun j t -> (j, t)) targets)
    in
    try search ([], []) c d with Exhausted -> None

let variants ?budget c d = Option.is_some (renaming ?budget ~symmetric:true c d)

type t = clause list Tbl.Clause_ints.t

let create () = Tbl.Clause_ints.create 128

(* The renaming-invariant bucket key: each literal's own normal form (an equation in its smaller
   orientation) and the sorted occurrence counts of the variables. A single literal normalizes by
   renaming alone, and the counts form a multiset, so neither needs a table. *)
let key c =
  let counts = ref [] in
  let rec visit = function
    | V v ->
        let rec bump = function
          | [] -> counts := (v, ref 1) :: !counts
          | ((w : variable), n) :: rest ->
              if Int.equal (fst w) (fst v) && Int.equal (snd w) (snd v) then incr n else bump rest
        in
        bump !counts
    | Fn (_, ts) -> List.iter visit ts
  in
  let shape l =
    List.iter visit (Clause.atom_terms l.atom);
    let canonical l = List.hd (Clause.rename_variables [ l ]) in
    let normal = canonical l in
    match l.atom with
    | E (x, y) ->
        let other = canonical { l with atom = E (y, x) } in
        if Clause.compare_literal normal other <= 0 then normal else other
    | _ -> normal
  in
  let shapes = List.map shape c |> List.sort Clause.compare_literal in
  (shapes, List.map (fun (_, n) -> !n) !counts |> List.sort Int.compare)

let mem ?(guard = fun () -> ()) t c =
  let bucket = Option.value ~default:[] (Tbl.Clause_ints.find_opt t (key c)) in
  List.exists
    (fun d ->
      guard ();
      variants c d)
    bucket

let add t c =
  let k = key c in
  Tbl.Clause_ints.replace t k (c :: Option.value ~default:[] (Tbl.Clause_ints.find_opt t k))
