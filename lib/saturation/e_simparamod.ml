open Wire
(** E 3.5.9's simultaneous paramodulation (pm_type ParamodSim) for the E-loop members
    ({!Heuristic.loop.sim_paramod}).

    E builds a paramodulant from the from clause [C | l = r] and the into clause [D] with the into
    subterm [s] ([sigma = mgu(l, s)]) by ClauseSimParamodConstruct (CLAUSES/ccl_paramod.c): every
    literal of [D] is copied with every occurrence of [s] replaced by [sigma(r)] (EqnListCopyRepl;
    TBInsertRepl compares the shared term cell of [s] before dereferencing, so these are the
    syntactic occurrences of [s] in the uninstantiated [D]: every literal, both sides of an
    equation, whether or not the position could take part in an inference; the occurs check keeps
    [s] out of the bindings of [D]'s variables), followed by [sigma(C)] unchanged; resolved and
    repeated literals go. With the given clause as the from clause (ComputeIntoParamodulants),
    compute_into_pm_pos_clause visits the into clause's positions of one into term in ascending
    order and stops after the first conclusion, so E makes one conclusion per from position, into
    clause and into subterm; with the given clause as the into clause (ComputeFromParamodulants)
    every into position of the given makes its own conclusion, the same clause for each occurrence
    of a term.

    Here such a paramodulant is a chain of ordinary Paramodulate steps: a plain paramodulation at
    one occurrence, then one step per further occurrence, from the same from clause into the
    previous result, with the substitution that maps the from clause onto the instance already in
    that result, so that its side literals repeat and normalization merges them. Every intermediate
    is a proof-only node; the kernel checks each step as it checks any paramodulation, so the
    certificate format and the trusted base are unchanged. A search-side choice only. *)

(** The occurrences of the non-variable term [s] in [c], as (literal index, path) pairs in literal
    order and preorder (paths as in [Paramodulate]: an equation's side or a predicate's argument
    first). No occurrence lies inside another. *)
let occurrences (s : term) (c : clause) =
  let found = ref [] in
  let rec visit j rev_path t =
    if Clause.compare_term t s = 0 then found := (j, List.rev rev_path) :: !found
    else
      match t with V _ -> () | Fn (_, ts) -> List.iteri (fun k u -> visit j (k :: rev_path) u) ts
  in
  List.iteri
    (fun j (l : literal) -> List.iteri (fun a t -> visit j [ a ] t) (Clause.atom_terms l.atom))
    c;
  List.rev !found

exception Repeated

(** Whether the non-variable term [s] occurs more than once in [c] (the only case in which a
    simultaneous paramodulant differs from the plain one), without allocating. *)
let repeated (s : term) (c : clause) =
  let seen = ref false in
  let rec visit t =
    if Clause.compare_term t s = 0 then if !seen then raise Repeated else seen := true
    else match t with V _ -> () | Fn (_, ts) -> List.iter visit ts
  in
  match
    List.iter
      (fun (l : literal) ->
        match l.atom with
        | P (_, ts) | D (_, ts) -> List.iter visit ts
        | E (a, b) ->
            visit a;
            visit b)
      c
  with
  | () -> false
  | exception Repeated -> true

(* An idempotent substitution (the unifier's snapshot, or a chain step's). *)
let apply sigma =
  let rec go = function
    | V v as t -> ( match List.assoc_opt v sigma with Some u -> u | None -> t)
    | Fn (f, ts) -> Fn (f, List.map go ts)
  in
  go

exception Unrenamed

(** [Clause.normalize c] with the renaming of [c]'s variables it applies (first occurrence in the
    sorted clause), as an association list from [c]'s variables to the normalized ones. *)
let normalize_renaming c =
  let sorted = List.sort_uniq Clause.compare_literal c in
  let renamed = Clause.rename_variables sorted in
  let pairs = ref [] in
  let rec zip a b =
    match (a, b) with
    | V v, V w -> if not (List.mem_assoc v !pairs) then pairs := (v, w) :: !pairs
    | Fn (_, xs), Fn (_, ys) -> List.iter2 zip xs ys
    | _ -> invalid_arg "E_simparamod.normalize_renaming"
  in
  List.iter2
    (fun (l : literal) (m : literal) ->
      List.iter2 zip (Clause.atom_terms l.atom) (Clause.atom_terms m.atom))
    sorted renamed;
  (List.sort_uniq Clause.compare_literal renamed, !pairs)

(* A term of the clause just recorded in the variables of its stored (normalized) form, moved to
   scope 2: the into clause of the next step. *)
let into_scope pairs =
  Clause.map_vars (fun v ->
      match List.assoc_opt v pairs with Some (_, i) -> V (2, i) | None -> raise Unrenamed)

let equal_literal (a : literal) (b : literal) = Clause.compare_literal a b = 0

(* One replacement of a chain on the current forms of the into clause's literals ([into_side]): the
   literal [jb] at the path [pb] becomes [put l pb rhs]. The other literals in the same current
   form share one normalized literal: one with an occurrence at the same path is replaced with it
   (taken out of [pending]); one without would be lost (E keeps both) unless a side literal of the
   from clause ([from_side]) repeats it. Returns the pending occurrences left, or [None] when a
   literal would be lost. *)
let replace_one ~from_side ~rhs into_side (jb, pb) pending =
  let l = into_side.(jb) in
  let pending = ref pending and lost = ref false and also = ref [] in
  Array.iteri
    (fun k m ->
      if k <> jb && equal_literal m l then
        if List.mem (k, pb) !pending then (
          pending := List.filter (fun o -> o <> (k, pb)) !pending;
          also := k :: !also)
        else if not (List.exists (equal_literal l) from_side) then lost := true)
    into_side;
  if !lost then None
  else
    let replaced = Clause.put l pb rhs in
    List.iter (fun k -> into_side.(k) <- replaced) (jb :: !also);
    Some !pending

type outcome =
  | Plain  (** The into subterm occurs once: the inference's own conclusion is E's. *)
  | Simultaneous of { clause : clause; rule : rule; steps : int }
      (** The chain's last step, to be emitted in place of the inference's conclusion, and the
          number of intermediates recorded before it. *)
  | Fallback of int
      (** Two literals that the substitution makes equal would need different replacements in every
          order of the chain, which the merged literal of a normalized intermediate cannot carry (E
          keeps both): the inference's own conclusion stands. The number of intermediates recorded
          (0 unless a chain had to stop). *)

(** The simultaneous paramodulant of [rule] =
    [Paramodulate (from.id, i, reverse, into.id, j, path, sigma)] with the conclusion [clause] (as
    {!Calculus.paramodulate} emits it); [record] stores an intermediate as a proof-only node and
    returns it. The chain starts at the inference's own position when no literal is lost that way,
    else at the first other occurrence that loses none. *)
let chain ~record ~(from : step) ~(into : step) (clause : clause) rule =
  match rule with
  | Paramodulate (p, i, reverse, q, j, path, sigma)
    when p = from.id && q = into.id
         && repeated (Clause.at (List.nth into.clause j) path) into.clause -> (
      let xs = Clause.scope 1 from.clause and ys = Clause.scope 2 into.clause in
      let s = Clause.at (List.nth ys j) path in
      let found = occurrences s ys in
      match (found, (List.nth xs i).atom) with
      | ([] | [ _ ]), _ | _, (P _ | D _) -> Plain
      | _, E (a, b) -> (
          let lhs, rhs = if reverse then (b, a) else (a, b) in
          let app = apply sigma in
          let plain (j, path) =
            List.map (Clause.map_literal app)
              (Clause.remove i xs @ Clause.replace j (Clause.put (List.nth ys j) path rhs) ys)
          in
          let own = plain (j, path) in
          if List.compare_lengths own clause <> 0 || not (List.for_all2 equal_literal own clause)
          then Plain
          else
            let from_side = List.map (Clause.map_literal app) (Clause.remove i xs) in
            let instance = Array.of_list (List.map (Clause.map_literal app) ys) in
            let rhs' = app rhs in
            (* Whether the chain in this order loses no literal: the first step replaces one
               occurrence in the into clause itself, the others meet the merged literals. *)
            let feasible = function
              | [] -> false
              | (j1, p1) :: rest ->
                  let current = Array.copy instance in
                  current.(j1) <- Clause.put current.(j1) p1 rhs';
                  let rec go pending =
                    match pending with
                    | [] -> true
                    | o :: rest -> (
                        match replace_one ~from_side ~rhs:rhs' current o rest with
                        | None -> false
                        | Some rest -> go rest)
                  in
                  go rest
            in
            let others = List.filter (fun o -> o <> (j, path)) found in
            let orders =
              ((j, path) :: others)
              :: List.map (fun o -> o :: List.filter (fun o' -> o' <> o) found) others
            in
            match List.find_opt feasible orders with
            | None | Some [] -> Fallback 0
            | Some ((j1, p1) :: pending) ->
                let first, first_rule =
                  if (j1, p1) = (j, path) then (clause, rule)
                  else (plain (j1, p1), Paramodulate (p, i, reverse, q, j1, p1, sigma))
                in
                (* The current forms of the from clause's side literals and of each literal of the
                   into clause, and the from clause's instance, in the variables of [raw]. *)
                let into_side = Array.copy instance in
                into_side.(j1) <- Clause.put into_side.(j1) p1 rhs';
                let inst = List.map (fun v -> (v, app (V v))) (Wire.variables xs) in
                let rec go raw rule from_side inst pending recorded =
                  match pending with
                  | [] -> Simultaneous { clause = raw; rule; steps = recorded }
                  | ((jb, pb) as o) :: rest -> (
                      let node : step = record raw rule in
                      let _, pairs = normalize_renaming raw in
                      match
                        let rename = into_scope pairs in
                        let from_side = List.map (Clause.map_literal rename) from_side in
                        Array.iteri
                          (fun k l -> into_side.(k) <- Clause.map_literal rename l)
                          into_side;
                        (from_side, List.map (fun (v, t) -> (v, rename t)) inst)
                      with
                      | exception Unrenamed -> Fallback (recorded + 1)
                      | from_side, inst -> (
                          let current = Clause.scope 2 node.clause in
                          let l = into_side.(jb) in
                          let rec find k = function
                            | [] -> None
                            | m :: more -> if equal_literal m l then Some k else find (k + 1) more
                          in
                          match find 0 current with
                          | Some index
                            when Clause.compare_term (Clause.at l pb) (apply inst lhs) = 0 -> (
                              match
                                replace_one ~from_side ~rhs:(apply inst rhs) into_side o rest
                              with
                              | None -> Fallback (recorded + 1)
                              | Some rest ->
                                  let sigma = List.sort compare inst in
                                  let app = apply sigma in
                                  let raw =
                                    List.map (Clause.map_literal app)
                                      (Clause.remove i xs
                                      @ Clause.replace index
                                          (Clause.put (List.nth current index) pb rhs)
                                          current)
                                  in
                                  go raw
                                    (Paramodulate (p, i, reverse, node.id, index, pb, sigma))
                                    from_side inst rest (recorded + 1))
                          | _ -> Fallback (recorded + 1)))
                in
                go first first_rule from_side inst pending 0))
  | _ -> Plain
