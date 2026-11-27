open Wire
(** E 3.5.9's creation order of a given clause's conclusions (CONTROL/cco_proofproc.c
    generate_new_clauses), which is their evaluation order and so E's tie-break between equally
    evaluated clauses (ccl_neweval.c EvalCompare, the evaluation counter of eval_clause_set): the
    clauses that backward simplification moved to tmp_store first, then the equality factors, the
    equality resolvents, the paramodulants with the given clause as the "from" clause
    (ComputeIntoParamodulants), then those with the given clause as the "into" clause
    (ComputeFromParamodulants, cco_paramodulation.c). Resolution is E's superposition of P(s) =
    $true into P(t) != $true, so a resolvent is a paramodulant of the given's positive atom (from)
    or into the given's negative atom (into).

    Within each paramodulation phase E pops the given's positions from a stack, so it visits them in
    reverse of their collection order (ccl_overlap_index.c ClauseCollectFromTermsPos: each literal's
    lterm then, unoriented, its rterm; ClauseCollectIntoTermsPos: the non-variable subterms of each
    literal's lterm in preorder, then those of an unoriented rterm). For each position it finds the
    partner subterms through the FP7 fingerprint index (TERMS/cte_fp_index.c fp_index_rek_find_unif
    pushes compatible leaves depth first; they are popped in reverse), and within a leaf it visits
    the partner clauses in creation order (CmpClauseTPosCells by perm_ident) and their positions in
    ascending order. [key] gives every conclusion its place in that order; the engine emits a
    given's conclusions sorted by it (Heuristic.loop.gen_order). A search-order choice only: the
    conclusions and their certificates are the same. Approximations: our literal order stands for
    E's (exact for unit clauses), an unoriented equation's left side for E's lterm, and the partner
    clause's id for E's term and clause identifiers. *)

(* E's FP7 sample values (cte_idx_fp.h). *)
let below_var = -2
let any_var = -1
let not_in_term = 0

(* TermFPSampleFO along [path] (argument indices). *)
let sample code t path =
  let rec go t = function
    | [] -> (
        match t with V _ -> any_var | Fn (f, ts) -> code (Ordering.Function f, List.length ts))
    | i :: rest -> (
        match t with
        | V _ -> below_var
        | Fn (_, ts) -> ( match List.nth_opt ts i with None -> not_in_term | Some u -> go u rest))
  in
  go t path

(* An atom P(ts) as a term with P at the top. *)
let atom_sample code head ts path =
  match path with
  | [] -> code (head, List.length ts)
  | i :: rest -> (
      match List.nth_opt ts i with None -> not_in_term | Some u -> sample code u rest)

(* IndexFP7Create: epsilon, 0, 1, 0.0, 0.1, 1.0, 1.1. *)
let fp7_paths = [ []; [ 0 ]; [ 1 ]; [ 0; 0 ]; [ 0; 1 ]; [ 1; 0 ]; [ 1; 1 ] ]

type subject = Term of term | Atom of Ordering.head * term list

let fp7 code = function
  | Term t -> List.map (sample code t) fp7_paths
  | Atom (h, ts) -> List.map (atom_sample code h ts) fp7_paths

(* The position of an indexed value in fp_index_rek_find_unif's visit order below a node, for the
   query value [k]: the same symbol, then ANY_VAR, then BELOW_VAR; for NOT_IN_TERM, NOT_IN_TERM then
   BELOW_VAR; for a variable, ANY_VAR, BELOW_VAR, then the symbols in ascending code order. *)
let visit_rank k v =
  if k > 0 then if v = k then 0 else if v = any_var then 1 else 2
  else if k = not_in_term then if v = not_in_term then 0 else 1
  else if v = any_var then 0
  else if v = below_var then 1
  else 2 + v

(* Leaves are pushed in visit order and popped in reverse: a larger rank vector comes first. *)
let leaf_key code query partner =
  List.map2 (fun k v -> -visit_rank k v) (fp7 code query) (fp7 code partner)

let rec nonvar_count = function
  | V _ -> 0
  | Fn (_, ts) -> List.fold_left (fun n t -> n + nonvar_count t) 1 ts

(* Preorder index of [path] among the non-variable subterms of [t] (term_collect_into_terms_pos). *)
let rec preorder t path =
  match (path, t) with
  | [], _ -> 0
  | i :: rest, Fn (_, ts) ->
      let before = List.filteri (fun k _ -> k < i) ts in
      1 + List.fold_left (fun n u -> n + nonvar_count u) 0 before + preorder (List.nth ts i) rest
  | _ -> 0

(* E's lterm side of an equation literal: the greater side when oriented, else the left side. *)
let lterm_side order (s, t) = if Ordering.greater ~order t s then 1 else 0

(* The collection index of an into-position [path] of literal [l] (ClauseCollectIntoTermsPos):
   the lterm's subterms in preorder, then an unoriented rterm's. A predicate atom is the lterm. *)
let into_index order (l : literal) path =
  match (l.atom, path) with
  | (P (_, ts) | D (_, ts)), [] ->
      ignore ts;
      0
  | (P (_, ts) | D (_, ts)), i :: rest ->
      let before = List.filteri (fun k _ -> k < i) ts in
      1 + List.fold_left (fun n u -> n + nonvar_count u) 0 before + preorder (List.nth ts i) rest
  | E (s, t), side :: rest ->
      let lside = lterm_side order (s, t) in
      let term = if side = 0 then s else t in
      if side = lside then preorder term rest
      else nonvar_count (if lside = 0 then s else t) + preorder term rest
  | E _, [] -> 0

(* The collection index of a from-side of literal [l] (ClauseCollectFromTermsPos): the lterm, then
   an unoriented rterm. [reverse]: the side is the right one (Calculus.paramodulate). *)
let from_index order (l : literal) reverse =
  match l.atom with
  | E (s, t) ->
      let side = if reverse then 1 else 0 in
      if side = lterm_side order (s, t) then 0 else 1
  | _ -> 0

let literal (c : clause) i = List.nth c i

let side_subject (l : literal) reverse =
  match l.atom with
  | E (s, t) -> Term (if reverse then t else s)
  | P (p, ts) -> Atom (Ordering.Predicate p, ts)
  | D (d, ts) -> Atom (Ordering.Definition d, ts)

let path_subject (l : literal) path =
  match (l.atom, path) with
  | P (p, ts), [] -> Atom (Ordering.Predicate p, ts)
  | D (d, ts), [] -> Atom (Ordering.Definition d, ts)
  | _, _ -> Term (Clause.at l path)

(** The sort key of a conclusion of the given clause [given] with [rule]; [get] reads a premise,
    [code] gives E's symbol codes (Truth 1). Keys compare lexicographically (Stdlib.compare); a
    stable sort keeps the generation order of equal keys. *)
let key ?rank ~order ~code ~get (given : step) rule =
  let g = given.id in
  let gc = given.clause in
  (* The given's literals in E's order ([rank], Eselection.e_rank) when known. *)
  let r i = match rank with Some a when i < Array.length a -> a.(i) | _ -> i in
  match rule with
  | Equality_factor (_, i, _, j, _, _) -> [ 1; r i; r j ]
  | Factor (_, i, j, _) -> [ 1; r i; r j ]
  | Equality_resolve (_, i, _) -> [ 2; r i ]
  | Paramodulate (p, i, reverse, q, j, path, _) ->
      if p = g then
        (* The given is the "from" clause: its from-side, then the into-partner's subterm. *)
        let l = literal gc i in
        let partner = (get q : step) in
        let pl = literal partner.clause j in
        [ 3; -r i; -from_index order l reverse ]
        @ leaf_key code (side_subject l reverse) (path_subject pl path)
        @ [ q; j; into_index order pl path ]
      else
        (* The given is the "into" clause: its into-position, then the from-partner's side. *)
        let l = literal gc j in
        let partner = (get p : step) in
        let pl = literal partner.clause i in
        [ 4; -r j; -into_index order l path ]
        @ leaf_key code (path_subject l path) (side_subject pl reverse)
        @ [ p; i; from_index order pl reverse ]
  | Resolve (a, i, b, j, _) ->
      (* E's superposition of the positive atom into the negative one. *)
      let own, oi, other, oj = if a = g then (a, i, b, j) else (b, j, a, i) in
      ignore own;
      let l = literal gc oi in
      let partner = (get other : step) in
      let pl = literal partner.clause oj in
      if l.positive then
        [ 3; -r oi; 0 ]
        @ leaf_key code (side_subject l false) (side_subject pl false)
        @ [ other; oj; 0 ]
      else
        [ 4; -r oi; 0 ]
        @ leaf_key code (side_subject l false) (side_subject pl false)
        @ [ other; oj; 0 ]
  | Input _ | Component _ -> [ 0 ]
