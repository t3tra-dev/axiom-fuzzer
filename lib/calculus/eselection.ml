open Wire
(** E 3.5.9 literal selection functions (HEURISTICS/che_litselection.c), on normalized clauses.

    A result is the list of selected literal indices, [None] for no selection. A negative literal is
    always among the selected ones; the "P" variants additionally select every positive literal. As
    in E, such a literal is only a target of superposition and equality factoring, never a
    superposition source or a positive resolution premise ({!Calculus.into_only}), and only another
    selected positive literal can exceed it. Selection only restricts which inferences are searched;
    it never changes what the kernel accepts.

    E's equation sides: a predicate atom P(ts) is the oriented equation P(ts) = $true; an equation s
    = t is oriented when one side is greater in the installed KBO, and its "lterm" is that side (an
    unoriented equation keeps its written order). Literal maximality is E's EqnIsMaximal after
    ClauseCondMarkMaximalTerms: no other literal is strictly greater. *)

type t =
  | Max_l_complex_avoid_pos_pred
      (** SelectMaxLComplexAvoidPosPred, che_litselection.c:4833 (weights :4624). *)
  | P_complex_except_uniq_max_horn
      (** PSelectComplexExceptUniqMaxHorn, che_litselection.c:3834, via PSelectComplex :2981 and
          PSelectDiffNegativeLiteral :1399. *)
  | New_complex_ahp  (** SelectNewComplexAHP, che_litselection.c:5353 (weights :5300). *)
  | Complex_except_uniq_max_horn
      (** SelectComplexExceptUniqMaxHorn, che_litselection.c:3806, via SelectComplex :2929 and
          SelectDiffNegativeLiteral :1361: [P_complex_except_uniq_max_horn] without the positive
          literals. *)
  | Cq_ar_nt
      (** SelectCQArNT, che_litselection.c:6620 (weights :6595): one negative literal, by a total
          order on the literal heads, higher arity first (an equation counts as arity 2), then the
          alphabetically first head symbol, then the smallest [diff_weight]. Never no selection. *)
  | Cq_iprec_w_nt_np
      (** SelectCQIPrecWNTNp, che_litselection.c:7092 (weights :7064): one negative literal, a
          variable lterm first, then the head of the lterm greatest in the installed precedence (E's
          prec_weights), the alphabetically first head, the smallest [diff_weight]; a propositional
          or type literal P(X) is never selected. *)

(* TermStandardWeight: function symbols 2, variables 1 (cte_termtypes.h:42-43). *)
let rec standard_weight = function
  | V _ -> 1
  | Fn (_, ts) -> List.fold_left (fun n t -> n + standard_weight t) 2 ts

(* Number of positions, TermWeight(t, 1, 1). *)
let rec positions = function
  | V _ -> 1
  | Fn (_, ts) -> List.fold_left (fun n t -> n + positions t) 1 ts

type side = { lterm_weight : int; rterm_weight : int; oriented : bool; lterm_positions : int }

(* E's view of one literal as an equation lterm = rterm. *)
let sides ?(order = Ordering.standard) l =
  match l.atom with
  | P (_, ts) | D (_, ts) ->
      let w = List.fold_left (fun n t -> n + standard_weight t) 2 ts in
      let p = List.fold_left (fun n t -> n + positions t) 1 ts in
      { lterm_weight = w; rterm_weight = 2; oriented = true; lterm_positions = p }
  | E (s, t) ->
      let s, t, oriented =
        if Ordering.greater ~order s t then (s, t, true)
        else if Ordering.greater ~order t s then (t, s, true)
        else (s, t, false)
      in
      let p = positions s + if oriented then 0 else positions t in
      {
        lterm_weight = standard_weight s;
        rterm_weight = standard_weight t;
        oriented;
        lterm_positions = p;
      }

(* lit_sel_diff_weight, che_litselection.c:205: 100 * EqnStandardDiff + EqnStandardWeight. *)
let diff_weight ?order l =
  let s = sides ?order l in
  (100 * abs (s.lterm_weight - s.rterm_weight)) + s.lterm_weight + s.rterm_weight

let ground l = Wire.variables [ l ] = []
let pure_variable l = match l.atom with E (V _, V _) -> true | _ -> false

(* EqnGetPredCodeFO: 0 for equations, the predicate symbol otherwise. *)
let pred_code l =
  match l.atom with
  | E _ -> `Eq
  | P (p, ts) -> `P (p, List.length ts)
  | D (d, ts) -> `D (d, List.length ts)

(* pos_pred_dist_array_compute: predicate codes of the positive literals. *)
let positive_distribution clause =
  let counts = Hashtbl.create 8 in
  List.iter
    (fun l ->
      if l.positive then
        let k = pred_code l in
        Hashtbl.replace counts k (1 + Option.value ~default:0 (Hashtbl.find_opt counts k)))
    clause;
  fun k -> Option.value ~default:0 (Hashtbl.find_opt counts k)

(** E's literal order of a clause when it is processed: ForwardContractClause sorts every non-unit
    given clause with ClauseSubsumeOrderSortLits (CLAUSES/ccl_eqn.c
    EqnSubsumeInverseRefinedCompareRef) before its literal selection: positive literals first,
    equations before predicate literals, predicate literals by descending symbol code ([code]: E's
    codes), then by descending standard weight, the rest in their previous order (here the clause's
    own). Returns each literal's position in that order. E's selection functions take the first of
    equally good literals in this order. *)
let e_rank ~code clause =
  let weight l =
    let s = sides l in
    s.lterm_weight + s.rterm_weight
  in
  let key i (l : literal) =
    let pred =
      match l.atom with
      | E _ -> 0
      | P (p, ts) -> -code (Ordering.Predicate p, List.length ts)
      | D (d, ts) -> -code (Ordering.Definition d, List.length ts)
    in
    ((if l.positive then 0 else 1), (match l.atom with E _ -> 0 | _ -> 1), pred, -weight l, i)
  in
  let sorted = List.sort compare (List.mapi (fun i l -> (key i l, i)) clause) in
  let rank = Array.make (List.length clause) 0 in
  List.iteri (fun pos (_, i) -> rank.(i) <- pos) sorted;
  rank

(* The literals of [clause] with their indices, in E's order when [rank] is given. *)
let in_order ?rank clause =
  let indexed = List.mapi (fun i l -> (i, l)) clause in
  match rank with
  | None -> indexed
  | Some r -> List.sort (fun (i, _) (j, _) -> compare r.(i) r.(j)) indexed

let maximal_flags ?order clause = Ordering.maximal_flags ?order clause

(** E's literal maximality once a selection exists (ClauseCondMarkMaximalTerms after the selection
    function cleared CPIsOriented, e.g. che_litselection.c:644 and :3845). E's LiteralCompare
    (CLAUSES/ccl_eqn.c:2558) ranks selected literals above unselected ones and makes selected
    literals of opposite sign incomparable, so exactly the selected literals that no selected
    literal of the same sign exceeds are maximal. Without a selection this is the plain KBO
    maximality. *)
let selected_maximal_flags ?order clause = function
  | None -> maximal_flags ?order clause
  | Some js ->
      let xs = Array.of_list clause in
      Array.mapi
        (fun i l ->
          List.mem i js
          && List.for_all
               (fun j ->
                 j = i || xs.(j).positive <> l.positive
                 || not (Ordering.literal_greater ?order xs.(j) l))
               js)
        xs

let horn clause = List.length (List.filter (fun l -> l.positive) clause) <= 1

(* generic_uniq_selection (che_litselection.c:599) restricted to negative literals: the first
   negative literal with minimal (w1, w2, w3); [None] from the weight function forbids it. *)
let uniq_selection ?rank clause weight =
  let best = ref None in
  let visit i l =
    if not l.positive then
      let w = weight i l in
      match !best with
      | Some (old, _) when compare (fst w) (fst old) >= 0 -> ()
      | _ -> best := Some (w, i)
  in
  (match rank with
  | None -> List.iteri visit clause
  | Some _ -> List.iter (fun (i, l) -> visit i l) (in_order ?rank clause));
  match !best with Some ((_, true), i) -> Some [ i ] | _ -> None

let max_l_complex_avoid_pos_pred ?order ?rank clause =
  if List.for_all (fun l -> l.positive) clause then None
  else
    let flags = maximal_flags ?order clause in
    if Array.fold_left (fun n b -> if b then n + 1 else n) 0 flags <= 1 then None
    else
      let dist = positive_distribution clause in
      uniq_selection ?rank clause (fun i l ->
          let w1 =
            (if flags.(i) then 0 else 100)
            + (if pure_variable l then 0 else 10)
            + if ground l then 0 else 1
          in
          ((w1, -diff_weight ?order l, dist (pred_code l)), true))

(* [positives]: the P variant, which also selects every positive literal of the clause. *)
let complex_except_uniq_max_horn ?order ?rank ~positives clause =
  if List.for_all (fun l -> l.positive) clause then None
  else if
    horn clause
    && Array.fold_left (fun n b -> if b then n + 1 else n) 0 (maximal_flags ?order clause) = 1
  then None
  else
    let indexed = in_order ?rank clause in
    (* ClauseFindNegPureVarLit, then the smallest negative ground literal. *)
    match List.find_opt (fun (_, l) -> (not l.positive) && pure_variable l) indexed with
    | Some (i, _) -> Some [ i ]
    | None -> (
        let ground_choice =
          List.fold_left
            (fun best (i, l) ->
              if l.positive || not (ground l) then best
              else
                let s = sides ?order l in
                let w = s.lterm_weight + s.rterm_weight in
                match best with Some (bw, _) when bw <= w -> best | _ -> Some (w, i))
            None indexed
        in
        match ground_choice with
        | Some (_, i) -> Some [ i ]
        | None ->
            (* PSelectDiffNegativeLiteral: the most unbalanced negative literal and every
               positive literal. *)
            let negative =
              List.fold_left
                (fun best (i, l) ->
                  if l.positive then best
                  else
                    let w = diff_weight ?order l in
                    match best with Some (bw, _) when bw >= w -> best | _ -> Some (w, i))
                None indexed
            in
            Option.map
              (fun (_, i) ->
                if not positives then [ i ]
                else
                  i :: List.filter_map (fun (j, l) -> if l.positive then Some j else None) indexed
                  |> List.sort compare)
              negative)

let p_complex_except_uniq_max_horn ?order ?rank clause =
  complex_except_uniq_max_horn ?order ?rank ~positives:true clause

(* E's alpha rank (SigGetAlphaRank) orders symbols by name; the name itself gives the same order.
   A Skolem symbol takes E's "esk<n>_<arity>" spelling, a variable the empty name (E's rank 0). *)
let alpha_name = function Original s -> s | Skolem (n, arity) -> Printf.sprintf "esk%d_%d" n arity

let cq_ar_nt ?order ?rank clause =
  if List.for_all (fun l -> l.positive) clause then None
  else
    uniq_selection ?rank clause (fun _ l ->
        let w1, w2 =
          match l.atom with
          | E (s, t) -> (
              (* E's lterm: the greater side of an oriented equation, else the first. *)
              match if Ordering.greater ?order t s then t else s with
              | V _ -> (-2, "")
              | Fn (f, _) -> (-2, alpha_name f))
          | P (p, ts) -> (-List.length ts, p)
          | D ((a, b), ts) -> (-List.length ts, Printf.sprintf "def%d_%d" a b)
        in
        ((w1, w2, diff_weight ?order l), true))

let cq_iprec_w_nt_np ?(order = Ordering.standard) ?rank clause =
  if List.for_all (fun l -> l.positive) clause then None
  else
    uniq_selection ?rank clause (fun _ l ->
        let diff = diff_weight ~order l in
        let head =
          match l.atom with
          | E (s, t) -> (
              (* E's lterm: the greater side of an oriented equation, else the first. *)
              match if Ordering.greater ~order t s then t else s with
              | V _ -> None
              | Fn (f, ts) -> Some ((Ordering.Function f, List.length ts), alpha_name f, false))
          | P (p, ts) ->
              Some
                ( (Ordering.Predicate p, List.length ts),
                  p,
                  match ts with [] | [ V _ ] -> true | _ -> false )
          | D (((a, b) as d), ts) ->
              Some
                ( (Ordering.Definition d, List.length ts),
                  Printf.sprintf "def%d_%d" a b,
                  match ts with [] | [ V _ ] -> true | _ -> false )
        in
        match head with
        | None -> ((0, "", diff), true)
        | Some (_, _, true) -> ((100000, "", diff), false)
        | Some (key, name, false) -> ((-Ordering.rank order key, name, diff), true))

let new_complex_ahp ?order ?rank clause =
  if List.for_all (fun l -> l.positive) clause then None
  else
    let dist = positive_distribution clause in
    uniq_selection ?rank clause (fun _ l ->
        let s = sides ?order l in
        let args = match l.atom with P (_, ts) | D (_, ts) -> Some ts | E _ -> None in
        let xtype =
          match args with
          | Some (_ :: _ as ts) -> List.for_all (function V _ -> true | Fn _ -> false) ts
          | _ -> false
        in
        let w1, w2, allowed =
          if ground l then (0, s.lterm_weight, true)
          else if not xtype then (10, s.lterm_positions, true)
          else if s.lterm_weight <> 3 then (20, -s.lterm_weight, true)
          else (* a type literal P(X) is never selected *) (100000, 0, false)
        in
        let w3 = match l.atom with E _ -> 0 | _ -> dist (pred_code l) in
        ((w1, w2, w3), allowed))

(* The selections without a rank, with the arity they had before they took one: [select] then
   builds the same closures as before (the allocation clock that cuts a lane's slices reads them). *)
let max_l_plain ?order clause = max_l_complex_avoid_pos_pred ?order clause
let p_complex_plain ?order clause = p_complex_except_uniq_max_horn ?order clause
let new_complex_plain ?order clause = new_complex_ahp ?order clause
let complex_plain ?order clause = complex_except_uniq_max_horn ?order ~positives:false clause
let cq_ar_nt_plain ?order clause = cq_ar_nt ?order clause
let cq_iprec_plain ?order clause = cq_iprec_w_nt_np ?order clause

(** [rank]: E's literal order ({!e_rank}), which decides between equally good literals; without it
    the clause's own order does. *)
let select ?order ?rank sel =
  match rank with
  | None -> (
      match sel with
      | Max_l_complex_avoid_pos_pred -> max_l_plain ?order
      | P_complex_except_uniq_max_horn -> p_complex_plain ?order
      | New_complex_ahp -> new_complex_plain ?order
      | Complex_except_uniq_max_horn -> complex_plain ?order
      | Cq_ar_nt -> cq_ar_nt_plain ?order
      | Cq_iprec_w_nt_np -> cq_iprec_plain ?order)
  | Some _ -> (
      match sel with
      | Max_l_complex_avoid_pos_pred -> max_l_complex_avoid_pos_pred ?order ?rank
      | P_complex_except_uniq_max_horn -> p_complex_except_uniq_max_horn ?order ?rank
      | New_complex_ahp -> new_complex_ahp ?order ?rank
      | Complex_except_uniq_max_horn -> complex_except_uniq_max_horn ?order ?rank ~positives:false
      | Cq_ar_nt -> cq_ar_nt ?order ?rank
      | Cq_iprec_w_nt_np -> cq_iprec_w_nt_np ?order ?rank)
