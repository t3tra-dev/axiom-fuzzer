open Wire
(** E 3.5.9 clause evaluation functions and priority functions (HEURISTICS/che_*.c).

    An evaluation is the pair (priority, heuristic weight); E orders a queue by priority, then
    weight, then evaluation order (CLAUSES/ccl_neweval.c:388 [EvalCompare]). Clause selection cycles
    through the queues with their counts (che_hcb.c:898 [HCBStandardClauseSelect], counts are
    cumulative in [HCBAddWFCB] :834). Evaluations only order the search; they never reach a
    certificate. The role-dependent inputs (conjecture symbols) are search hints. *)

type priority =
  | Const_prio  (** che_prio_funs.c:606 PrioFunConstPrio: always PrioNormal. *)
  | Simulate_sos
      (** che_prio_funs.c:779 PrioFunSimulateSOS: PrioNormal for initial or set-of-support clauses,
          PrioDefer otherwise. Every ported strategy has use_tptp_sos false, so the set of support
          is E's ClauseSetMarkSOS (ccl_clausesets.c:1162): the initial clauses without a positive
          literal, and every clause derived from or simplified by a set-of-support clause. *)
  | Prefer_non_goals
      (** che_prio_funs.c:395 PrioFunPreferNonGoals: PrioPrefer unless the clause is a goal, i.e.
          has no positive literal (ccl_clauses.h ClauseIsGoal). Role-free. *)
  | Prefer_processed
      (** che_prio_funs.c:319 PrioFunPreferProcessed: PrioPrefer for clauses that were processed
          before (here: results of backward simplification of an active clause). *)
  | Prefer_goals
      (** che_prio_funs.c:369 PrioFunPreferGoals: PrioPrefer for goals, i.e. clauses without a
          positive literal (ccl_clauses.h:248 ClauseIsGoal), PrioNormal otherwise. Role-free. *)
  | Below_level of priority * int
      (** Layered clause selection (Gleiss and Suda, PAAR 2020) on SInE levels ({!Sine_levels},
          [facts.level]): the inner priority for a clause whose level is at most the cutoff, and
          every deeper clause after all of them ([prio_layer] later). Such a queue selects from the
          goal-near layer while it has clauses and from the whole set otherwise; a member pairs it
          with the plain queue, so the deeper clauses keep their turns (no axiom is filtered). *)

(* ccl_neweval.h:44-48 *)
let prio_prefer = 30
let prio_normal = 40
let prio_defer = 50

(* Above every E priority difference: a deeper-layer clause comes after every clause of the layer. *)
let prio_layer = 1000

(* PrioLargestReasonable (MEGA): E's prefer_initial_clauses lowers every evaluation priority of an
   initial clause by it (cco_proofproc.c:1510 EvalListChangePriority), so each queue selects the
   initial clauses first. *)
let prio_largest_reasonable = 1 lsl 20

type weight =
  | Crsw of {
      conj_multiplier : float;
      fweight : int;
      cweight : int;
      pweight : int;
      vweight : int;
      max_term : float;
      max_literal : float;
      positive : float;
    }
      (** ConjectureRelativeSymbolWeight (che_funweights.c:870, init_conj_vector :59,
          GenericFunWeightCompute :1451, ClauseFunWeight ccl_clauses.c:2037, EqnFunWeight
          ccl_eqn.c:2790). Symbols of negated-conjecture input clauses weigh
          [floor (conj_multiplier * base)]. *)
  | Refined of {
      fweight : int;
      vweight : int;
      max_term : float;
      max_literal : float;
      positive : float;
    }
      (** Refinedweight (che_refinedweight.c ClauseRefinedWeightCompute, ClauseWeight
          ccl_clauses.c:2006 with count_eq_encoding false, EqnCorrectedWeight ccl_eqn.c:2959). *)
  | Pn_refined of {
      fweight : int;
      vweight : int;
      nfweight : int;
      nvweight : int;
      max_term : float;
      max_literal : float;
      positive : float;
    }
      (** PNRefinedweight (che_varweights.c:893 PNRefinedWeightCompute): Refinedweight with
          [fweight]/[vweight] on positive literals and [nfweight]/[nvweight] on negative ones. *)
  | Fifo  (** FIFOWeight (che_fifo.c:111): evaluation order. *)
  | Diversity of {
      fweight : int;
      vweight : int;
      max_term : float;
      max_literal : float;
      positive : float;
      fdiff1 : float;
      fdiff2 : float;
      vdiff1 : float;
      vdiff2 : float;
    }  (** Diversityweight (che_diversityweight.c DiversityWeightCompute). *)
  | Orient_lmax of {
      fweight : int;
      vweight : int;
      unorientable : float;
      max_literal : float;
      positive : float;
    }  (** OrientLMaxWeight (che_orientweight.c:242). *)
  | Conj_general of {
      fweight : int;
      cweight : int;
      pweight : int;
      conj_fweight : int;
      conj_cweight : int;
      conj_pweight : int;
      vweight : int;
      max_term : float;
      max_literal : float;
      positive : float;
    }
      (** ConjectureGeneralSymbolWeight (che_funweights.c ConjectureGeneralSymbolWeightParse,
          init_conj_vector :59, GenericFunWeightCompute): symbols of the negated-conjecture input
          clauses weigh the conj_* weights, the others the base weights, in the clause function
          weight of [Crsw]. *)
  | Relevance2 of {
      const : float;
      lin : float;
      square : float;
      penalty : int;
      fweight : int;
      cweight : int;
      pweight : int;
      vweight : int;
      max_term : float;
      max_literal : float;
      positive : float;
    }
      (** RelevanceLevelWeight2 (che_funweights.c RelevanceLevelWeightParse2 :1141,
          init_relevance_vector2 :259): a symbol of relevance level [r] ([facts.relevance]; the
          default penalty plus the deepest level when unreached, 1 for $true) weighs its base weight
          times [const + lin r + square r^2], truncated (E stores it as an integer), in the clause
          function weight of [Crsw]. E passes [const] as an integer. *)

type queue = { count : int; priority : priority; weight : weight }

type relevance = { symbol_level : Ordering.head * int -> int option; max_level : int }
(** E's RelevanceDataCompute (ccl_relevance.c:445): level 1 holds the symbols of the
    negated-conjecture clauses; the clauses that contain a symbol of level [k] and no earlier one
    form the next core, whose new symbols get level [k + 1]; [max_level] is one past the last level.
*)

type facts = {
  initial : bool;  (** An input clause or a forward simplification of one (E's CPInitial). *)
  sos : bool;
      (** In E's set of support (CPIsSOS): an input clause without a positive literal, a conclusion
          with a set-of-support premise, or a clause simplified by one. *)
  processed : bool;  (** A backward simplification of an active clause (E's CPIsProcessed). *)
  conjecture : (Ordering.head * int -> bool) option;
      (** Membership in the symbol set of the negated-conjecture input clauses; [None] when the
          input carries no roles (then no symbol is a conjecture symbol). *)
  age : int;  (** Evaluation order, the FIFO weight. *)
  level : int;
      (** The clause's SInE level ({!Sine_levels}): an input clause has its axiom's level, a derived
          clause the least level of its parents. 0 when the strategy reads no levels. *)
  relevance : relevance option;
      (** E's relevance levels of the input symbols ({!relevance_levels}), for [Relevance2]. *)
}
(** Facts about one clause that its evaluations read. *)

(* E's view of one literal after ClauseCondMarkMaximalTerms: lterm = rterm with lterm the greater
   side when oriented; a predicate atom is the oriented P(ts) = $true. *)
type side = Term of term | Head of Ordering.head * term list | True

type literal_view = {
  lterm : side;
  rterm : side;
  oriented : bool;
  maximal : bool;
  positive_lit : bool;
  equation : bool;
}

(* [selection]: the E selection function of the clause's strategy. E evaluates an initial clause
   before any literal selection (cco_proofproc.c:1501, ProofStateInit), and every other clause
   after it (cco_proofproc.c:741, insert_new_clauses), when a selection makes exactly the maximal
   selected literals maximal (Eselection.selected_maximal_flags). *)
let views ?order ?selection ?rank ~initial ~maximality clause =
  let flags =
    match selection with
    | _ when not maximality -> Array.make (List.length clause) false
    | Some s when not initial ->
        Eselection.selected_maximal_flags ?order clause (Eselection.select ?order ?rank s clause)
    | _ -> Eselection.maximal_flags ?order clause
  in
  List.mapi
    (fun i l ->
      let lterm, rterm, oriented, equation =
        match l.atom with
        | P (p, ts) -> (Head (Ordering.Predicate p, ts), True, true, false)
        | D (d, ts) -> (Head (Ordering.Definition d, ts), True, true, false)
        | E (s, t) ->
            if Ordering.greater ?order s t then (Term s, Term t, true, true)
            else if Ordering.greater ?order t s then (Term t, Term s, true, true)
            else (Term s, Term t, false, true)
      in
      { lterm; rterm; oriented; maximal = flags.(i); positive_lit = l.positive; equation })
    clause

(* TermWeight(t, vweight, fweight); $true is a function symbol in E's term bank. *)
let side_weight ~fweight ~vweight side =
  let rec term = function
    | V _ -> vweight
    | Fn (_, ts) -> List.fold_left (fun n t -> n + term t) fweight ts
  in
  match side with
  | Term t -> term t
  | Head (_, ts) -> List.fold_left (fun n t -> n + term t) fweight ts
  | True -> fweight

let modifiers ~max_literal ~positive v w =
  let w = if v.maximal then w *. max_literal else w in
  if v.positive_lit then w *. positive else w

(* LiteralWeight with count_eq_encoding false (EqnCorrectedWeight). *)
let literal_weight ~fweight ~vweight ~max_term ~max_literal ~positive v =
  let w = float_of_int (side_weight ~fweight ~vweight v.lterm) *. max_term in
  let w =
    if v.equation then
      let r = float_of_int (side_weight ~fweight ~vweight v.rterm) in
      w +. (if v.oriented then r else r *. max_term) +. float_of_int fweight
    else w
  in
  modifiers ~max_literal ~positive v w

(* ClauseWeight: the sum of the literal weights. *)
let refined_weight ~fweight ~vweight ~max_term ~max_literal ~positive views =
  List.fold_left
    (fun acc v -> acc +. literal_weight ~fweight ~vweight ~max_term ~max_literal ~positive v)
    0. views

let rec distinct_variables acc = function
  | V v -> if List.mem v acc then acc else v :: acc
  | Fn (_, ts) -> List.fold_left distinct_variables acc ts

let rec function_codes acc = function
  | V _ -> acc
  | Fn (f, ts) ->
      let key = (Ordering.Function f, List.length ts) in
      List.fold_left function_codes (if List.mem key acc then acc else key :: acc) ts

(* A symbol's base weight in E's function weights: predicates (and $true) [pweight], constants
   [cweight], other function symbols [fweight]. *)
let base_weight ~fweight ~cweight ~pweight (head, arity) =
  match head with
  | Ordering.Predicate _ | Ordering.Definition _ | Ordering.Truth -> pweight
  | Ordering.Function _ -> if arity = 0 then cweight else fweight

let is_conj facts key = match facts.conjecture with None -> false | Some f -> f key

(* ClauseFunWeight (ccl_clauses.c:2037) with EqnFunWeight (ccl_eqn.c:2790): the sides weigh
   their symbols by [symbol] and variables [vweight]; the lterm is multiplied by [max_term] always,
   the rterm only when unoriented. *)
let fun_weight ~symbol ~vweight ~max_term ~max_literal ~positive views =
  let rec fsum = function
    | V _ -> vweight
    | Fn (f, ts) ->
        List.fold_left (fun n t -> n + fsum t) (symbol (Ordering.Function f, List.length ts)) ts
  in
  let side = function
    | Term t -> fsum t
    | Head (h, ts) -> List.fold_left (fun n t -> n + fsum t) (symbol (h, List.length ts)) ts
    | True -> symbol (Ordering.Truth, 0)
  in
  List.fold_left
    (fun acc v ->
      let r = float_of_int (side v.rterm) in
      let r = if v.oriented then r else r *. max_term in
      let w = r +. (float_of_int (side v.lterm) *. max_term) in
      acc +. modifiers ~max_literal ~positive v w)
    0. views

let heuristic weight facts clause views =
  match weight with
  | Fifo -> float_of_int facts.age
  | Refined { fweight; vweight; max_term; max_literal; positive } ->
      refined_weight ~fweight ~vweight ~max_term ~max_literal ~positive views
  | Pn_refined { fweight; vweight; nfweight; nvweight; max_term; max_literal; positive } ->
      List.fold_left
        (fun acc v ->
          let fweight, vweight =
            if v.positive_lit then (fweight, vweight) else (nfweight, nvweight)
          in
          acc +. literal_weight ~fweight ~vweight ~max_term ~max_literal ~positive v)
        0. views
  | Diversity { fweight; vweight; max_term; max_literal; positive; fdiff1; fdiff2; vdiff1; vdiff2 }
    ->
      let base = refined_weight ~fweight ~vweight ~max_term ~max_literal ~positive views in
      let terms = List.concat_map (fun l -> Clause.atom_terms l.atom) clause in
      let vars = float_of_int (List.length (List.fold_left distinct_variables [] terms)) in
      let codes =
        List.fold_left
          (fun acc l ->
            match l.atom with
            | P (p, ts) -> (Ordering.Predicate p, List.length ts) :: acc
            | D (d, ts) -> (Ordering.Definition d, List.length ts) :: acc
            | E _ -> acc)
          (List.fold_left function_codes [] terms)
          clause
        |> List.sort_uniq compare |> List.length |> float_of_int
      in
      base +. (codes *. ((fdiff2 *. codes) +. fdiff1)) +. (vars *. ((vdiff2 *. vars) +. vdiff1))
  | Orient_lmax { fweight; vweight; unorientable; max_literal; positive } ->
      List.fold_left
        (fun acc v ->
          let w =
            float_of_int
              (max (side_weight ~fweight ~vweight v.lterm) (side_weight ~fweight ~vweight v.rterm))
          in
          let w = if v.positive_lit then w *. positive else w in
          let w = if v.maximal then w *. max_literal else w in
          acc +. if v.oriented then w else w *. unorientable)
        0. views
  | Crsw { conj_multiplier; fweight; cweight; pweight; vweight; max_term; max_literal; positive } ->
      let conj w = int_of_float (conj_multiplier *. float_of_int w) in
      let symbol key =
        let base = base_weight ~fweight ~cweight ~pweight key in
        if is_conj facts key then conj base else base
      in
      fun_weight ~symbol ~vweight ~max_term ~max_literal ~positive views
  | Conj_general
      {
        fweight;
        cweight;
        pweight;
        conj_fweight;
        conj_cweight;
        conj_pweight;
        vweight;
        max_term;
        max_literal;
        positive;
      } ->
      let symbol key =
        if is_conj facts key then
          base_weight ~fweight:conj_fweight ~cweight:conj_cweight ~pweight:conj_pweight key
        else base_weight ~fweight ~cweight ~pweight key
      in
      fun_weight ~symbol ~vweight ~max_term ~max_literal ~positive views
  | Relevance2
      {
        const;
        lin;
        square;
        penalty;
        fweight;
        cweight;
        pweight;
        vweight;
        max_term;
        max_literal;
        positive;
      } ->
      let level ((head, _) as key) =
        match (head, facts.relevance) with
        | Ordering.Truth, _ -> 1
        | _, None -> penalty
        | _, Some r -> (
            match r.symbol_level key with Some l -> l | None -> penalty + r.max_level)
      in
      let symbol key =
        let r = float_of_int (level key) in
        int_of_float
          (float_of_int (base_weight ~fweight ~cweight ~pweight key)
          *. (Float.trunc const +. (lin *. r) +. (square *. r *. r)))
      in
      fun_weight ~symbol ~vweight ~max_term ~max_literal ~positive views

let rec priority p facts clause =
  match p with
  | Const_prio -> prio_normal
  | Simulate_sos -> if facts.initial || facts.sos then prio_normal else prio_defer
  | Prefer_non_goals ->
      if List.exists (fun l -> l.positive) clause then prio_prefer else prio_normal
  | Prefer_processed -> if facts.processed then prio_prefer else prio_normal
  | Prefer_goals -> if List.exists (fun l -> l.positive) clause then prio_normal else prio_prefer
  | Below_level (p, cutoff) ->
      priority p facts clause + if facts.level > cutoff then prio_layer else 0

(** Evaluate one clause for every queue, in queue order. [selection] is the E selection function
    whose choice decides the maximal literals of a non-initial clause; without it every clause uses
    its maximal literals in the installed order. [prefer_initial] (E's prefer_initial_clauses)
    lowers every priority of an initial clause by [prio_largest_reasonable]. *)
let evaluate ?order ?selection ?rank ?(prefer_initial = false) queues facts clause =
  (* A max_literal factor of 1 multiplies by 1.0, which is exact: maximality is only computed
     when some queue weighs it. *)
  let maximality =
    List.exists
      (fun q ->
        match q.weight with
        | Crsw { max_literal; _ }
        | Refined { max_literal; _ }
        | Pn_refined { max_literal; _ }
        | Diversity { max_literal; _ }
        | Orient_lmax { max_literal; _ }
        | Conj_general { max_literal; _ }
        | Relevance2 { max_literal; _ } ->
            max_literal <> 1.
        | Fifo -> false)
      queues
  in
  let views =
    match rank with
    | None -> lazy (views ?order ?selection ~initial:facts.initial ~maximality clause)
    | Some _ -> lazy (views ?order ?selection ?rank ~initial:facts.initial ~maximality clause)
  in
  let boost = if prefer_initial && facts.initial then prio_largest_reasonable else 0 in
  Array.of_list
    (List.map
       (fun q ->
         let views = match q.weight with Fifo -> [] | _ -> Lazy.force views in
         (priority q.priority facts clause - boost, heuristic q.weight facts clause views))
       queues)

(** The symbol set of the given (negated-conjecture) clauses, for [facts.conjecture]. E adds the
    $true symbol when a goal clause has a predicate literal. *)
let conjecture_symbols (clauses : clause list) =
  let set = Hashtbl.create 32 in
  let rec term = function
    | V _ -> ()
    | Fn (f, ts) ->
        Hashtbl.replace set (Ordering.Function f, List.length ts) ();
        List.iter term ts
  in
  List.iter
    (List.iter (fun l ->
         match l.atom with
         | E (s, t) ->
             term s;
             term t
         | P (p, ts) ->
             Hashtbl.replace set (Ordering.Predicate p, List.length ts) ();
             Hashtbl.replace set (Ordering.Truth, 0) ();
             List.iter term ts
         | D (d, ts) ->
             Hashtbl.replace set (Ordering.Definition d, List.length ts) ();
             Hashtbl.replace set (Ordering.Truth, 0) ();
             List.iter term ts))
    clauses;
  fun key -> Hashtbl.mem set key

(** E's relevance levels ({!relevance}) of the symbols of [goals] (the negated-conjecture clauses)
    and [others]. *)
let relevance_levels ~(goals : clause list) ~(others : clause list) =
  let symbols (c : clause) =
    let seen = Hashtbl.create 16 in
    let rec term = function
      | V _ -> ()
      | Fn (f, ts) ->
          Hashtbl.replace seen (Ordering.Function f, List.length ts) ();
          List.iter term ts
    in
    List.iter
      (fun l ->
        match l.atom with
        | E (s, t) ->
            term s;
            term t
        | P (p, ts) ->
            Hashtbl.replace seen (Ordering.Predicate p, List.length ts) ();
            List.iter term ts
        | D (d, ts) ->
            Hashtbl.replace seen (Ordering.Definition d, List.length ts) ();
            List.iter term ts)
      c;
    Hashtbl.fold (fun k () acc -> k :: acc) seen []
  in
  let level = Hashtbl.create 64 in
  let rest = Array.of_list (List.map symbols others) in
  let used = Array.make (Array.length rest) false in
  let by_symbol = Hashtbl.create 64 in
  Array.iteri
    (fun i syms ->
      List.iter
        (fun k ->
          Hashtbl.replace by_symbol k (i :: Option.value ~default:[] (Hashtbl.find_opt by_symbol k)))
        syms)
    rest;
  let rec go k core =
    if core = [] then k
    else
      let fresh =
        List.concat_map
          (fun syms ->
            List.filter
              (fun s ->
                if Hashtbl.mem level s then false
                else (
                  Hashtbl.replace level s k;
                  true))
              syms)
          core
      in
      let next =
        List.concat_map
          (fun s ->
            List.filter_map
              (fun i ->
                if used.(i) then None
                else (
                  used.(i) <- true;
                  Some rest.(i)))
              (Option.value ~default:[] (Hashtbl.find_opt by_symbol s)))
          fresh
      in
      go (k + 1) next
  in
  let max_level = go 1 (List.map symbols goals) in
  { symbol_level = Hashtbl.find_opt level; max_level }

(** Whether a queue mix reads relevance levels. *)
let uses_relevance queues =
  List.exists (fun q -> match q.weight with Relevance2 _ -> true | _ -> false) queues

(** Whether a queue mix reads SInE levels. *)
let uses_levels queues =
  List.exists (fun q -> match q.priority with Below_level _ -> true | _ -> false) queues

(** The two-layer version of a queue mix: each queue as it is, followed by its copy restricted to
    the clauses of level at most [cutoff] (falling back to the rest when that layer is empty), with
    [ratio] times its count. *)
let layered ~cutoff ~ratio queues =
  List.concat_map
    (fun q ->
      [ q; { q with count = ratio * q.count; priority = Below_level (q.priority, cutoff) } ])
    queues
