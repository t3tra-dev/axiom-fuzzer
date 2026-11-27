open Wire
(** E 3.5.9 term-ordering instantiation (KBO6 or LPO4): precedence and symbol-weight generators.

    E builds one total precedence over every symbol of the input (function and predicate symbols
    together) by sorting feature keys (HEURISTICS/che_to_precgen.c, che_fcode_featurearrays.c:54-83
    [feature_compare_function]: ascending key0..key3, then first occurrence), and then derives KBO
    symbol weights from that precedence or from symbol frequencies (HEURISTICS/che_to_weightgen.c).
    This module reproduces the generators used by the ported strategies and returns the table that
    {!Ordering.install_table} consumes: [(head, arity) -> (rank, weight)].

    With [e_signature] the table is E's own KBO instance, checked against E's printed ordering and
    clause evaluations (tests/unit/heuristic_tests.ml). Without it (the first port, still the
    measured e208, y1346 and sat001) three search-only deviations remain:
    - {!Ordering} compares heads class-first (functions below predicates); within a class the rank
      below is E's unified rank, so only weight ties between a predicate atom and a function term
      can order differently from E.
    - E's internal symbols ($false, $eq, ..., $distinct) are not counted, so the precedence weights
      of non-constant symbols and the weight-0 symbol of aritymax0 can differ.
    - A to_const_weight of 0 makes every constant weigh 1, where E keeps the generated weights.

    Weights never affect soundness: the kernel checks every inference whatever ordering produced it.
    They affect termination of rewriting, so {!admissible} repairs any weight-0 unary function
    symbol that is not the greatest function symbol, as KBO requires.

    An LPO4 instance ([ordering = Lpo], E's to_weight_gen none) uses only the precedence: E's LPO
    compares heads by OCBFunCompare, so the LPO strategies set [e_signature] and compare predicate
    and function symbols in one precedence. E's internal symbols take part in E's sort but never in
    a clause, so they do not change the relative order of the input symbols. *)

type precedence =
  | Invfreq  (** che_to_precgen.c:461 [generate_invfreq_precedence] *)
  | Invfreq_hack  (** che_to_precgen.c:718 [generate_invfreq_hack_precedence] *)
  | Arity  (** che_to_precgen.c:219 [generate_arity_precedence] *)
  | Invfreq_constmin  (** che_to_precgen.c:676 [generate_invfreq_constmin_precedence] *)
  | Invarity  (** che_to_precgen.c:248 [generate_invarity_precedence]: higher arity is smaller. *)
  | Unary_first
      (** che_to_precgen.c:138 [generate_unary_first_precedence]: by arity, unary symbols on top. *)
  | Const_min
      (** che_to_precgen.c:310 [generate_const_min_precedence] (E's const_min): by inverse arity,
          constants at the bottom. *)
  | Invfreq_conjmax
      (** che_to_precgen.c:613 [generate_invfreq_conjmax_precedence]: the symbols of the
          negated-conjecture clauses above the others, inverse frequency within each class, then
          arity. Without roles no symbol is a conjecture symbol and this is [Invfreq]. *)
  | Occurrence of precedence * occurrence
      (** The precedence with E's first sort key raised by the symbol's occurrence class
          (che_fcode_featurearrays.c:158 FCodeFeatureArrayUpdateOccKey: conj_only_mod,
          conj_axiom_mod and axiom_only_mod of the ordering parameters). *)

and occurrence = { conj_only : int; conj_axiom : int; axiom_only : int }
(** E's occurrence modifiers of the first precedence key: for symbols that occur only in
    negated-conjecture clauses, in both, and only in the other clauses. *)

type weights =
  | Unit_weights  (** Every symbol weighs 1 (the production KBO weights). *)
  | Precedence_weights  (** che_to_weightgen.c:411 [generate_precedence_weights] *)
  | Invfreq_rank  (** che_to_weightgen.c:916 [generate_invfreqrank_weights] *)
  | Arity_weights  (** che_to_weightgen.c:352 [generate_arity_weights], WArityWeight *)
  | Arity_max0  (** As [Arity_weights], then the first maximal symbol weighs 0 (set_maximal_0). *)
  | Inv_precedence
      (** che_to_weightgen.c:446 [generate_invprecedence_weights]: 1 + the number of greater symbols
          in the total precedence. *)
  | Selmax
      (** che_to_weightgen.c:333 [generate_selmax_weights], E's to_weight_gen none: every symbol
          weighs 1 and the greatest symbol of the total precedence 0. *)
  | Precrank20
      (** che_to_weightgen.c:518 [generate_precrank20_weights] (generate_precrank_weights :141): the
          symbols in ascending precedence, the [i]-th of [n] weighs [floor (i / (n / 20)) + 1]. *)

type t = {
  ordering : Ordering.kind;  (** E's ordertype: KBO6 ([Kbo]) or LPO4 ([Lpo]). *)
  precedence : precedence;
  weights : weights;
  const_weight : int;
      (** E's to_const_weight: every constant weighs [max const_weight 1]
          (che_to_weightgen.c:1448-1460). With [e_signature], 0 keeps the generated weights, as E's
          TOSelectOrdering maps WConstNoWeight to WConstNoSpecialWeight (che_to_autoselect.c:872).
      *)
  e_signature : bool;
      (** E's own instance: E's internal symbols take part in the generators, a constant weight 0
          keeps the generated weights, and predicate and function symbols share one precedence
          (OCBFunCompare, cto_ocb.h:227). *)
  e_ranks : bool;
      (** E's own first-occurrence tie breaker ({!e_pos_ranks}). Off: the rank of the first preorder
          occurrence, as in the first port (and every KBO strategy). *)
}

type symbol = {
  key : Ordering.head * int;
  arity : int;
  mutable freq : int;  (** Occurrences in the initial clauses (ClauseSetAddSymbolDistribution). *)
  mutable conj : bool;  (** Occurs in a negated-conjecture clause (E's conjfreq > 0). *)
  mutable axiom : bool;  (** Occurs in another clause (E's axiomfreq > 0). *)
  mutable first : int;  (** First-occurrence rank, E's pos_rank tie breaker. *)
}

(* Symbol statistics of the initial clause set, in clause and preorder term order. The truth
   constant is E's SIG_TRUE_CODE and never takes part in the sort. *)
let statistics (clauses : clause list) =
  let table = Hashtbl.create 64 and order = ref [] in
  let bump key arity =
    match Hashtbl.find_opt table key with
    | Some s -> s.freq <- s.freq + 1
    | None ->
        let s =
          { key; arity; freq = 1; conj = false; axiom = false; first = Hashtbl.length table }
        in
        Hashtbl.add table key s;
        order := s :: !order
  in
  let rec term = function
    | V _ -> ()
    | Fn (f, ts) ->
        bump (Ordering.Function f, List.length ts) (List.length ts);
        List.iter term ts
  in
  List.iter
    (List.iter (fun l ->
         match l.atom with
         | E (s, t) ->
             term s;
             term t
         | P (p, ts) ->
             bump (Ordering.Predicate p, List.length ts) (List.length ts);
             List.iter term ts
         | D (d, ts) ->
             bump (Ordering.Definition d, List.length ts) (List.length ts);
             List.iter term ts))
    clauses;
  List.rev !order

(* E's pos_rank (TERMS/cte_termfunc.c:2653 TermComputeFunctionRanks via
   ClauseSetComputeFunctionRanks, che_fcode_featurearrays.c FCodeFeatureArrayAlloc): clauses in
   order, each equation's lterm then rterm (a predicate atom is P(ts) = $true), every term in
   postorder (arguments before the head), each symbol taking the next count when its rank is still
   0. The count starts at 0, so the first symbol E visits keeps rank 0 only until its next
   occurrence, which ranks it again (above every symbol seen in between). The truth constant takes a
   count too. Returns the rank of every visited symbol. *)
let e_pos_ranks (clauses : clause list) =
  let rank = Hashtbl.create 64 and count = ref 0 in
  let visit key =
    if Option.value ~default:0 (Hashtbl.find_opt rank key) = 0 then Hashtbl.replace rank key !count;
    incr count
  in
  let rec term = function
    | V _ -> ()
    | Fn (f, ts) ->
        List.iter term ts;
        visit (Ordering.Function f, List.length ts)
  in
  let atom head ts =
    List.iter term ts;
    visit (head, List.length ts);
    visit (Ordering.Truth, 0)
  in
  List.iter
    (List.iter (fun l ->
         match l.atom with
         | E (s, t) ->
             term s;
             term t
         | P (p, ts) -> atom (Ordering.Predicate p) ts
         | D (d, ts) -> atom (Ordering.Definition d) ts))
    clauses;
  rank

(* E 3.5.9's internal symbols, signature codes 2-22 (TERMS/cte_signature.c SigAlloc): they never
   occur in a first-order clause (frequency 0, pos_rank 0) but take part in E's precedence and
   in every generator that counts smaller symbols. $true (code 1) never takes part. *)
let e_internal =
  [
    ("$false", 0);
    ("$eq", 2);
    ("$neq", 2);
    ("$qex", 2);
    ("$qall", 2);
    ("$not", 1);
    ("$and", 2);
    ("$or", 2);
    ("$impl", 2);
    ("$equiv", 2);
    ("$nand", 2);
    ("$nor", 2);
    ("$bimpl", 2);
    ("$xor", 2);
    ("$answer", 1);
    ("$@_var", 1);
    ("$named_lam", 2);
    ("$db_lam", 2);
    ("$ite", 3);
    ("$let", 3);
    ("$distinct", -1);
  ]

(* Internal symbols use definition heads with negative ids, which no clause contains. *)
let internal_symbols () =
  List.mapi
    (fun i (_, arity) ->
      {
        key = (Ordering.Definition (-1, i), max arity 0);
        arity;
        freq = 0;
        conj = false;
        axiom = false;
        first = -1;
      })
    e_internal

let is_internal s = match fst s.key with Ordering.Definition (-1, _) -> true | _ -> false
let semi_infinity = 1 lsl 40

(* E's INT_MAX key of unary_first and const_max: above every arity. *)
let int_max = 1 lsl 40

(* Sort keys (key0, key1, key2, key3) of one symbol; first occurrence breaks the remaining ties. *)
let rec keys precedence ~max_unary_freq s =
  let k1, k2, k3 = base_keys precedence ~max_unary_freq s in
  let k0 =
    match precedence with
    | Occurrence (_, m) ->
        if s.conj then if s.axiom then m.conj_axiom else m.conj_only
        else if s.axiom then m.axiom_only
        else 0
    | _ -> 0
  in
  (k0, k1, k2, k3)

and base_keys precedence ~max_unary_freq s =
  match precedence with
  | Occurrence (p, _) -> base_keys p ~max_unary_freq s
  | Invfreq -> (-s.freq, s.arity, 0)
  | Arity -> (s.arity, 0, 0)
  | Invarity -> (-s.arity, 0, 0)
  | Unary_first -> ((if s.arity = 1 then int_max else s.arity), 0, 0)
  | Const_min -> ((if s.arity = 0 then -semi_infinity else -s.arity), 0, 0)
  | Invfreq_constmin -> if s.arity = 0 then (-semi_infinity, s.freq, 0) else (-s.freq, s.arity, 0)
  | Invfreq_hack ->
      if s.arity = 0 then (-semi_infinity, -s.freq, 0)
      else if s.arity = 1 && s.freq = max_unary_freq then (semi_infinity, 0, 0)
      else (-s.freq, s.arity, 0)
  | Invfreq_conjmax -> ((if s.conj then 1 else 0), -s.freq, s.arity)

(** The unified E precedence, smallest symbol first. *)
let sorted precedence symbols =
  let max_unary_freq =
    List.fold_left (fun m s -> if s.arity = 1 then max m s.freq else m) (-1) symbols
  in
  List.map (fun s -> (keys precedence ~max_unary_freq s, s.first, s)) symbols
  |> List.sort (fun (k, f, _) (k', f', _) -> compare (k, f) (k', f'))
  |> List.map (fun (_, _, s) -> s)

let is_function s = match fst s.key with Ordering.Function _ -> true | _ -> false

(* Weight generation over the unified precedence [order] (smallest first). *)
let generate_weights weights order =
  let n = List.length order in
  let weight = Hashtbl.create (max 16 n) in
  let set s w = Hashtbl.replace weight s.key w in
  (match weights with
  | Unit_weights -> List.iter (fun s -> set s 1) order
  | Precedence_weights ->
      (* Weight(f) = 1 + |{g | g < f}|: the 1-based position in a total precedence. *)
      List.iteri (fun i s -> set s (i + 1)) order
  | Invfreq_rank ->
      (* The most frequent symbols weigh 1, the next distinct frequency 2, ... *)
      let by_freq = List.stable_sort (fun a b -> compare b.freq a.freq) order in
      let _ =
        List.fold_left
          (fun (last, w) s ->
            let w = if Some s.freq = last then w else w + 1 in
            set s (max w 1);
            (Some s.freq, w))
          (None, 0) by_freq
      in
      ()
  | Inv_precedence ->
      (* Weight(f) = 1 + |{g | g > f}| in the total precedence (W_DEFAULT_WEIGHT 1). *)
      List.iteri (fun i s -> set s (n - i)) order
  | Arity_weights | Arity_max0 -> (
      List.iter (fun s -> set s (s.arity + 1)) order;
      if weights = Arity_max0 then
        (* set_maximal_0 (che_to_weightgen.c:234): the greatest symbol of the total
           precedence weighs 0, whatever its arity; constants are reset below. *)
        match List.rev order with
        | s :: _ -> set s 0
        | [] -> ())
  | Selmax -> (
      List.iter (fun s -> set s 1) order;
      match List.rev order with s :: _ -> set s 0 | [] -> ())
  | Precrank20 ->
      let per = float_of_int n /. 20. in
      List.iteri (fun i s -> set s (int_of_float (float_of_int i /. per) + 1)) order);
  weight

type violation = { symbol : Ordering.head * int; reason : string }

(** KBO admissibility with variable weight 1: every constant weighs at least 1, and a unary function
    symbol of weight 0 is the unique such symbol and greater than every other function symbol in the
    class-first precedence of {!Ordering}. Repairs violations in place (weight 1) and returns them.
    Predicate symbols never occur below a function symbol, so any weight is admissible for them;
    function symbols of arity two or more may weigh 0. *)
let admissible ~(rank : Ordering.head * int -> int) (weight : (Ordering.head * int, int) Hashtbl.t)
    =
  let functions =
    Hashtbl.fold
      (fun ((head, arity) as key) w acc ->
        match head with Ordering.Function _ -> (key, arity, w) :: acc | _ -> acc)
      weight []
    |> List.sort compare
  in
  let top =
    List.fold_left
      (fun best (key, _, _) ->
        match best with Some b when rank b >= rank key -> best | _ -> Some key)
      None functions
  in
  let violations = ref [] in
  List.iter
    (fun (key, arity, w) ->
      if arity = 0 && w < 1 then (
        Hashtbl.replace weight key 1;
        violations := { symbol = key; reason = "constant weight below 1" } :: !violations)
      else if w < 0 then (
        Hashtbl.replace weight key 1;
        violations := { symbol = key; reason = "negative weight" } :: !violations)
      else if arity = 1 && w = 0 && Some key <> top then (
        Hashtbl.replace weight key 1;
        violations :=
          { symbol = key; reason = "weight-0 unary symbol is not the greatest function symbol" }
          :: !violations))
    functions;
  List.rev !violations

(** The (rank, weight) table of a strategy for the given initial clauses, plus repaired
    admissibility violations. Ranks are E's unified precedence positions (1-based); a weight-0 unary
    function symbol gets rank [max_int] so that symbols first seen later stay below it. [conjecture]
    marks the symbols of the negated-conjecture clauses (for [Invfreq_conjmax]). *)
let table ?(conjecture = fun _ -> false) ?(axiom = fun _ -> false) ?ranks t (clauses : clause list)
    =
  let symbols = statistics clauses in
  List.iter
    (fun s ->
      s.conj <- conjecture s.key;
      s.axiom <- axiom s.key)
    symbols;
  (if t.e_ranks then
     (* [ranks]: E's pos_rank over E's canonized clause set, when the caller has E's view of the
        input (E_initial.pos_ranks); otherwise over the clauses in their order here. *)
     let ranks = match ranks with Some r -> r | None -> e_pos_ranks clauses in
     List.iter (fun s -> s.first <- Option.value ~default:0 (Hashtbl.find_opt ranks s.key)) symbols);
  let symbols = symbols @ if t.e_signature then internal_symbols () else [] in
  let order = sorted t.precedence symbols in
  let weight = generate_weights t.weights order in
  (* Every constant, function or propositional predicate, weighs max(to_const_weight, 1); E keeps
     the generated weights (at least 1) for to_const_weight 0. *)
  List.iter
    (fun s ->
      if s.arity = 0 then
        if t.e_signature && t.const_weight = 0 then
          Hashtbl.replace weight s.key (max 1 (Hashtbl.find weight s.key))
        else Hashtbl.replace weight s.key (max t.const_weight 1))
    order;
  let order = List.filter (fun s -> not (is_internal s)) order in
  let positions = Hashtbl.create (max 16 (List.length order)) in
  List.iteri (fun i s -> Hashtbl.replace positions s.key (i + 1)) order;
  let rank key = Option.value ~default:0 (Hashtbl.find_opt positions key) in
  let violations = admissible ~rank weight in
  let result = Hashtbl.create (max 16 (List.length order)) in
  List.iter
    (fun s ->
      let w = Hashtbl.find weight s.key in
      let r = if w = 0 && s.arity = 1 && is_function s then max_int else rank s.key in
      Hashtbl.replace result s.key (r, w))
    order;
  (result, violations)

(** Install the instance for [clauses] in [order] (its precedence table, unified for [e_signature],
    and its ordering); returns the repaired admissibility violations. *)
let install ?conjecture ?axiom ?ranks t order (clauses : clause list) =
  let table, violations = table ?conjecture ?axiom ?ranks t clauses in
  Ordering.install_table ~unified:t.e_signature ~kind:t.ordering order table;
  violations
