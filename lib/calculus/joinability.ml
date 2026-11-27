open Wire
(** Unit-equality redundancy tests of a lean worker (EQ-UNIT): ground joinability of an unorientable
    unit equation (Martin and Nipkow; the case split over variable orders of Twee, without its model
    weakening) and connectedness of a superposition conclusion below its peak (Bachmair and
    Dershowitz; Twee's connectedness step). A test only decides that a clause may be deleted as
    redundant: it records no proof step, and a deleted clause never reaches a certificate, so the
    kernel never depends on it.

    Both tests rewrite terms (not clauses) with the live rules of a {!Demodulation.t} with ordered
    rewriting: the oriented rules and both directions of the unorientable equations (the worker's
    demodulator, or an index of its active equations kept for the tests alone). Every test is
    bounded by a budget of rule trials ([work]) and of rewrite steps per term ([steps]); an
    exhausted test answers "not redundant", so a bound only keeps a clause. *)

exception Exhausted

type stats = {
  mutable ground_tests : int;  (** ground-joinability tests started *)
  mutable ground_joined : int;  (** equations found ground joinable *)
  mutable ground_cases : int;  (** variable orders examined *)
  mutable connected_tests : int;  (** connectedness tests started *)
  mutable connected : int;  (** conclusions found connected below their peak *)
  mutable exhausted : int;  (** tests stopped by the budget *)
  mutable trials : int;  (** rule trials (matching attempts) of all tests *)
  mutable comparisons : int;  (** ordering checks under a variable order *)
}

let stats () =
  {
    ground_tests = 0;
    ground_joined = 0;
    ground_cases = 0;
    connected_tests = 0;
    connected = 0;
    exhausted = 0;
    trials = 0;
    comparisons = 0;
  }

(* Distinct variables in order of first occurrence. *)
let variables terms =
  let seen = ref [] in
  let rec visit = function
    | V v -> if not (List.mem v !seen) then seen := v :: !seen
    | Fn (_, ts) -> List.iter visit ts
  in
  List.iter visit terms;
  List.rev !seen

let rec occurs x = function V y -> x = y | Fn (_, ts) -> List.exists (occurs x) ts
let rec substitute f = function V v -> f v | Fn (g, ts) -> Fn (g, List.map (substitute f) ts)

(* {2 KBO under a variable order}

   [rank] is a strict total order of the variables of the compared terms (a model). [greater_in]
   holds only if s theta > t theta in the KBO for every ground substitution theta with
   rank x < rank y implies x theta < y theta. It is Twee's "KBO under assumptions" (lessIn): in the
   KBO a smaller ground term never weighs more, so with v_1 < ... < v_k the weight difference
   W + sum_i d_i w(v_i theta) (d_i = occurrences in s minus occurrences in t, W the difference of
   the symbol weights) is bounded below iff every suffix sum d_j + ... + d_k is nonnegative, and
   then its minimum is W + wmin * (d_1 + ... + d_k), with [wmin] the least weight of a ground
   term (the lightest constant). A positive minimum decides; a zero minimum falls back to the
   precedence and a lexicographic comparison of the arguments under the same model, which holds
   for every theta, so in particular for those of equal weight. *)

let rec greater_in order ~wmin rank s t =
  match Ordering.kind order with
  | Ordering.Lpo -> Ordering.greater ~order s t
  | Ordering.Kbo -> s <> t && weight_greater order ~wmin rank s t

and weight_greater order ~wmin rank s t =
  (* (rank, occurrences in s minus occurrences in t) per variable. *)
  let counts = ref [] in
  let rec count k = function
    | V v ->
        let r = rank v in
        let rec bump = function
          | [] -> [ (r, k) ]
          | (q, d) :: rest when q = r -> (q, d + k) :: rest
          | x :: rest -> x :: bump rest
        in
        counts := bump !counts
    | Fn (_, ts) -> List.iter (count k) ts
  in
  count 1 s;
  count (-1) t;
  let by_rank = List.sort (fun (a, _) (b, _) -> compare b a) !counts in
  (* Suffix sums from the greatest variable down. *)
  let rec bounded sum = function
    | [] -> Some sum
    | (_, d) :: rest ->
        let sum = sum + d in
        if sum < 0 then None else bounded sum rest
  in
  match bounded 0 by_rank with
  | None -> false
  | Some total ->
      let minimum =
        fst (Ordering.wire_weights order s) - fst (Ordering.wire_weights order t) + (wmin * total)
      in
      minimum > 0 || (minimum = 0 && lex_in order ~wmin rank s t)

and lex_in order ~wmin rank s t =
  match (s, t) with
  | Fn (f, ss), Fn (g, ts) ->
      let c =
        Ordering.compare_heads order
          (Ordering.Function f, List.length ss)
          (Ordering.Function g, List.length ts)
      in
      if c > 0 then true
      else if c < 0 then false
      else if Sym.equal f g && List.length ss = List.length ts then
        let rec lex = function
          | x :: xs, y :: ys -> if x = y then lex (xs, ys) else greater_in order ~wmin rank x y
          | _ -> false
        in
        lex (ss, ts)
      else false
  | Fn _, V x ->
      (* s properly contains x, or a variable above x: s theta >= y theta > x theta. *)
      occurs x s || List.exists (fun y -> rank y > rank x) (variables [ s ])
  | V x, V y -> rank x > rank y
  | V _, Fn _ -> false

(* {2 Rewriting terms} *)

(* One rewrite of [term]: leftmost-outermost, the first live rule (oldest first, as
   Demodulation.rewrite_first tries them) whose instance is accepted: [local rule u r] on the
   redex [u] and its replacement [r], then [whole] on the rewritten term (lazily). [memo] holds
   subterms in which no rule passed [local]: they stay irreducible within one normalization run
   (a [whole] rejection depends on the context, so such a subterm is not remembered). *)
let step ?(irreducible = fun _ -> false) ?(normal = false) ~tick ~local ~whole ~memo ~oriented
    (rules : Demodulation.t) term =
  let exception Found of term in
  (* [visit] answers whether the subtree had no context-dependent rejection, and whether no
     oriented rule applies in it. [known]: no oriented rule applies in the subtree ([normal] for
     the first scan of a normal form, [irreducible] = the worker's normal-form memo, [oriented] =
     subterms found so earlier in this test: oriented rules apply whatever the context and the
     variable order), so only the unoriented rules are tried. *)
  let rec visit known reverse_path u =
    match u with
    | V _ -> (true, true)
    | Fn (f, args) ->
        if Hashtbl.mem memo u then (true, true)
        else
          let known = known || irreducible u || Hashtbl.mem oriented u in
          let clean = ref true in
          let key = (f, List.length args) in
          let candidates =
            if known then Demodulation.unoriented rules key else Demodulation.candidates rules key
          in
          for k = 0 to Array.length candidates - 1 do
            let rule = candidates.(k) in
            tick ();
            match Subsumption.term [] rule.lhs u with
            | exception Subsumption.No_match -> ()
            | sigma ->
                if rule.extra = [] || rules.minimal <> None then
                  let sigma = Demodulation.complete rules rule sigma in
                  let r =
                    substitute
                      (fun v -> Option.value ~default:(V v) (List.assoc_opt v sigma))
                      rule.rhs
                  in
                  if local rule u r then
                    let rewritten = lazy (Clause.put_term (List.rev reverse_path) r term) in
                    if whole rule rewritten then raise (Found (Lazy.force rewritten))
                    else clean := false
          done;
          (* No oriented rule applies at [u]: one that matched would have been accepted. *)
          let settled = ref true in
          let rec children j = function
            | [] -> ()
            | a :: rest ->
                let c, o = visit known (j :: reverse_path) a in
                if not c then clean := false;
                if not o then settled := false;
                children (j + 1) rest
          in
          children 0 args;
          if !clean then Hashtbl.replace memo u ();
          if !settled && not known then Hashtbl.replace oriented u ();
          (!clean, known || !settled)
  in
  match visit normal [] term with _ -> None | exception Found t -> Some t

(* [normal]: [term] is in normal form under the rules with every instance decreasing (the
   worker's own rewriting just stopped on it), so its first scan tries only the unoriented ones. *)
let normalize ?irreducible ?(normal = false) ~tick ~steps ~local ~whole ~memo ~oriented rules term =
  let rec go n normal term =
    match step ?irreducible ~normal ~tick ~local ~whole ~memo ~oriented rules term with
    | None -> term
    | Some next -> if n >= steps then raise Exhausted else go (n + 1) false next
  in
  go 1 normal term

(* The ordered set partitions (total preorders) of [xs], each as its blocks in ascending order:
   every way the variables of an equation can compare in a ground instance. Most blocks first,
   so that a test that fails, the common case, fails on its first, most general orders. *)
let orders xs =
  let rec go = function
    | [] -> [ [] ]
    | x :: rest ->
        List.concat_map
          (fun blocks ->
            let n = List.length blocks in
            (* x joins block i, or forms a new block at position i. *)
            List.init n (fun i -> List.mapi (fun j b -> if i = j then x :: b else b) blocks)
            @ List.init (n + 1) (fun i ->
                List.filteri (fun j _ -> j < i) blocks
                @ [ [ x ] ]
                @ List.filteri (fun j _ -> j >= i) blocks))
          (go rest)
  in
  go xs
  |> List.map (fun blocks -> (List.length blocks, blocks))
  |> List.stable_sort (fun (a, _) (b, _) -> compare b a)
  |> List.map snd

(* Twee's connectedness rewriting and the per-model rewriting order: a model where the
   variables compare by [rank]. *)
let in_model order ~wmin rank u r = greater_in order ~wmin rank u r

(** [ground_joinable ... s t]: every ground instance of [s = t] is joinable by ordered rewriting
    with [rules] ([Demodulation.t] with ordered rewriting). For every total preorder of the
    variables, the variables of a block are identified and the blocks are ordered; [s] and [t] are
    rewritten to normal form with the rule instances that decrease in every ground instance of that
    order ({!greater_in}), and must meet. At most [max_variables] variables; every total preorder is
    tried (13 for three variables, 75 for four). *)
let ground_joinable ?irreducible ?(normal = false) ?(max_variables = 4) ~work ~steps ~order ~wmin
    stats rules s t =
  stats.ground_tests <- stats.ground_tests + 1;
  let xs = variables [ s; t ] in
  if List.length xs > max_variables || xs = [] then false
  else
    let left = ref work in
    let tick () =
      stats.trials <- stats.trials + 1;
      decr left;
      if !left < 0 then raise Exhausted
    in
    (* Oriented rules apply whatever the order of the variables: one table for all cases of
       the same terms. Identified terms differ, but the table is keyed by terms. *)
    let oriented = Hashtbl.create 64 in
    try
      let joined =
        List.for_all
          (fun blocks ->
            stats.ground_cases <- stats.ground_cases + 1;
            (* Each block becomes its first variable; ranks follow the block order. *)
            let representative = Hashtbl.create 8 and ranks = Hashtbl.create 8 in
            List.iteri
              (fun i block ->
                let r = List.hd block in
                Hashtbl.replace ranks r i;
                List.iter (fun x -> Hashtbl.replace representative x r) block)
              blocks;
            let trivial = List.for_all (fun block -> List.length block = 1) blocks in
            (* Without an identification the terms stay the stored ones, which the worker's
               normal-form memo knows. *)
            let identify u =
              if trivial then u else substitute (fun v -> V (Hashtbl.find representative v)) u
            in
            let irreducible = if trivial then irreducible else None
            and normal = trivial && normal in
            let s = identify s and t = identify t in
            s = t
            ||
            let rank v = Hashtbl.find ranks v in
            let local (rule : Demodulation.rewrite) u r =
              rule.oriented || in_model order ~wmin rank u r
            and whole _ _ = true
            and memo = Hashtbl.create 64 in
            normalize ?irreducible ~normal ~tick ~steps ~local ~whole ~memo ~oriented rules s
            = normalize ?irreducible ~normal ~tick ~steps ~local ~whole ~memo ~oriented rules t)
          (orders xs)
      in
      if joined then stats.ground_joined <- stats.ground_joined + 1;
      joined
    with Exhausted ->
      stats.exhausted <- stats.exhausted + 1;
      false

(** [connected ... ~peak a b]: [a = b] is connected below [peak]: both sides rewrite to the same
    term by steps whose results all stay below [peak] in every ground instance (the plain ordering,
    stable under substitution). Each step uses an instance of a live equation; which direction it
    takes only has to make the rewriting terminate, so it follows the ordering under one fixed order
    of the variables (with [flip], then the reverse one, as Twee's flipped critical pair). An
    oriented rule is applied without the peak check: in every ground instance in which the
    superposition is an inference of the calculus both sides are below the peak, and oriented steps
    only decrease. Every intermediate term and every equation instance used is then below the peak
    in every such ground instance, so the superposition inference that produced [a = b] from [peak]
    is redundant (a critical-pair criterion): its conclusion need not be kept. *)
let connected ?irreducible ?(normal = false) ?(flip = true) ~work ~steps ~order ~wmin stats rules
    ~peak a b =
  stats.connected_tests <- stats.connected_tests + 1;
  let left = ref work in
  let tick () =
    stats.trials <- stats.trials + 1;
    decr left;
    if !left < 0 then raise Exhausted
  in
  let xs = variables [ a; b; peak ] in
  let oriented = Hashtbl.create 64 in
  (* An oriented rule decreases every instance, so from a side that is below the peak in an
     instance it stays below; an unorientable equation is used only when the result is below the
     peak in every instance. Whether a second variable order can differ: some unorientable
     equation matched. *)
  let unoriented = ref false in
  let attempt rank =
    let local (rule : Demodulation.rewrite) u r =
      rule.oriented
      ||
      (unoriented := true;
       stats.comparisons <- stats.comparisons + 1;
       in_model order ~wmin rank u r)
    and whole (rule : Demodulation.rewrite) rewritten =
      rule.oriented || Ordering.greater ~order peak (Lazy.force rewritten)
    and memo = Hashtbl.create 64 in
    normalize ?irreducible ~normal ~tick ~steps ~local ~whole ~memo ~oriented rules a
    = normalize ?irreducible ~normal ~tick ~steps ~local ~whole ~memo ~oriented rules b
  in
  let position v =
    let rec find i = function [] -> 0 | x :: rest -> if x = v then i else find (i + 1) rest in
    find 0 xs
  in
  try
    let joined =
      a = b || attempt position || (flip && !unoriented && attempt (fun v -> -position v))
    in
    if joined then stats.connected <- stats.connected + 1;
    joined
  with Exhausted ->
    stats.exhausted <- stats.exhausted + 1;
    false

(** The weight of the lightest constant of [constants] (1 without one), the [wmin] of {!greater_in}:
    no ground term weighs less. *)
let least_weight order constants =
  match constants with
  | [] -> 1
  | _ ->
      List.fold_left
        (fun m c -> min m (Ordering.weight order (Ordering.of_term c)))
        max_int constants
