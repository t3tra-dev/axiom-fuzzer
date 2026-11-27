(** Per-worker search strategy: the literal selection, term ordering, rewriting and clause-selection
    settings of one heuristic worker. A strategy changes which proofs are found and how fast, never
    which proofs are accepted: every reported refutation is checked by the kernel, and the reference
    enumerator ignores it.

    [production] is the standard calculus. Other values are portfolio members or evaluation
    variants; they are internal configuration, not CLI modes. Extend the record with a field whose
    [production] value keeps the current behaviour. *)

type selection =
  | First_negative
      (** Production: the first negative literal in normalized order, which the bounded index
          lookahead may revise when the clause is selected. *)
  | Max_complex_avoid_pos_pred
      (** E's SelectMaxLComplexAvoidPosPred: no selection when at most one literal is maximal;
          otherwise the maximal, most complex negative literal, preferring pure-variable and ground
          literals and avoiding predicates that also occur positively. The lookahead is not used. *)
  | Max_complex_avoid_pos_pred_lookahead
      (** As [Max_complex_avoid_pos_pred], but the lookahead may revise a negative selection. *)
  | Max_complex  (** Always the most complex negative literal, ignoring maximality. *)
  | Vampire_best_10
      (** Vampire's selection 10 (CompleteBestLiteralSelector with Comparator10: negative equalities
          first, then the greatest symbol count): with a negative literal in the clause, the best
          negative literal by that order (the first one in clause order on a tie); otherwise no
          selection (every maximal literal). The lookahead is not used. *)

type precedence =
  | Alphabetical  (** Production: symbol order by (head, name, arity), unit weights. *)
  | Invfreq  (** E invfreq precedence with invfreqrank symbol weights (constants 1). *)
  | E_instance of Eorder.t
      (** An E term-ordering instance generated from the input clauses ({!Eorder.install}): KBO6
          with E's weights, or LPO4 on E's precedence. *)

type queues =
  | Standard_queues  (** Production: weight, unit weight, age, preferred and class turns. *)
  | Plain_queues  (** Only the age and the size/unit weight heaps. *)

type weight = Standard_weight  (** Production: [Clause.weight]. *)

type t = {
  name : string;
  selection : selection;
  maximal_candidates : bool;
      (** When a clause selects nothing, restrict its inference and index candidates to literals
          that no other literal exceeds before substitution. The ordering is stable under
          substitution, so the dropped literals can never pass the post-unification maximality
          check: the inferences are the same, only futile unification attempts disappear. *)
  precedence : precedence;
  ordered_rewriting : bool;
      (** Also rewrite with unorientable unit equations, both directions, when the instance
          decreases in the term ordering. *)
  queues : queues;
  weight : weight;
  heuristic : Heuristic.t option;
      (** A ported E heuristic (Heuristic): its E literal selection, KBO instance, queue mix and
          lean given-clause loop replace [selection], [precedence], [queues] and [weight]. *)
  unfold : int option;
      (** E's equational-definition unfolding of the initial clause set ([Unfold]) with this
          eq-unfold-limit, before the term ordering is computed; [None] keeps the input clauses. A
          preprocessing choice of the search: the rewritten clauses are ordinary paramodulation
          steps from the input clauses. *)
}

let production =
  {
    name = "production";
    selection = First_negative;
    maximal_candidates = false;
    precedence = Alphabetical;
    ordered_rewriting = false;
    queues = Standard_queues;
    weight = Standard_weight;
    heuristic = None;
    unfold = None;
  }

(* E-style maximality-aware selection: the portfolio member for backward
   chaining from goals through Horn rules whose head dominates the body. *)
let calc_e =
  {
    production with
    name = "calc:e";
    selection = Max_complex_avoid_pos_pred;
    maximal_candidates = true;
    (* Unfolding lost no problem and solved more of the development corpus's problems that have a
       definition. *)
    unfold = Some Unfold.default_limit;
  }

(* Evaluation variants of calc:e. proto:e makes every literal of an unselected clause a candidate
   (no maximality filter and no unfolding); proto:combo adds the invfreq precedence and ordered
   rewriting. *)
let proto_e = { calc_e with name = "proto:e"; maximal_candidates = false; unfold = None }

(* The production calculus, queues and producers on an LPO: E's LPO4 with the arity precedence
   (higher arity is greater, E's first-occurrence ranks break ties), the default precedence of
   Vampire's LPO slices. An evaluation member, not in [diversified]. *)
let calc_lpo = { production with name = "calc:lpo"; precedence = E_instance (Heuristic.lpo4 Arity) }

(* The production calculus, queues, producers and AVATAR with Vampire's literal selection 10, an
   evaluation baseline for Vampire's selection functions (the selection of the Vampire slices that
   solved SET209-6 and SET211-6 when selection 1011 timed out). An evaluation member, not in
   [diversified]. *)
let calc_v10 =
  { production with name = "calc:v10"; selection = Vampire_best_10; maximal_candidates = true }

let named =
  [
    production;
    calc_e;
    proto_e;
    { proto_e with name = "proto:ela"; selection = Max_complex_avoid_pos_pred_lookahead };
    { proto_e with name = "proto:maxw"; selection = Max_complex };
    { proto_e with name = "proto:combo"; precedence = Invfreq; ordered_rewriting = true };
    calc_lpo;
    calc_v10;
  ]
  @ List.map
      (fun (h : Heuristic.t) ->
        {
          production with
          name = h.name;
          ordered_rewriting = h.ordered_rewriting;
          (* E only tries literals that are maximal before substitution. *)
          maximal_candidates = true;
          heuristic = Some h;
          unfold = h.unfold;
        })
      Heuristic.named

let names = List.map (fun s -> s.name) named

let of_name name =
  match List.find_opt (fun s -> s.name = name) named with
  | Some s -> s
  | None ->
      invalid_arg (Printf.sprintf "unknown strategy %S (known: %s)" name (String.concat ", " names))

(** Worker strategies of a portfolio.
    - [Balanced], the default ([Scheduler.default_config]): the composition rule for every worker
      count W ([balanced]). Workers [0 .. ceil(W/2) - 1] run the engine strategy ([production]
      unless a caller sets another) at queue phases [0 .. ceil(W/2) - 1], exactly the all-production
      portfolio of that size; the other [floor(W/2)] workers take the [diversified] members in
      round-robin order, so no member runs on more than [ceil(floor(W/2) / 4)] workers. One worker
      runs the engine strategy.
    - [Uniform]: every worker runs the engine strategy; with the default this is the all-production
      configuration (A/A checks).
    - [Standard]: with two or more heuristic workers, worker 1 runs [calc_e] and every other worker
      the engine strategy. One worker runs the engine strategy.
    - [Workers]: one named strategy per worker.

    Every worker also has a queue phase ([resolve], [phase_of]): a production-queue strategy runs at
    its worker index, and a ported E heuristic at its copy index. Two workers repeat one search when
    they run the same strategy at phases congruent modulo its period ([queue_period]); a ported E
    heuristic is deterministic, so every portfolio refuses such a repeat of it
    ([deterministic_repeat]). *)
type portfolio = Balanced | Standard | Uniform | Workers of t list

(** The period of a ported E heuristic's queue mix in the phase ([Passive.mix_period]): 11 for the
    208 mix of [e208] and [sat001], 26 for [y1346]. *)
let heuristic_period (h : Heuristic.t) =
  Passive.mix_period (List.map (fun (q : Evaluation.queue) -> q.count) h.queues)

(** The period of a strategy's selection schedule in the queue phase, for an engine with weight
    ratio [ratio] and clause weight [policy]: the queue mix's period for a ported E heuristic,
    otherwise the production queue turns' ([Passive.turn_period], 22 for the default ratio 10).
    Phases congruent modulo it select by the same schedule: a deterministic search repeats, and a
    production-queue search differs at most by the wall-clock scheduling costs. *)
let queue_period ~policy ~ratio s =
  match s.heuristic with
  | Some h -> heuristic_period h
  | None -> Passive.turn_period ~policy ~plain:(s.queues = Plain_queues) ~ratio ()

type worker = { strategy : t; phase : int }
(** One worker of a resolved portfolio: its strategy and its queue phase relative to the internal
    phase base ([Scheduler.config.phase_base], 0 by default). *)

(** The queue phases of a list of worker strategies. A production-queue strategy ([production],
    [calc:e], ...) runs at its worker index. A ported E heuristic runs at its copy index: the number
    of earlier workers that run the same strategy. Its first copy therefore runs at phase 0, E's own
    start, and every further copy at the next phase. *)
let phases strategies =
  let copies = Hashtbl.create 8 in
  List.mapi
    (fun index s ->
      match s.heuristic with
      | None -> { strategy = s; phase = index }
      | Some _ ->
          let k = Option.value ~default:0 (Hashtbl.find_opt copies s.name) in
          Hashtbl.replace copies s.name (k + 1);
          { strategy = s; phase = k })
    strategies

(** The first worker that repeats an earlier worker's deterministic search: the same ported E
    heuristic at a phase congruent modulo its period. Production-queue strategies are not checked.
*)
let deterministic_repeat workers =
  let rec go seen = function
    | [] -> None
    | w :: rest -> (
        match w.strategy.heuristic with
        | Some h ->
            let key = (w.strategy.name, w.phase mod heuristic_period h) in
            if List.mem key seen then Some w else go (key :: seen) rest
        | None -> go seen rest)
  in
  go [] workers

let refuse_repeat (w : worker) context =
  let period = Option.fold ~none:1 ~some:heuristic_period w.strategy.heuristic in
  invalid_arg
    (Printf.sprintf
       "strategy %s is deterministic: %s would repeat its search at queue phase %d (modulo its \
        period %d; name it on at most %d workers)"
       w.strategy.name context (w.phase mod period) period period)

let check_repeats context workers =
  Option.iter (fun w -> refuse_repeat w context) (deterministic_repeat workers);
  workers

(** The diversified half of [Balanced], in the order workers take it: the three ported E heuristics,
    each a distinct deterministic search that differs from production in literal selection, term
    ordering and clause selection at once, then [calc:e] (E's literal selection on the production
    queues). Workers take them round-robin: copy k of an E heuristic runs at its queue phase k (its
    copy index), and [calc:e] at its worker index, as every production-queue strategy. Not members:
    the E-instance variants (e208k, y1346k, sat001k: the same heuristics on E's exact KBO instance,
    measured to solve the same cases as the plain ones) and the proto:* research variants (proto:e
    makes calc:e's inferences without its candidate filter). *)
let diversified = List.map of_name [ "e208"; "y1346"; "sat001" ] @ [ calc_e ]

(** The [Balanced] composition of [workers] workers: [base] on the first [ceil(workers/2)], then the
    [diversified] members round-robin. The two halves differ by at most one worker, and no
    diversified member runs on more than [ceil(floor(workers/2) / 4)] workers. Each worker count
    extends the composition of the one before by one worker; up to 8 workers it is the composition
    of the earlier rule (members in order, calc:e last). *)
let balanced ~base ~workers =
  let production = (workers + 1) / 2 and members = Array.of_list diversified in
  List.init workers (fun i ->
      if i < production then base else members.((i - production) mod Array.length members))

(** The workers of a portfolio of [workers] workers with [base] as the engine strategy, with their
    queue phases ([phases]). Refuses a portfolio that repeats a deterministic search. *)
let resolve portfolio ~base ~workers =
  if workers < 1 then invalid_arg "Strategy.assign: worker index";
  match portfolio with
  | Balanced ->
      check_repeats
        (Printf.sprintf "the balanced portfolio of %d workers" workers)
        (phases (balanced ~base ~workers))
  | Uniform ->
      check_repeats
        (Printf.sprintf "%d workers" workers)
        (phases (List.init workers (fun _ -> base)))
  | Standard ->
      check_repeats
        (Printf.sprintf "the standard portfolio of %d workers" workers)
        (phases (List.init workers (fun i -> if i = 1 then calc_e else base)))
  | Workers strategies ->
      if List.length strategies <> workers then
        invalid_arg
          (Printf.sprintf "%d worker strategies given for %d workers" (List.length strategies)
             workers);
      check_repeats "the worker list" (phases strategies)

let assign portfolio ~base ~workers index =
  if workers < 1 || index < 0 || index >= workers then invalid_arg "Strategy.assign: worker index";
  (List.nth (resolve portfolio ~base ~workers) index).strategy

let phase_of portfolio ~base ~workers index =
  if workers < 1 || index < 0 || index >= workers then invalid_arg "Strategy.assign: worker index";
  (List.nth (resolve portfolio ~base ~workers) index).phase

(** Evaluation-only portfolio specification: [balanced], [standard], one strategy name for every
    worker, or a comma-separated name per worker. Returns the portfolio and, for a single name, the
    base strategy; the caller resets the base to [production] when none is returned, so the last
    specification fully determines the workers. Phases follow [phases]: a name repeated in a list
    runs at its worker index (production queues) or its copy index (E), and a list that repeats a
    deterministic search (an E strategy named more often than its period) is refused.

    Spec strings:
    - the default rule: [balanced] (any worker count; for example [production,production,e208,y1346]
      at 4 workers);
    - all production: [production] (any worker count; the A/A baseline);
    - Standard (worker 1 = calc:e): [standard], or explicitly
      [production,calc:e,production,production] at 4 workers;
    - a list such as [e208,production,y1346,production] (production on queue phases 1 and 3; 4
      workers only). *)
let portfolio_of_string spec =
  match String.split_on_char ',' spec with
  | [ "balanced" ] -> (Balanced, None)
  | [ "standard" ] -> (Standard, None)
  | [ name ] -> (Uniform, Some (of_name name))
  | names ->
      let strategies = List.map of_name names in
      ignore (check_repeats "the worker list" (phases strategies));
      (Workers strategies, None)
