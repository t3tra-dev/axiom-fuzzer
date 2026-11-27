open Wire

type limits = { max_given : int; max_generated : int; max_retained : int; seconds : float }
(** Hard caps. Reaching a count cap stops this worker for the rest of the run, so the defaults leave
    them unlimited and memory is governed by [budget]. *)

let default_limits =
  { max_given = max_int; max_generated = max_int; max_retained = max_int; seconds = 10. }

(* Finite caps for the short searches of single attempts: axiom-minimize's reduction attempts and
   axiom-mutate's searches of one mutant (also the defaults of earlier releases). *)
let attempt_limits =
  { max_given = 2000; max_generated = 50000; max_retained = 20000; seconds = 10. }

type budget = { heap_words : int; proof_nodes : int }
(** Soft memory budgets of one engine; 0 disables one. [heap_words] bounds the engine's [footprint]:
    a deterministic estimate, in 64-bit words, of the search state it keeps reachable, maintained
    from engine counts (stored proof nodes, suspended Goal and transfer cursors, Goal index
    postings) and never read from the garbage collector. [proof_nodes] bounds stored first-order
    plus Boolean proof nodes. Both are checked after every engine step, a deterministic point of the
    search. Over budget, the engine drops suspended Goal and transfer cursors (they continue from
    their marks), collects and, if the pressure persists, trims derived Passive clauses. It stops
    only when its footprint stays at [ceiling] times its budget, when the node budget cannot be met,
    or at the environment-dependent safety limit ([safety]). *)

let default_budget = { heap_words = Footprint.of_mib 256; proof_nodes = 1000000 }
let no_budget = { heap_words = 0; proof_nodes = 0 }

(* The CLI's budget for each worker: [Some mib] MiB of footprint words ([Some 0]: no budget at
   all, footprint and nodes), [None] the default. It is the same for every worker count and every
   machine. *)
let worker_budget ?mib () =
  match mib with
  | Some n when n < 0 -> invalid_arg "worker_budget: negative budget"
  | Some 0 -> no_budget
  | Some n -> { default_budget with heap_words = Footprint.of_mib n }
  | None -> default_budget

type config = {
  limits : limits;
  budget : budget;
  avatar : bool;
  weight_ratio : int;
  clause_weight : Passive.policy;
  lookahead : int;
  fingerprint : bool;
  indexed : bool;
  subsumption : bool;
  subsumption_indexed : bool;
  equality_indexed : bool;
  backward_subsumption : bool;
  variants : bool;
  ordered : bool;
  selection : bool;
  demodulation : bool;
  backward_demodulation : bool;
  variable_positions : bool;
  cnf_mode : cnf_mode;
  collect_every : int;
  collect_adaptive : bool;
  strategy : Strategy.t;
      (** Literal selection, term ordering, rewriting and clause-selection settings of this worker;
          [Strategy.production] is the standard calculus. *)
  goal_names : string list;
      (** Axioms whose TPTP role is negated_conjecture. A search-only hint for conjecture-relative
          evaluations; roles never reach a certificate. *)
  normal_form : bool;
      (** A ported E heuristic (lean worker) rewrites a new clause to normal form within one
          admission, as E's ForwardModifyClause does: the clauses between the first and the last
          rewrite are proof-only nodes and only the normal form is admitted. Without it, as in
          production, every rewrite step is a clause that runs the whole admission again. *)
  given_at_once : bool;
      (** A lean worker processes the replacement of a given clause that it simplified at selection
          in the same step, as E's ProcessClause does after ForwardContractClause, instead of
          queueing the replacement in Passive. Off by default: in this loop, with its admission-time
          simplification, it solved fewer problems of the development corpus at a lower throughput
          (an evaluation variant, AXIOM_LEAN_NF=both). *)
  eq_instances : bool;
      (** EQ-UNIT, a lean worker with ordered rewriting: its unorientable unit equations whose sides
          have different variables are rules too, and a right-side variable that the left side lacks
          is bound to the least constant of the problem (E's rewrite_strong_rhs_inst). Every rewrite
          is still one Paramodulate step, whose substitution binds that variable. *)
  eq_ground_joinable : bool;
      (** EQ-UNIT: a lean worker (any ported E heuristic) deletes an unorientable positive unit
          equation that is ground joinable with its active unit equations
          ({!Joinability.ground_joinable}), at admission and again when it is selected. *)
  eq_connected : bool;
      (** EQ-UNIT: a lean worker deletes an unorientable superposition conclusion between two
          positive unit equations that is connected below its peak ({!Joinability.connected}). *)
  vampire_symbols : (Ordering.head * int, int) Hashtbl.t option;
      (** Vampire's symbol numbers of the input as its parser assigns them
          ({!Vampire.parse_order_of_text}), a search-only hint for the Vampire slice members' tie
          breaks and predicate levels; [None]: numbered from the Source formulas. *)
  e_text : E_initial.text option;
      (** E's view of the problem text ({!E_initial.of_text}): its symbol codes in E's parse order
          and every cnf clause as written, a search-only hint for the E ports' tie breaks (the
          initial evaluation order and the E instance's precedence ties); [None]: numbered from the
          clauses. *)
  equivalence : Contraction.equivalence;
      (** When Contraction's literal rewriting with an equivalence may retire the rewritten clause:
          [Contraction.Derive] (the default) only when that is a redundancy deletion, so never a
          unit, and where [Contraction.Legacy] would retire a clause it keeps the clause and adds
          the rewritten clause as an ordinary resolvent with the side clause;
          [Contraction.Redundant] (AXIOM_EQUIVALENCE=redundant) the redundancy deletions only;
          [Contraction.Legacy] (the evaluation hook AXIOM_EQUIVALENCE=legacy) on any strict
          decrease, which is refutationally incomplete. A Vampire slice member keeps Vampire's own
          condition (ForwardLiteralRewriting: the legacy one) whatever this says. *)
  fresh_refutation : bool;
      (** An engine other than a Vampire slice member whose refutation ends in an AVATAR Boolean
          refutation also re-solves the same Boolean inputs in a new solver after the search and
          certifies whichever proof has fewer steps after pruning (true, the default; a Vampire
          member always uses the fresh one when it is smaller). Only the certificate changes. False
          keeps the incremental refutation (the evaluation hook
          AXIOM_AVATAR_REFUTATION=incremental). *)
  ground_explanation : Ground.explanation;
      (** How the ground congruence closure explains a conflict ({!Ground.explanation}):
          [Ground.Short] (the default) explains a long final conflict by the cheapest paths with
          shared lemmas, which changes only the certificate; [Ground.Forest] (the evaluation hook
          AXIOM_GROUND_EXPLANATION=forest) along the union-find forest. *)
}

let default_config =
  {
    limits = default_limits;
    budget = default_budget;
    avatar = true;
    weight_ratio = 10;
    clause_weight = Passive.Mixed;
    lookahead = 64;
    fingerprint = true;
    indexed = true;
    subsumption = true;
    subsumption_indexed = true;
    equality_indexed = true;
    backward_subsumption = true;
    variants = true;
    ordered = true;
    selection = true;
    demodulation = true;
    backward_demodulation = true;
    variable_positions = false;
    cnf_mode = Hybrid;
    collect_every = 64;
    collect_adaptive = true;
    strategy = Strategy.production;
    goal_names = [];
    normal_form = true;
    given_at_once = false;
    eq_instances = false;
    eq_ground_joinable = false;
    eq_connected = false;
    vampire_symbols = None;
    e_text = None;
    equivalence = Contraction.Derive;
    fresh_refutation = true;
    ground_explanation = Ground.Short;
  }

type metrics = {
  mutable generated : int;
  mutable retained : int;
  mutable given : int;
  mutable redundant : int;
  mutable tautologies : int;
  mutable duplicates : int;
  mutable variants : int;
  mutable memory_samples : int;
  mutable subsumed : int;
  mutable subsumption_trials : int;
  mutable backward_subsumed : int;
  mutable given_subsumed : int;
  mutable demodulated : int;
  mutable backward_demodulated : int;
  mutable backward_unit_cut : int;
      (** [Heuristic.loop.backward]: active clauses a unit given simplified (E's
          eliminate_unit_simplified_clauses). *)
  mutable backward_demodulation_candidates : int;
  mutable backward_demodulation_baseline : int;
  mutable subsumption_exhausted : int;
  mutable subsumption_resolved : int;
  mutable resolution_trials : int;
  mutable peak_live_words : int;
  mutable allocated_words : float;
  mutable collections : int;
  mutable reclaimed_nodes : int;
  mutable reclaimed_terms : int;
  mutable lookahead_postings : int;
  mutable lookahead_exhausted : int;
  mutable lookahead_changed : int;
  mutable positive_directions : int;
  mutable inference_batches : int;
  mutable inference_ordinary_batches : int;
  mutable inference_yields : int;
  mutable inference_cancelled : int;
  mutable peak_pending_inferences : int;
  mutable peak_domain_words : int;
  mutable budget_responses : int;
  mutable budget_heap_responses : int;
  mutable budget_node_responses : int;
  mutable budget_cursor_drops : int;
  mutable budget_trimmed : int;
  mutable budget_first_seconds : float;
  mutable budget_deferred : int;
  mutable budget_released : int;
  mutable budget_reinjected : int;
  mutable budget_checks : int;  (** budget checks (one after every engine step) *)
  mutable budget_digest : int;
      (** FNV-1a digest of every check's footprint reading and every response, in order *)
  mutable peak_footprint_words : int;  (** largest footprint reading of the budget *)
  mutable normal_form_chains : int;
      (** forward rewritings of a lean worker to normal form within one admission ([normal_form]) *)
  mutable normal_form_steps : int;  (** their rewrite steps (one Paramodulate step each) *)
  mutable normal_form_bounded : int;  (** chains cut at [normal_form_bound] steps *)
  mutable rewrite_reentries : int;
      (** one-step forward rewrites whose result is rewritten again at its own admission: the
          rewrite intermediates that run the admission pipeline (production; 0 in a lean worker
          unless a chain was cut) *)
  mutable given_requeued : int;
      (** given clauses simplified at selection whose replacement entered Passive *)
  mutable given_at_once : int;
      (** given clauses simplified at selection whose replacement was processed at once *)
  mutable processed : int;  (** given clauses that reached inference *)
  mutable orphans : int;
      (** [Heuristic.loop.orphans]: Passive orphans dropped at selection (E's ClauseIsOrphaned) *)
  mutable sim_paramodulants : int;
      (** [Heuristic.loop.sim_paramod]: paramodulants that replaced more than one occurrence *)
  mutable sim_steps : int;  (** their proof-only intermediate Paramodulate steps *)
  mutable sim_merged : int;
      (** paramodulants not made: E makes one per from position, into clause and into subterm *)
  mutable sim_fallbacks : int;
      (** paramodulants left plain: a merged literal would need two different replacements *)
  mutable top_skipped : int;
      (** [Heuristic.loop.top_once]: paramodulants of a partner into the top of the given's positive
          literal not made (E made them with the given as the from clause) *)
  mutable eqn_subsumed : int;
      (** [Heuristic.loop.eqn_subsume]: selected clauses deleted by E's equational unit subsumption
          below the top of a literal *)
  mutable eqn_backward : int;  (** active clauses a selected unit deleted that way *)
  mutable checks : int;
      (** cooperative checks ([check_time] calls); with allocation, the work clock of slices *)
}

type ticket = Directions.ticket

type inference_group = Directions.group = {
  parents : ticket list;
  start : unit -> Calculus.inference Seq.t;
}

type pending_inference = Directions.work = {
  owner : ticket;
  mutable groups : inference_group Seq.t;
  mutable current : (ticket list * Calculus.inference Seq.t) option;
}

(* Terms by physical identity: emission hash-conses every stored clause's terms ([Term]), so
   equal subterms of stored clauses are one value within a collection epoch. *)
module Physical = Hashtbl.Make (struct
  type t = Wire.term

  let equal = ( == )
  let hash = Hashtbl.hash
end)

(* A continuation mutates its cursors. Only physical work identity and the
   immutable owner ticket may be used for its request binding. *)
module Work_table = Hashtbl.Make (struct
  type t = pending_inference

  let equal a b = a == b
  let hash work = Hashtbl.hash work.owner
end)

type t = {
  config : config;
  proof : Proof.t;
  avatar : Avatar.t;
  control : Control.t;
  work : Directions.Schedule.t;
  focus : Focus.t;
  goals : Goal.t;
  transfer : Goal_transfer.t;
  transfer_work : Goal_transfer.request_id Work_table.t;
  transfer_owners : int Tbl.Int.t;
      (** the number of [transfer_work] entries per owner id, so that [forget_work_owner] sweeps the
          table only when the id has one *)
  transfer_observations : Transfer_policy.observations;
  producers : Producer_schedule.t;
  schedule_trace : Producer_schedule.Trace.t;
  mutable emission_observer : Transfer_policy.observer option;
  ground : Ground.statistics;
  ground_boolean : Ground_boolean.t;
  mutable knowledge_epoch : int;
  mutable ground_epoch : int;
  mutable ground_given : int;
  ground_units : (step * literal) Tbl.Int.t;
  ground_literals : int list Tbl.Literal.t;
  mutable ground_clashes : int;
      (** pairs of complementary literals that both have an entry in [ground_literals] *)
  mutable ground_reflexive : int;  (** [ground_units] entries s <> s *)
  mutable ground_equations : int;  (** [ground_units] entries s = t *)
  component_atoms : (bool * int) list Tbl.Atom.t;
  terms : Term.arena;
  order : Ordering.order;
  calculus : Calculus.t;
  directions : Directions.t;
  passive : Passive.t;
  index : Index.t;
  retained_index : Index.t;
  subsumption_index : Subsumption_index.t;
  retained_subsumption : Subsumption_index.t;
  equality_index : Equality_index.t;
  demodulator : Demodulation.t;
  contraction : Contraction.t;
  pending : pending_inference Queue.t;
  mutable pending_resumptions : int;
  mutable axioms : axiom list;
  mutable root : int option;
  mutable stopped : string option;
  mutable budget_settled : int;
  mutable budget_escalate : bool;
  releasable : (int, unit) Hashtbl.t;
  released : int Queue.t;
  mutable budget_sweep : (first:bool -> unit) option;
  mutable heap_reading : unit -> int;
      (** The budget's reading; [footprint] (set by [create]) unless a test replaces it. *)
  node_words : int Tbl.Int.t;  (** [Footprint.step] of every stored proof node *)
  mutable stored_words : int;  (** their sum *)
  mutable census : int;
      (** Footprint of the suspended Goal and transfer cursors, counted at every collection point *)
  metrics : metrics;
  timing : Telemetry.t;
  started : float;
  deadline : Deadline.t;
  allocated_start : float;
  mutable finished : float option;
  cancelled : unit -> bool;
  on_active : step -> unit;
  on_clause : (string -> int list -> step -> unit) option;
  on_conflict : guard:(unit -> unit) -> step list -> unit;
  on_collect : (int -> bool) -> unit;
  on_demand : guard:(unit -> unit) -> clause -> unit;
  mutable busy : bool;
  mutable sweep_interval : int;
  mutable sweep_wait : int;
  mutable sweep_stored : int;
  mutable sweep_footprint : int;
  mutable collected_removals : int;
      (** [retained_index.removals] at the previous collection point (see [collect_notes]) *)
  initial_ids : (int, unit) Hashtbl.t;
      (** Input clauses and their forward simplifications (E's CPInitial). *)
  processed_ids : (int, unit) Hashtbl.t;
      (** Backward simplifications of active clauses (E's CPIsProcessed). *)
  sos_ids : (int, unit) Hashtbl.t;
      (** E's set of support (CPIsSOS, use_tptp_sos false): input clauses without a positive literal
          and every step with a set-of-support parent. *)
  mutable inherit_initial : bool;
  mutable mark_processed : bool;
  levels : (int, int) Hashtbl.t;
      (** SInE level of each clause ({!Evaluation.facts.level}), only for a lean strategy whose
          queues read levels and an input with negated-conjecture axioms ([sine]). *)
  mutable sine : Sine_levels.t option;
  mutable conjecture : (Ordering.head * int -> bool) option;
  mutable order_violations : int;
  mutable unfolded : Unfold.source list;
      (** The definitions that equational-definition unfolding removed from the search set, in
          removal order ([add_initial_axioms]); they also rewrite every later axiom's clauses. *)
  mutable unfold_summary : string option;
      (** What the unfolding did, when the strategy enables it ([unfold_report]). *)
  unfolded_inputs : (int, unit) Hashtbl.t;
      (** The unfolded input clauses of non-releasable axioms: like their input clauses, the memory
          budget never discards them ([trimmable]). At most one entry per input clause; proof IDs
          are never reused, so entries of collected clauses stay harmless. *)
  mutable unfolded_next : bool;
  mutable capture : capture;
      (** The first clause [retain] admits while [select_given] simplifies its given clause. *)
  mutable rewrite_emit : bool;  (** the next [emit] is a forward rewrite result *)
  mutable probe : Avatar.probe;
      (** the AVATAR keys of the clause [emit] last tested for duplicates, for its [remember] and
          its admission's duplicate test (Avatar.probe; a test of another clause ignores it) *)
  mutable rewrite_result : int;  (** the id of the last forward rewrite result *)
  mutable normal_form_rule : rule option;
      (** The rule of the last normal form [normal_form] returned: its chain ended because no
          demodulator applied. *)
  normal_terms : unit Physical.t;
      (** Subterms of stored clauses a lean worker's normal-form search found irreducible under the
          demodulators of generation [normal_generation] (rules removed since keep them
          irreducible); emptied when a rule is added and at every memory sweep. *)
  normal_terms_full : unit Physical.t;
      (** [normal_terms] for E's FullRewrite level ([Heuristic.loop.full_rewrite]), whose rule set
          also holds the directions of unorientable equations *)
  mutable normal_generation : int;
  mutable normal_form_result : int;
      (** The clause [emit] stored for that rule: its admission need not search for a rewrite again
          (no demodulator was added in between). *)
  joinability : Joinability.stats;  (** EQ-UNIT test counters ([eq_report]) *)
  equations : Demodulation.t option;
      (** EQ-UNIT for a lean worker without ordered rewriting: the active unit equations as
          ordered-rewriting rules (both directions of an unorientable one), read only by the
          redundancy tests; the worker's own demodulation keeps its oriented rules. *)
  mutable peak : term option;
      (** The next [emit] is a superposition conclusion between two positive unit equations, or the
          normal form of one: its peak, in the variables of the clause passed to [emit]. *)
  mutable admit_peak : term option;
      (** The same peak for the next [admit], in the stored clause's variables. *)
  mutable least_weight : int;  (** the weight of the problem's lightest constant *)
  mutable eq_reported : bool;
  mutable full_target : int;
      (** [Heuristic.loop.full_rewrite]: the clause whose rewriting uses E's FullRewrite level (the
          given clause, the replacement it gets at selection, or an active clause that a new unit
          rewrote); every other clause uses the strategy's forward_demod. *)
  mutable full_next : bool;  (** the next [emit] is such a clause *)
  mutable presat_running : bool;
      (** [Heuristic.loop.presat]: the presaturation pass (no generating inferences) is running *)
  mutable presat_active : int list;  (** the clauses it activated, most recent first *)
  mutable evaluations : int;  (** [Heuristic.loop.presat]: E's evaluation counter *)
  mutable e_batch : (clause * rule) list option;
      (** [Heuristic.loop.gen_order]: the conclusions of the given clause's generating inferences so
          far (most recent first), emitted in E's creation order when its inferences end. *)
  mutable activations : int Tbl.Int.t option;
      (** [Heuristic.loop.backward]: each active clause's activation number, E's processed-set
          order. *)
  mutable e_codes : (Ordering.head * int -> int) option;
      (** E's symbol codes of the input ({!E_initial.codes}), for [gen_order]'s FP7 keys. *)
  mutable inserting_initial : bool;
      (** [add_initial_axioms] runs: E's ProofStateInit, the only place where prefer_initial_clauses
          raises a clause's priorities (a member with [Heuristic.loop.replacing]) *)
  mutable relevance : Evaluation.relevance option;
      (** E's relevance levels of the input symbols, for a queue mix that reads them *)
  origins : int list Tbl.Int.t;
      (** [Heuristic.loop.discount]: the premises of the generating inference behind each retained
          clause that can still become an orphan. The replacement of a clause simplified at
          admission or selection inherits them (E simplifies such a clause in place, and
          ClauseIsOrphaned follows the simplification parents). With [Heuristic.loop.orphans] the
          replacement of a backward-simplified active clause has none ([backward_demodulate]), and
          neither has a Passive clause that stands for a dropped duplicate ([absorb_duplicate]).
          Only the orphan deletion reads it, but every DISCOUNT worker keeps it: without it the
          others would allocate less, and the work clock of a schema probe lane counts the words a
          worker allocates. *)
  dead : unit Tbl.Int.t;
      (** [Heuristic.loop.discount]: active clauses that backward simplification retired (E's
          CPIsDead) *)
  mutable origin_next : int list option;  (** the origin the next [emit] inherits *)
  vampire_ages : (int, int) Hashtbl.t;
      (** A Vampire slice member's clause ages (Kernel/Inference.cpp): 0 for an input clause, one
          more than the oldest premise for a generating inference, the simplified premise's age for
          a simplification. *)
  vampire_goals : (int, unit) Hashtbl.t;
      (** Clauses derived from a negated conjecture (Vampire's input type, inherited from every
          premise): they weigh less in clause selection ([nongoal_weight]) and win ties. *)
  vampire_inputs : (int, unit) Hashtbl.t;
      (** Input clauses and their equality resolutions with deletion (Vampire's preprocessing). *)
  vampire_parents : (int, int) Hashtbl.t;  (** AVATAR component id -> the clause it split. *)
  mutable vampire_simplified : int option;
      (** The next [emit] simplifies this clause (it keeps its age), instead of generating. *)
  urr_units : (Clause.feature, int list) Hashtbl.t;
      (** Unit resulting resolution: active unit clauses by the key of their literal. *)
  urr_nonunits : (Clause.feature, int list) Hashtbl.t;
      (** Active non-unit clauses by the key of each of their literals. *)
  flr_partial : (clause, int) Hashtbl.t;
      (** Forward literal rewriting: retained two-literal clauses (by their normal form) whose
          complementary variant has not been retained yet. *)
  flr_rules : (Clause.feature, flr_rule list) Hashtbl.t;
      (** The literal rewrite rules by the (positive) key of their left literal. *)
  mutable lrs_limits : Vampire.limits option;
      (** A Vampire LRS slice's current selection limits (no limits before the first estimate). *)
  mutable lrs_counter : int;  (** LRS::shouldUpdateLimits' call counter. *)
  mutable lrs_first : int option;  (** The work clock at the first activation. *)
  mutable lrs_discarded : int;  (** New clauses dropped for exceeding every limit. *)
  mutable vampire_input : bool option;
      (** The next [emit] is a preprocessed input clause (age 0) of a negated-conjecture axiom or
          not, possibly unfolded by function definitions. *)
  vampire_numbers : (int, int) Hashtbl.t;
      (** Vampire's clause numbers where they differ from the id, as negative tie-break numbers:
          Vampire numbers the input clauses in file order (and its preprocessed versions after them)
          but processes them in reverse order (SaturationAlgorithm::init pushes them on the
          new-clause stack), so the input clauses are admitted last to first here. *)
  vampire_positions : (int, int) Hashtbl.t;  (** Input clause id -> its input position. *)
  mutable vampire_position : int option;  (** The input position of the next [emit]. *)
  mutable vampire_total : int;  (** The number of input clauses. *)
  mutable vampire_batch : vampire_new list option;
      (** A Vampire slice member's new clauses of the current activation, newest first, not yet
          processed (SaturationAlgorithm's _newClauses); [None] outside an activation. *)
  mutable vampire_direct : bool;  (** The next [emit] processes a batched clause. *)
  mutable vampire_count : int;  (** Vampire's clause numbers of the derived clauses so far. *)
  mutable vampire_number : int option;  (** The number of the batched clause [emit] processes. *)
  vampire_tries : (Clause.feature, vampire_trie) Hashtbl.t;
      (** A Vampire slice member's resolution index as its substitution tree orders it: per literal
          key, a trie over the argument symbols in insertion order. *)
  vampire_paths : (int * int, vampire_symbol array * int) Hashtbl.t;
      (** (active clause, literal) -> its symbols in [vampire_tries] and its insertion count. *)
  mutable vampire_inserted : int;
}

and capture = Off | Armed | Captured of int

(* A new clause of a Vampire activation, as [emit] received it, with the facts [emit] reads from
   the engine state and the number Vampire gives it when it is created. *)
(* A node of [vampire_tries]: its children by symbol (a function symbol and arity, or a variable
   by first occurrence), with their insertion ranks, kept in insertion order up to three children
   (SubstitutionTree's UArrIntermediateNode) and sorted from the fourth on (SListIntermediateNode:
   variables first, then function symbols by Vampire's number). *)
and vampire_trie = {
  children : (vampire_symbol, int * vampire_trie) Hashtbl.t;
  mutable sorted : bool;
  mutable in_order : vampire_symbol array option;  (** The sorted children, until the next one. *)
}

and vampire_symbol = Vsym of Wire.symbol * int | Vvar of int

and vampire_new = {
  vn_clause : clause;
  vn_rule : rule;
  vn_simplified : int option;
  vn_peak : term option;
  vn_rewritten : bool;
  vn_number : int;
}

(* A literal rewrite rule (RewriteRuleIndex): the positive literal [lhs] at [position] of the
   two-literal clause [clause], whose complementary variant is [counterpart]: an instance of
   [lhs] is equivalent to the complement of the instance of the clause's other literal. *)
and flr_rule = { lhs : literal; position : int; clause : int; counterpart : int }

exception Stop

(* The internal selection trace of lean workers ([given_trace]): set once by the CLI (an
   evaluation switch, AXIOM_MEASURE_GIVEN_TRACE), never by a search. *)
let given_trace : (string -> unit) option ref = ref None

(* The evaluation trace of lean workers (AXIOM_MEASURE_EVAL_TRACE): one line per clause that enters
   Passive with its evaluation order and its evaluation in every queue, so that a first divergence
   from E's given sequence can be told apart into an evaluation, a tie-break or a missing clause.
   Set once by the CLI or a measurement harness, never by a search. *)
let eval_trace : (string -> unit) option ref = ref None

(* With [given_trace] set, also one line per clause that enters Passive (an evaluation switch,
   AXIOM_MEASURE_NEW_TRACE): its rule and parents, to compare derivations with another prover's
   (Vampire's --show_new). *)
let new_trace = ref false

type guide = { retained : step -> unit; pick : t -> int option }
(** An evaluation diagnostic of lean workers, never set by a search: [retained] sees every clause
    that enters Passive and [pick] may name the next given clause (a live Passive clause) instead of
    the queue mix, so that a port can be made to follow another prover's given sequence (E's -l1)
    and the first given clause it cannot follow can be found. [None] leaves the pick to the queues.
*)

let selection_guide : guide option ref = ref None

(* The memory budget's reading (see [budget] and Footprint): stored proof nodes, maintained on
   every store and reclaim, the cursors counted at the last collection point, and the Goal index
   postings. Every term is a count the search maintains, so the reading is the same for the same
   search whatever the collector, the machine, the load or the other workers do. *)
let footprint t =
  Footprint.estimate ~stored:t.stored_words ~goal_cursors:0 ~request_cursors:0
    ~goal_postings:t.goals.index.size
  + t.census

(* The default reading, a sentinel for [footprint] (a field cannot refer to its own record):
   [reading] reads the footprint while [heap_reading] is this function. *)
let own_footprint () = -1
let reading t = if t.heap_reading == own_footprint then footprint t else t.heap_reading ()

(* The cursors' part of the footprint, counted at a collection point. *)
let count_cursors t =
  let goal =
    Tbl.Int.fold
      (fun _ (s : Goal.state) n -> if s.cursor <> None then n + 1 else n)
      t.goals.states 0
  and request =
    Tbl.Int.fold
      (fun _ (q : Goal_transfer.request) n -> if q.cursor <> None then n + 1 else n)
      t.transfer.requests 0
  in
  t.census <-
    Footprint.estimate ~stored:0 ~goal_cursors:goal ~request_cursors:request ~goal_postings:0

(* Every proof node is stored through here, so [stored_words] stays exact. *)
let store t clause rule =
  let step = Proof.add t.proof clause rule in
  let words = Footprint.step step in
  Tbl.Int.replace t.node_words step.id words;
  t.stored_words <- t.stored_words + words;
  step

(* After [Proof.reclaim]: forget the words of the reclaimed nodes. *)
let forget_reclaimed t =
  Tbl.Int.filter_map_inplace
    (fun id words ->
      match Proof.get t.proof id with
      | _ -> Some words
      | exception Not_found ->
          t.stored_words <- t.stored_words - words;
          None)
    t.node_words

(* The clock of the scheduling costs: the wall time a step takes is charged to its lane, its
   Control arm and its preferred-resumption rank. A measurement switch (the CLI's
   AXIOM_MEASURE_COST_CLOCK=stopped) stops it, so that a bounded search is a function of its input
   alone and runs can be compared step by step; it never changes the time limit. *)
let cost_clock = ref Telemetry.now
let cost_now () = !cost_clock ()

(* [Heuristic.loop.full_rewrite]: the worker's demodulator also holds the directions of its
   unorientable unit equations, which only a FullRewrite ([full_target]) uses. *)
let full_rewrite_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.full_rewrite | None -> false

(* [Heuristic.loop.discount]: E's DISCOUNT loop. *)
let discount_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.discount | None -> false

(* [Heuristic.loop.discount] with [duplicates]: variants wait for their selection. *)
let duplicates_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.discount && h.loop.duplicates | None -> false

(* [Heuristic.loop.discount] with [orphans]: E's orphan deletion at selection. *)
let orphans_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.discount && h.loop.orphans | None -> false

(* [Heuristic.loop.presat]: presaturation interreduction, with E's evaluation order. *)
let presat_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.presat | None -> false

(* [Heuristic.loop.presat_duplicates]: presaturation keeps E's variants. *)
let presat_duplicates_strategy (s : Strategy.t) =
  match s.heuristic with
  | Some h -> h.loop.discount && h.loop.presat && h.loop.presat_duplicates
  | None -> false

(* [Heuristic.loop.cp_initial]: E's CPInitial semantics. *)
let cp_initial_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.cp_initial | None -> false

(* [Heuristic.loop.discount] with [replacing]: E's timing of destructive equality resolution
   (ProofStateInit, replacing_inferences) and of prefer_initial_clauses. *)
let gen_order_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.e_calculus && h.loop.gen_order | None -> false

(* [Heuristic.loop.discount] with [eqn_subsume]: E's equational unit subsumption. *)
let eqn_subsume_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.discount && h.loop.eqn_subsume | None -> false

(* [Heuristic.loop.top_once]: E's single top-level overlap of positive literals, over [gen_order]'s
   batch. *)
let top_once_strategy (s : Strategy.t) =
  match s.heuristic with
  | Some h -> h.loop.e_calculus && h.loop.gen_order && h.loop.top_once
  | None -> false

(* [Heuristic.loop.sim_paramod]: E's simultaneous paramodulation, over [gen_order]'s batch. *)
let sim_paramod_strategy (s : Strategy.t) =
  match s.heuristic with
  | Some h -> h.loop.e_calculus && h.loop.gen_order && h.loop.sim_paramod
  | None -> false

let backward_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.discount && h.loop.backward | None -> false

let replacing_strategy (s : Strategy.t) =
  match s.heuristic with Some h -> h.loop.discount && h.loop.replacing | None -> false

let create ?(phase = 0) ?(cancelled = fun () -> false) ?(on_active = fun _ -> ()) ?on_clause
    ?on_inference ?(on_conflict = fun ~guard:_ _ -> ()) ?(on_collect = fun _ -> ())
    ?(on_demand = fun ~guard:_ _ -> ()) config =
  if config.backward_demodulation && not config.demodulation then
    invalid_arg "backward demodulation requires demodulation";
  if config.lookahead < 0 || config.lookahead > 1000000 then
    invalid_arg "lookahead budget must be between 0 and 1000000";
  if config.lookahead > 0 && ((not config.ordered) || not config.selection) then
    invalid_arg "lookahead requires ordered inference and negative selection";
  if
    config.collect_every < 0 || config.limits.max_given < 0 || config.limits.max_generated < 0
    || config.limits.max_retained < 0
    || (not (Float.is_finite config.limits.seconds))
    || config.limits.seconds < 0.
  then invalid_arg "search limits must be finite and nonnegative";
  if config.budget.heap_words < 0 || config.budget.proof_nodes < 0 then
    invalid_arg "memory budgets must be nonnegative";
  (* A ported E heuristic fixes its own literal selection (the index lookahead would
     revise it) and, like E's strategies, does not split clauses. *)
  let config =
    match config.strategy.heuristic with
    | Some h ->
        {
          config with
          lookahead = 0;
          avatar = h.avatar;
          given_at_once = config.given_at_once || h.loop.at_once;
        }
    | None -> config
  in
  let started_ns = Telemetry.now_ns () and allocated_start = Telemetry.allocated_words () in
  let started = Float.of_int started_ns *. 1e-9 in
  let terms = Term.create () and order = Ordering.create () in
  let strategy = config.strategy in
  let calculus =
    Calculus.create ~variable_positions:config.variable_positions ~ordered:config.ordered
      ~selection:config.selection ~strategy ~order terms
  in
  let directions = Directions.create ~strategy ~order ~memo:calculus.memo () in
  calculus.observe <-
    Some
      (fun stage rule ->
        Directions.observe directions stage rule;
        Option.iter (fun f -> f stage rule) on_inference);
  directions.probe.observe <-
    Some
      (fun stage rule ->
        Directions.observe directions stage rule;
        Option.iter (fun f -> f ("probe/" ^ stage) rule) on_inference);
  {
    config;
    proof = Proof.create ();
    avatar = Avatar.create ();
    control = Control.create ();
    work = Directions.Schedule.create ();
    focus = Focus.create ();
    goals =
      Goal.create ?on_clause
        ?on_inference:(Option.map (fun f stage rule -> f ("goal/" ^ stage) rule) on_inference)
        ();
    transfer = Goal_transfer.create ~calculus ();
    transfer_work = Work_table.create 32;
    transfer_owners = Tbl.Int.create 32;
    transfer_observations = Transfer_policy.create ();
    producers = Producer_schedule.create ();
    schedule_trace = Producer_schedule.Trace.create ();
    emission_observer = None;
    ground = Ground.statistics ();
    ground_boolean =
      Ground_boolean.create
      (* Vampire has no ground Boolean reasoning outside AVATAR: a slice member runs without it. *)
        ~enabled:(match strategy.heuristic with Some { vampire = Some _; _ } -> false | _ -> true)
        ~capacity:
          (if config.budget.proof_nodes > 0 then
             min config.limits.max_retained config.budget.proof_nodes
           else config.limits.max_retained)
        ();
    knowledge_epoch = 0;
    ground_epoch = 0;
    ground_given = 0;
    ground_units = Tbl.Int.create 64;
    ground_literals = Tbl.Literal.create 64;
    ground_clashes = 0;
    ground_reflexive = 0;
    ground_equations = 0;
    component_atoms = Tbl.Atom.create 64;
    terms;
    order;
    calculus;
    directions;
    passive =
      Passive.create ~phase ~policy:config.clause_weight
        ~plain:(strategy.queues = Strategy.Plain_queues)
        ?balance:
          (match strategy.heuristic with
          | Some { vampire = Some v; _ } -> Some (v.age_ratio, v.weight_ratio)
          | _ -> None)
        ?split:
          (match strategy.heuristic with
          | Some { vampire = Some v; _ } when v.positive_split ->
              Some
                [
                  {
                    Passive.split_feature = 0;
                    ratios = v.plsqr;
                    cutoffs = v.plsqc;
                    layered = v.plsql;
                  };
                ]
          | _ -> None)
        ?mix:
          (Option.map
             (fun (h : Heuristic.t) -> List.map (fun (q : Evaluation.queue) -> q.count) h.queues)
             strategy.heuristic)
        ~ratio:config.weight_ratio ();
    index = Index.create ~fingerprint:config.fingerprint ();
    retained_index = Index.create ~fingerprint:config.fingerprint ();
    subsumption_index = Subsumption_index.create ();
    retained_subsumption = Subsumption_index.create ~resolution:false ();
    equality_index = Equality_index.create ~fingerprint:config.fingerprint ();
    demodulator =
      Demodulation.create ~order
        ~ordered_rewriting:(strategy.ordered_rewriting || full_rewrite_strategy strategy)
        ~instances:
          (config.eq_instances && strategy.heuristic <> None && strategy.ordered_rewriting
         && not config.avatar)
        ();
    contraction =
      Contraction.create ~order
        ~equivalence:
          (match strategy.heuristic with
          | Some { vampire = Some _; _ } -> Contraction.Legacy
          | _ -> config.equivalence)
        ();
    pending = Queue.create ();
    pending_resumptions = 0;
    axioms = [];
    root = None;
    stopped = None;
    budget_settled = 0;
    budget_escalate = false;
    releasable = Hashtbl.create 64;
    released = Queue.create ();
    budget_sweep = None;
    heap_reading = own_footprint;
    node_words = Tbl.Int.create 256;
    stored_words = 0;
    census = 0;
    metrics =
      {
        generated = 0;
        retained = 0;
        given = 0;
        redundant = 0;
        tautologies = 0;
        duplicates = 0;
        subsumed = 0;
        subsumption_trials = 0;
        subsumption_exhausted = 0;
        subsumption_resolved = 0;
        resolution_trials = 0;
        backward_subsumed = 0;
        given_subsumed = 0;
        peak_live_words = 0;
        allocated_words = 0.;
        variants = 0;
        memory_samples = 0;
        demodulated = 0;
        backward_demodulated = 0;
        backward_unit_cut = 0;
        backward_demodulation_candidates = 0;
        backward_demodulation_baseline = 0;
        collections = 0;
        reclaimed_nodes = 0;
        reclaimed_terms = 0;
        lookahead_postings = 0;
        lookahead_exhausted = 0;
        lookahead_changed = 0;
        positive_directions = 0;
        inference_batches = 0;
        inference_ordinary_batches = 0;
        inference_yields = 0;
        inference_cancelled = 0;
        peak_pending_inferences = 0;
        peak_domain_words = 0;
        budget_responses = 0;
        budget_heap_responses = 0;
        budget_node_responses = 0;
        budget_cursor_drops = 0;
        budget_trimmed = 0;
        budget_first_seconds = -1.;
        budget_deferred = 0;
        budget_released = 0;
        budget_reinjected = 0;
        budget_checks = 0;
        budget_digest = 0;
        peak_footprint_words = 0;
        normal_form_chains = 0;
        normal_form_steps = 0;
        normal_form_bounded = 0;
        rewrite_reentries = 0;
        given_requeued = 0;
        given_at_once = 0;
        processed = 0;
        orphans = 0;
        sim_paramodulants = 0;
        sim_steps = 0;
        sim_merged = 0;
        sim_fallbacks = 0;
        top_skipped = 0;
        eqn_subsumed = 0;
        eqn_backward = 0;
        checks = 0;
      };
    timing = Telemetry.create ();
    started;
    deadline = Deadline.create ~now:started_ns config.limits.seconds;
    allocated_start;
    finished = None;
    cancelled;
    on_active;
    on_clause;
    on_conflict;
    on_collect;
    on_demand;
    busy = false;
    sweep_interval = 1;
    sweep_wait = 0;
    sweep_stored = 0;
    sweep_footprint = 0;
    collected_removals = 0;
    initial_ids = Hashtbl.create 64;
    processed_ids = Hashtbl.create 64;
    sos_ids = Hashtbl.create 64;
    inherit_initial = false;
    mark_processed = false;
    levels = Hashtbl.create 64;
    sine = None;
    conjecture = None;
    order_violations = 0;
    unfolded = [];
    unfold_summary = None;
    unfolded_inputs = Hashtbl.create 16;
    unfolded_next = false;
    capture = Off;
    rewrite_emit = false;
    probe = Avatar.probe [];
    rewrite_result = -1;
    normal_form_rule = None;
    normal_terms = Physical.create 1024;
    normal_terms_full = Physical.create 1024;
    normal_generation = 0;
    normal_form_result = -1;
    joinability = Joinability.stats ();
    equations =
      (if
         strategy.heuristic <> None && (not strategy.ordered_rewriting) && (not config.avatar)
         && (config.eq_ground_joinable || config.eq_connected)
       then Some (Demodulation.create ~order ~ordered_rewriting:true ())
       else None);
    peak = None;
    admit_peak = None;
    least_weight = 1;
    eq_reported = false;
    full_target = -1;
    full_next = false;
    presat_running = false;
    presat_active = [];
    evaluations = 0;
    e_batch = None;
    activations = None;
    e_codes = None;
    inserting_initial = false;
    relevance = None;
    origins = Tbl.Int.create 256;
    dead = Tbl.Int.create 64;
    origin_next = None;
    vampire_ages = Hashtbl.create 64;
    vampire_goals = Hashtbl.create 64;
    vampire_inputs = Hashtbl.create 64;
    vampire_parents = Hashtbl.create 16;
    vampire_simplified = None;
    vampire_input = None;
    vampire_numbers = Hashtbl.create 64;
    vampire_positions = Hashtbl.create 64;
    vampire_position = None;
    vampire_total = 0;
    vampire_batch = None;
    vampire_direct = false;
    vampire_count = 0;
    vampire_number = None;
    vampire_tries = Hashtbl.create 16;
    vampire_paths = Hashtbl.create 64;
    vampire_inserted = 0;
    urr_units = Hashtbl.create 16;
    urr_nonunits = Hashtbl.create 16;
    flr_partial = Hashtbl.create 16;
    flr_rules = Hashtbl.create 16;
    lrs_limits = None;
    lrs_counter = 0;
    lrs_first = None;
    lrs_discarded = 0;
  }

(* Lean mode: only the given-clause loop, as in E. *)
let lean t = t.config.strategy.heuristic <> None

(* A Vampire slice member (Heuristic.of_vampire). *)
let vampire t =
  match t.config.strategy.heuristic with Some { vampire = Some v; _ } -> Some v | _ -> None

(* EQ-UNIT applies to a lean worker without AVATAR (no ported heuristic splits), so that a
   deletion never meets a clause's AVATAR dependencies. The tests read the worker's demodulator
   when it does ordered rewriting, and otherwise a second index of the same active equations with
   both directions of the unorientable ones ([equations]). *)
let unit_equality t =
  lean t && (not t.config.avatar) && (t.config.strategy.ordered_rewriting || t.equations <> None)

let test_rules t = match t.equations with Some e -> e | None -> t.demodulator

(* Diagnostics hook (AXIOM_LEAN_EQ_REPORT): one line of EQ-UNIT counters per engine that ran a
   test, when it is sealed. *)
let eq_report : (string -> unit) ref = ref (fun _ -> ())

let report_eq t =
  let j = t.joinability in
  if (not t.eq_reported) && j.ground_tests + j.connected_tests + t.demodulator.instance_rewrites > 0
  then (
    t.eq_reported <- true;
    !eq_report
      (Printf.sprintf
         "eq-unit: strategy=%s given=%d ground_tests=%d ground_joined=%d ground_cases=%d \
          connected_tests=%d connected=%d exhausted=%d instance_rewrites=%d trials=%d \
          comparisons=%d ground_seconds=%.3f connected_seconds=%.3f active_seconds=%.3f"
         t.config.strategy.name t.metrics.given j.ground_tests j.ground_joined j.ground_cases
         j.connected_tests j.connected j.exhausted t.demodulator.instance_rewrites j.trials
         j.comparisons
         (Telemetry.seconds t.timing "joinability")
         (Telemetry.seconds t.timing "connectedness")
         ((match t.finished with Some at -> at | None -> Telemetry.now ()) -. t.started)))

(* A clause's SInE level: its axiom's level for an input clause, otherwise the least level of its
   parents (a clause with no recorded parent is unreached). *)
let note_level t (step : step) rule =
  match t.sine with
  | None -> ()
  | Some sine ->
      let level =
        match rule with
        | Input (axiom, _) -> Sine_levels.level sine axiom
        | _ ->
            List.fold_left
              (fun m p ->
                min m (Option.value ~default:Sine_levels.unreached (Hashtbl.find_opt t.levels p)))
              Sine_levels.unreached (Wire.parents rule)
      in
      Hashtbl.replace t.levels step.id level

(* E's set of support (ClauseSetMarkSOS with use_tptp_sos false, ccl_clausesets.c:1162) is the
   input clauses without a positive literal. E passes the flag to every conclusion with a
   set-of-support premise (cco_paramodulation.c:163, cco_factoring.c:88, cco_eqnresolving.c:91)
   and to every clause that a set-of-support clause rewrites or cuts (ccl_rewrite.c:1400,
   ccl_subsumption.c:1306, ccl_context_sr.c:85). A simplification step here has both the
   simplified and the simplifying clause as parents, so every case reads "some parent is in the
   set of support". *)
let note_sos t (step : step) rule =
  if lean t then (
    let sos =
      match rule with
      | Input _ -> (
          match t.config.strategy.heuristic with
          (* E's use_tptp_sos marks the clauses of TPTP role conjecture, which E has negated
             (negated_conjecture) before any clause exists: the set of support is empty. *)
          | Some { tptp_sos = true; _ } -> false
          | _ -> not (List.exists (fun l -> l.positive) step.clause))
      | _ -> List.exists (fun p -> Hashtbl.mem t.sos_ids p) (Wire.parents rule)
    in
    if sos then Hashtbl.replace t.sos_ids step.id ();
    note_level t step rule)

(* A Vampire slice member's clause facts: the age and the goal flag (Kernel/Inference.cpp) and
   whether the clause is an input clause for the preprocessing ([vampire_inputs]). [simplified]
   is the premise a simplification replaces. *)
let note_vampire t (step : step) rule ?input ?position ?number simplified =
  let n = t.vampire_total in
  (* A derived clause's number: the one Vampire gave it when it was created ([vampire_batch]), or
     the next one. Input clauses have negative numbers, below every derived one. *)
  let derived () =
    let k =
      match number with
      | Some k -> k
      | None ->
          t.vampire_count <- t.vampire_count + 1;
          t.vampire_count
    in
    Hashtbl.replace t.vampire_numbers step.id k
  in
  (match (position, rule, simplified) with
  | Some p, Input _, _ ->
      Hashtbl.replace t.vampire_positions step.id p;
      Hashtbl.replace t.vampire_numbers step.id (p - (2 * n))
  | Some p, _, _ ->
      (* An input clause unfolded by function definitions: a preprocessed clause. *)
      Hashtbl.replace t.vampire_positions step.id p;
      Hashtbl.replace t.vampire_numbers step.id (p - n)
  | None, Equality_resolve _, Some premise -> (
      match Hashtbl.find_opt t.vampire_positions premise with
      | Some p ->
          Hashtbl.replace t.vampire_positions step.id p;
          Hashtbl.replace t.vampire_numbers step.id (p - n)
      | None -> derived ())
  | None, Input _, _ -> ()
  | None, _, _ -> derived ());
  let age id = Option.value ~default:0 (Hashtbl.find_opt t.vampire_ages id) in
  let goal_axiom axiom_id =
    match List.find_opt (fun (a : axiom) -> a.axiom_id = axiom_id) t.axioms with
    | Some a -> List.mem a.name t.config.goal_names
    | None -> false
  in
  let parents =
    match rule with
    | Component id -> Option.to_list (Hashtbl.find_opt t.vampire_parents id)
    | _ -> Wire.parents rule
  in
  let goal =
    match (input, rule) with
    | Some goal, _ -> goal
    | None, Input (axiom_id, _) -> goal_axiom axiom_id
    | None, _ -> List.exists (fun p -> Hashtbl.mem t.vampire_goals p) parents
  in
  if goal then Hashtbl.replace t.vampire_goals step.id ();
  let value =
    match (rule, simplified) with
    | _ when input <> None -> 0
    | Input _, _ -> 0
    | Component _, _ -> List.fold_left (fun m p -> max m (age p)) 0 parents
    | _, Some premise -> age premise
    | _, None -> 1 + List.fold_left (fun m p -> max m (age p)) 0 parents
  in
  Hashtbl.replace t.vampire_ages step.id value;
  match (rule, simplified) with
  | _ when input <> None -> Hashtbl.replace t.vampire_inputs step.id ()
  | Input _, _ -> Hashtbl.replace t.vampire_inputs step.id ()
  | Equality_resolve _, Some premise when Hashtbl.mem t.vampire_inputs premise ->
      Hashtbl.replace t.vampire_inputs step.id ()
  | _ -> ()

(* E clause facts are only read for retained clauses and the premises of later steps, which
   are all live: drop the facts of collected clauses. *)
let prune_facts t ~keep =
  if lean t then
    List.iter
      (fun table ->
        Hashtbl.filter_map_inplace (fun id () -> if keep id then Some () else None) table)
      [ t.initial_ids; t.processed_ids; t.sos_ids; t.vampire_goals; t.vampire_inputs ];
  if vampire t <> None then (
    Hashtbl.filter_map_inplace (fun id a -> if keep id then Some a else None) t.vampire_ages;
    Hashtbl.filter_map_inplace (fun id a -> if keep id then Some a else None) t.vampire_numbers;
    Hashtbl.filter_map_inplace (fun (id, _) a -> if keep id then Some a else None) t.vampire_paths);
  if t.sine <> None then
    Hashtbl.filter_map_inplace (fun id l -> if keep id then Some l else None) t.levels

let elapsed t = (match t.finished with Some at -> at | None -> Telemetry.now ()) -. t.started

let sample_memory t =
  t.metrics.memory_samples <- t.metrics.memory_samples + 1;
  let gc = Gc.quick_stat () in
  t.metrics.peak_live_words <- max t.metrics.peak_live_words gc.heap_words;
  t.metrics.allocated_words <- max 0. (Telemetry.allocated_words () -. t.allocated_start)

(* Diagnostics hook (AXIOM_EQUIVALENCE_REPORT): one line of Contraction's literal rewriting
   counters per engine that searched, when it is sealed. [justified] counts the rewrites whose
   retirement is a redundancy deletion (all of them under the default rule), [units] those of a
   unit target. *)
let equivalence_report : (string -> unit) ref = ref (fun _ -> ())

let report_equivalence t =
  let c = t.contraction in
  if c.trials > 0 || t.metrics.generated > 0 then
    !equivalence_report
      (Printf.sprintf
         "equivalence: strategy=%s rule=%s given=%d generated=%d rewritten=%d justified=%d \
          units=%d derived=%d unit_deleted=%d trials=%d exhausted=%d skipped=%d"
         t.config.strategy.name
         (Contraction.equivalence_name c.equivalence)
         t.metrics.given t.metrics.generated c.literal_rewritten c.literal_justified c.literal_units
         c.literal_derived c.unit_deleted c.trials c.exhausted c.skipped)

let seal t =
  if t.root <> None || t.stopped <> None then Queue.clear t.pending;
  (* A rebuild of the ground Boolean context deferred by its last collection, so that it reads as
     every report expects (Ground_boolean.collect_logged). *)
  Ground_boolean.materialize t.ground_boolean;
  if t.finished = None then (
    sample_memory t;
    t.finished <- Some (Telemetry.now ());
    report_equivalence t;
    (* Diagnostics (AXIOM_VAMPIRE_ORDERING): a Vampire slice member's LRS state. *)
    if vampire t <> None then
      !Vampire.report
        (Printf.sprintf "vampire-lrs: strategy=%s given=%d lrs_discarded=%d limits=%s"
           t.config.strategy.name t.metrics.given t.lrs_discarded
           (match t.lrs_limits with
           | None -> "none"
           | Some l ->
               Printf.sprintf "age<=%d(w<=%d),weight<=%d" l.max_age l.max_age_weight l.max_weight)));
  report_eq t

let stop t message =
  t.stopped <- Some message;
  raise Stop

let check_time t =
  t.metrics.checks <- t.metrics.checks + 1;
  if Option.is_some t.root || Option.is_some t.stopped then raise Stop;
  if t.cancelled () then stop t "cancelled";
  (* Without a retained-node limit (max_int, the default) neither test below can fire: no store
     reaches max_int nodes, and Ground_boolean's space would have to exceed max_int minus it. *)
  if t.config.limits.max_retained <> max_int then (
    let required = Proof.stored t.proof + Boolean.proof_size t.avatar.solver in
    if required >= t.config.limits.max_retained then stop t "retained proof node limit";
    Ground_boolean.enforce_space t.ground_boolean
      ~available:(t.config.limits.max_retained - required));
  (* Amortized: reads the clock on every few calls only (Deadline). A zero
     budget is expired from the start, so the first check still stops. *)
  if Deadline.expired t.deadline then stop t "time limit"

(* The work clock of single-worker slices: the words the calling domain has
   allocated plus [check_words] per cooperative check of [t]. Allocated words track wall time
   across producers and inference lanes; checks track array-based CDCL and congruence work, which
   allocates little. Only differences are used, over stretches in which [t] alone runs on the
   domain, so they measure [t]'s work there. Allocation counts are per domain and exact (they do
   not depend on when the collector runs), so for the same input and binary the readings repeat;
   they never depend on the machine or its load. About [work_units_per_second] units take one
   second on a quiet performance core (the calibration of the former wall-clock costs). *)
let check_words = 20
let work_units_per_second = 3e8
let work_clock ~checks = int_of_float (Telemetry.allocated_words ()) + (check_words * checks)
let work_reading t = work_clock ~checks:t.metrics.checks

(* Precise variant for coarse boundaries (the start of every engine step): the
   amortized check can fire up to 15 guard calls late, and right after a dense
   phase those calls may be sparse. One clock read per step bounds how far that
   lateness can carry. The other limits are checked first, as in [check_time],
   so a found refutation is never reported as a time limit. *)
let check_time_now t =
  check_time t;
  if Deadline.expired_now t.deadline then stop t "time limit"

let subsumes t c d =
  check_time t;
  t.metrics.subsumption_trials <- t.metrics.subsumption_trials + 1;
  Subsumption.subsumes
    ~guard:(fun () -> check_time t)
    ~on_exhausted:(fun () -> t.metrics.subsumption_exhausted <- t.metrics.subsumption_exhausted + 1)
    c d

let forward_subsuming ?(except = -1) t clause =
  let candidates =
    if t.config.subsumption_indexed then Subsumption_index.forward t.subsumption_index clause
    else
      let count = Tbl.Int.length t.index.live in
      t.subsumption_index.baseline <- t.subsumption_index.baseline + count;
      t.subsumption_index.candidates <- t.subsumption_index.candidates + count;
      Index.all t.index
  in
  List.find_opt
    (fun (s : step) ->
      s.id <> except
      && (except < 0 || Avatar.can_reduce t.avatar ~target:except ~using:s.id)
      && subsumes t s.clause clause)
    candidates

(* E's eqn_subsumes_termpair below the top: [s] and [u] have the same head and exactly one
   differing argument; that pair, or one further down the same way, is an instance of a unit
   equation's sides. [at x y] finds a unit for the pair [(x, y)]. Two identical sides are a
   tautology, which emission has dropped. *)
let rec below_top at s u =
  match (s, u) with
  | Fn (f, xs), Fn (g, ys) when Sym.equal f g && List.compare_lengths xs ys = 0 -> (
      let rec differing found xs ys =
        match (xs, ys) with
        | [], [] -> found
        | x :: xs, y :: ys ->
            if Clause.compare_term x y = 0 then differing found xs ys
            else if found = None then differing (Some (x, y)) xs ys
            else None
        | _ -> None
      in
      match differing None xs ys with
      | None -> None
      | Some (x, y) -> ( match at x y with Some _ as found -> found | None -> below_top at x y))
  | _ -> None

(* [Heuristic.loop.eqn_subsume], forward (E's ForwardSubsumption by processed_pos_eqns): an active
   unorientable positive unit equation (a direction of one in the demodulator) whose sides match a
   pair below the top of a positive literal of [clause]. *)
let eqn_subsuming ?(except = -1) t clause =
  let at x y =
    match x with
    | V _ -> None
    | Fn (f, args) ->
        let rules = Demodulation.unoriented t.demodulator (f, List.length args) in
        let found = ref None and k = ref 0 in
        while !found = None && !k < Array.length rules do
          let (rule : Demodulation.rewrite) = rules.(!k) in
          incr k;
          if
            rule.extra = [] && rule.parent <> except
            && (except < 0 || Avatar.can_reduce t.avatar ~target:except ~using:rule.parent)
          then
            match Subsumption.term ~guard:(fun () -> check_time t) [] rule.lhs x with
            | exception Subsumption.No_match -> ()
            | sigma ->
                if Clause.compare_term (E_simparamod.apply sigma rule.rhs) y = 0 then
                  found := Some rule.parent
        done;
        !found
  in
  let rec literals = function
    | [] -> None
    | { positive = true; atom = E (s, u) } :: rest -> (
        match below_top at s u with Some _ as found -> found | None -> literals rest)
    | _ :: rest -> literals rest
  in
  match literals clause with
  | None -> None
  | Some id ->
      t.metrics.eqn_subsumed <- t.metrics.eqn_subsumed + 1;
      Some (Proof.get t.proof id)

(* Forward subsumption, with E's equational unit subsumption for [Heuristic.loop.eqn_subsume]. *)
let forward_subsumer ?(except = -1) t clause =
  match forward_subsuming ~except t clause with
  | Some _ as found -> found
  | None -> if eqn_subsume_strategy t.config.strategy then eqn_subsuming ~except t clause else None

let observe t stage (step : step) =
  Option.iter (fun f -> f stage (Avatar.dependency t.avatar step.id) step) t.on_clause

let count_work_owner t id d =
  let n = d + Option.value ~default:0 (Tbl.Int.find_opt t.transfer_owners id) in
  if n <= 0 then Tbl.Int.remove t.transfer_owners id else Tbl.Int.replace t.transfer_owners id n

(* Without an entry of [id] the sweep would keep every entry in place, so it is skipped. *)
let forget_work_owner t id =
  if Tbl.Int.mem t.transfer_owners id then (
    Tbl.Int.remove t.transfer_owners id;
    Work_table.filter_map_inplace
      (fun work request -> if fst work.owner = id then None else Some request)
      t.transfer_work)

let complementary (l : literal) = { l with positive = not l.positive }

(* [ground_reflexive] and [ground_equations] for a [ground_units] entry added (1) or removed (-1). *)
let count_ground_unit t (l : literal) d =
  match l.atom with
  | E _ when l.positive -> t.ground_equations <- t.ground_equations + d
  | E (a, b) when a = b -> t.ground_reflexive <- t.ground_reflexive + d
  | _ -> ()

let deactivate t id =
  Option.iter
    (fun (e : Avatar.entry) ->
      let stage =
        if e.role = Avatar.Retired then "retired"
        else if e.lock <> None then "locked"
        else "inactive"
      in
      observe t stage e.step)
    (Tbl.Int.find_opt t.avatar.entries id);
  Directions.remove t.directions id;
  Focus.remove t.focus id;
  Ground_boolean.forget t.ground_boolean id;
  Goal.remove t.goals id;
  Goal_transfer.remove t.transfer id;
  forget_work_owner t id;
  Option.iter
    (fun (_, literal) ->
      Tbl.Int.remove t.ground_units id;
      count_ground_unit t literal (-1);
      let remaining = List.filter (( <> ) id) (Tbl.Literal.find t.ground_literals literal) in
      if remaining = [] then (
        Tbl.Literal.remove t.ground_literals literal;
        if Tbl.Literal.mem t.ground_literals (complementary literal) then
          t.ground_clashes <- t.ground_clashes - 1)
      else Tbl.Literal.replace t.ground_literals literal remaining;
      t.knowledge_epoch <- t.knowledge_epoch + 1)
    (Tbl.Int.find_opt t.ground_units id);
  Passive.invalidate t.passive id;
  Calculus.forget t.calculus id;
  Index.remove t.index id;
  Index.remove t.retained_index id;
  Equality_index.remove t.equality_index id;
  Demodulation.remove t.demodulator id;
  Option.iter (fun e -> Demodulation.remove e id) t.equations;
  Contraction.remove t.contraction id;
  Subsumption_index.remove t.subsumption_index id;
  Subsumption_index.remove t.retained_subsumption id

let retire t id =
  Avatar.retire t.avatar id;
  deactivate t id

(* A Vampire slice member keeps no Focus entries: its only operation is inference (its queue mix
   ignores preferences), so Focus would be bookkeeping without effect. *)
let reward ?(closed = false) t ids gain =
  match t.config.strategy.heuristic with
  | Some { vampire = Some _; _ } -> ()
  | _ ->
      Focus.reward ~closed t.focus ~get:(Proof.get t.proof) ~promote:(Passive.prefer t.passive) ids
        gain

let focus_register t id =
  match t.config.strategy.heuristic with
  | Some { vampire = Some _; _ } -> ()
  | _ -> Focus.register t.focus id

let reduce_using t ~target ~using =
  if Avatar.reduce_using t.avatar ~target ~using then (
    observe t "reduced" (Proof.get t.proof target);
    deactivate t target;
    reward t using 4;
    true)
  else false

let reduce t ~target ~using = reduce_using t ~target ~using:[ using ]
let current_ticket t (id, generation) = Index.current t.retained_index id generation

let pressure t (step : step) =
  Focus.pressure t.focus
    ~guard:(fun () -> check_time t)
    ~alive:(current_ticket t)
    ~eligible:
      (Calculus.eligible t.calculus
         (Calculus.selected t.calculus step)
         (Clause.scope 1 step.clause))
    step.clause

let compact_pending t =
  Shared.filter_queue
    (fun work ->
      if current_ticket t work.owner then true
      else (
        t.metrics.inference_cancelled <- t.metrics.inference_cancelled + 1;
        false))
    t.pending;
  Work_table.filter_map_inplace
    (fun work request ->
      if current_ticket t work.owner then Some request
      else (
        count_work_owner t (fst work.owner) (-1);
        None))
    t.transfer_work

let trace_action t action (id, generation) =
  Producer_schedule.Trace.action t.schedule_trace action ~id ~generation
    ~control_turn:t.control.turns ~lane_turn:t.work.turns
    ~producer_turn:(Producer_schedule.turns t.producers)
    ~pending:(Queue.length t.pending)

let trace_collection t edge origin =
  Producer_schedule.Trace.gc t.schedule_trace edge ~origin ~control_turn:t.control.turns
    ~producer_turn:(Producer_schedule.turns t.producers)
    ~stored:(Proof.stored t.proof)
    ~retained:(Tbl.Int.length t.retained_index.live)
    ~pending:(Queue.length t.pending)

(* Scheduling-state collectors and index compaction. Goal, transfer, focus and
   direction queues drop dead tickets here, and budgeted scans (contraction
   ticks, cursor quanta, Index.sample) count stale postings until compaction,
   so these steps are visible to the search: they always run on the fixed
   collection cadence. They must also run before any proof reclaim. *)
let collect_notes t =
  (* Every executable premise is retained and thus already a proof root. Stale
     tickets are checked without reading their possibly reclaimed proof nodes. *)
  compact_pending t;
  (* Tickets ([current_ticket]) and [Index.mem] read only the retained index. While no retained
     clause was removed or superseded since the previous collection point, everything the
     collectors kept then is still alive and they need to check only what was added since. *)
  let quiet = t.retained_index.removals = t.collected_removals in
  t.collected_removals <- t.retained_index.removals;
  Focus.collect ~quiet t.focus ~keep:(Index.mem t.retained_index) ~alive:(current_ticket t);
  Goal.collect ~quiet t.goals ~alive:(current_ticket t);
  Goal_transfer.collect ~quiet t.transfer ~alive:(current_ticket t);
  Ground_boolean.collect_logged t.ground_boolean ~keep:(Index.mem t.retained_index);
  Index.compact t.index;
  Index.compact t.retained_index;
  Equality_index.compact t.equality_index;
  Demodulation.compact t.demodulator;
  Option.iter Demodulation.compact t.equations;
  Contraction.compact t.contraction;
  Directions.compact t.directions ~alive:(current_ticket t);
  count_cursors t

let check_collectable t =
  if t.busy || t.ground_boolean.running || Unify.mark t.calculus.unifier <> 0 then
    invalid_arg "Engine.collect: inference in progress"

(* A full collection: the scheduling collectors, then the memory sweep (proof
   reclaim, AVATAR tables, passive heap rebuild, selection memos and E clause
   facts, term arena). *)
let collect ?(origin = Producer_schedule.Trace.Manual) t =
  trace_collection t Producer_schedule.Trace.Begin origin;
  Telemetry.with_stage t.timing "collection" (fun () ->
      check_collectable t;
      collect_notes t;
      (* Every live id of these tables is a root; they are pushed without building their list,
         and the reclaimed set does not depend on the order (Proof.reclaim_with). *)
      let roots push =
        Ground_boolean.iter_roots t.ground_boolean push;
        Avatar.iter_roots t.avatar push;
        Tbl.Int.iter (fun id _ -> push id) t.retained_index.live;
        Tbl.Int.iter (fun id _ -> push id) t.index.live;
        Tbl.Int.iter (fun id _ -> push id) t.passive.live;
        if not t.avatar.unsat then Option.iter push t.root;
        (* A Vampire activation's waiting new clauses keep their premises (unit resulting
           resolution's intermediate clauses among them). *)
        match t.vampire_batch with
        | None -> ()
        | Some pending ->
            List.iter
              (fun n ->
                Option.iter push n.vn_simplified;
                List.iter push (Wire.parents n.vn_rule))
              pending
      in
      let dropped = ref [] in
      let reclaimed =
        Proof.reclaim_with ~dropped:(fun id -> dropped := id :: !dropped) t.proof roots
      in
      if reclaimed > 0 then forget_reclaimed t;
      (* AVATAR keeps the entries of stored nodes (Avatar.collect with the store as [keep]): only
         those of the nodes just dropped go. *)
      Avatar.collect_dropped t.avatar !dropped;
      (* Production heaps are rebuilt; an E queue mix only once its stale entries dominate. *)
      Passive.compact t.passive;
      Tbl.Int.filter_map_inplace
        (fun id selected ->
          if Index.mem t.index id || Index.mem t.retained_index id then Some selected else None)
        t.calculus.selected;
      Calculus.prune t.calculus ~keep:(fun id ->
          Index.mem t.index id || Index.mem t.retained_index id);
      prune_facts t ~keep:(fun id -> Index.mem t.index id || Index.mem t.retained_index id);
      if discount_strategy t.config.strategy then (
        (* The origins of retained clauses, and the dead premises they still name. *)
        Tbl.Int.filter_map_inplace
          (fun id origin -> if Index.mem t.retained_index id then Some origin else None)
          t.origins;
        let named = Tbl.Int.create (Tbl.Int.length t.dead) in
        Tbl.Int.iter
          (fun _ origin ->
            List.iter (fun p -> if Tbl.Int.mem t.dead p then Tbl.Int.replace named p ()) origin)
          t.origins;
        Tbl.Int.filter_map_inplace
          (fun id () -> if Tbl.Int.mem named id then Some () else None)
          t.dead);
      Physical.reset t.normal_terms;
      Physical.reset t.normal_terms_full;
      t.metrics.collections <- t.metrics.collections + 1;
      t.metrics.reclaimed_nodes <- t.metrics.reclaimed_nodes + reclaimed;
      t.metrics.reclaimed_terms <- t.metrics.reclaimed_terms + Term.count t.terms;
      Term.clear t.terms;
      t.on_collect (Index.mem t.index);
      sample_memory t);
  trace_collection t Producer_schedule.Trace.End origin

(* Only the scheduling collectors (no memory sweep). *)
let collect_notes_only ~origin t =
  trace_collection t Producer_schedule.Trace.Begin origin;
  Telemetry.with_stage t.timing "collection" (fun () ->
      check_collectable t;
      collect_notes t;
      t.on_collect (Index.mem t.index));
  trace_collection t Producer_schedule.Trace.End origin

(* Footprint growth since an engine's last sweep that forces its next sweep:
   an eighth of the footprint, at least 2^22 words (32 MiB). *)
let footprint_slack words = max (1 lsl 22) (words / 8)

(* The memory sweep reclaims proof nodes, AVATAR entries, stale passive-heap
   entries, selection memos (lookahead selections and a strategy's default
   selections), E clause facts and the term arena. Every live clause is a root,
   stale postings are skipped, and the passive heaps order by (priority, id),
   so the clause sets the search works on are the same whenever it runs. It is
   not fully unobservable, though: Focus.reward walks proof parents until the
   first reclaimed node, the retained-node limit and Ground_boolean's space
   budget count Proof.stored including unreclaimed nodes, and a stale selection
   memo survives until the next sweep. Its cost is linear in the live state, so
   a fixed period makes its total cost quadratic in the run length. With
   [collect_adaptive], every collection point runs the scheduling collectors;
   the sweep runs only when its interval (in collection points, 1..64)
   expires. The interval doubles while a sweep reclaims less than 1/16 of the
   stored proof nodes and halves when it reclaims more than 1/4. Memory guards
   force a sweep once the term arena holds 2^20 nodes, the proof store has
   grown past twice its size after the previous sweep plus 65536 nodes, or the
   engine's [footprint] has grown by [footprint_slack] since its previous
   sweep. All of these are counts of the engine's own state, never readings of
   the collector, so a worker sweeps at the same points whatever the garbage
   collector, the load or the other workers do. While a heap response of the
   memory budget is unrelieved ([memory_pressure], below), every collection
   point sweeps, as every collection point did before the adaptive interval. *)
(* One adaptive memory sweep: a full collection, after which the interval and
   the memory guards of [periodic_collect] restart from this sweep. Every sweep
   of an adaptive worker goes through here: the periodic ones and the one that
   ends a heap response of the memory budget ([budget_sweep]). *)
let sweep ~origin t =
  let before = Proof.stored t.proof in
  collect ~origin t;
  let after = Proof.stored t.proof in
  let reclaimed = before - after in
  t.sweep_wait <- 0;
  t.sweep_stored <- after;
  t.sweep_footprint <- footprint t;
  if 16 * reclaimed < before then t.sweep_interval <- min (2 * t.sweep_interval) 64
  else if 4 * reclaimed > before then t.sweep_interval <- max 1 (t.sweep_interval / 2)

let periodic_collect t origin =
  if not t.config.collect_adaptive then collect ~origin t
  else (
    t.sweep_wait <- t.sweep_wait + 1;
    if
      t.sweep_wait >= t.sweep_interval
      || Term.count t.terms >= 1 lsl 20
      || Proof.stored t.proof >= (2 * t.sweep_stored) + 65536
      || footprint t >= t.sweep_footprint + footprint_slack t.sweep_footprint
      || t.budget_escalate
    then sweep ~origin t
    else collect_notes_only ~origin t)

let budget_nodes t =
  Proof.stored t.proof
  + Boolean.proof_size t.avatar.solver
  + Ground_boolean.proof_size t.ground_boolean

(* Passive clauses the budget may discard: derived ones, and the input clauses
   of axioms registered as releasable (schema instances whose injector takes
   them back, see [released]). Fixed axioms and the negated conjecture are never
   discarded: nothing would ever add them again. *)
let trimmable t =
  Tbl.Int.fold
    (fun id (size, _) victims ->
      match Proof.get t.proof id with
      | { rule = Input (axiom, _); _ } when not (Hashtbl.mem t.releasable axiom) -> victims
      | _ when Hashtbl.mem t.unfolded_inputs id -> victims
      | _ -> (size, id) :: victims
      | exception Not_found -> victims)
    t.passive.live []

(* Passive input clauses of releasable axioms, by axiom. *)
let releasable_inputs t =
  let by_axiom = Hashtbl.create 64 in
  Tbl.Int.iter
    (fun id _ ->
      match Proof.get t.proof id with
      | { rule = Input (axiom, _); _ } when Hashtbl.mem t.releasable axiom ->
          Hashtbl.replace by_axiom axiom
            (id :: Option.value ~default:[] (Hashtbl.find_opt by_axiom axiom))
      | _ -> ()
      | exception Not_found -> ())
    t.passive.live;
  by_axiom

(* Withdraw a releasable axiom: retire every input clause of it that is still
   Passive ([inputs], from [releasable_inputs]) and queue its id on [released],
   once. The injector drains [released] and adds the axiom again later under a
   fresh id, so the withdrawal delays the instance and never loses it. Input
   clauses of it that were already selected stay active; their copies are
   duplicates when the axiom returns. Returns the number of clauses retired. *)
let withdraw t inputs axiom =
  Hashtbl.remove t.releasable axiom;
  Queue.add axiom t.released;
  t.metrics.budget_released <- t.metrics.budget_released + 1;
  let ids = List.filter (Tbl.Int.mem t.passive.live) (Hashtbl.find inputs axiom) in
  List.iter (retire t) ids;
  List.length ids

(* Retire the [count] heaviest trimmable Passive clauses, the newest first
   among equal weights; the next collection reclaims them and their unshared
   ancestors. A releasable input clause withdraws its whole axiom, and all of
   its retired clauses count. Discarding derived clauses makes the ordinary
   search incomplete, never unsound. *)
let retire_heaviest ?(until = fun () -> false) t victims count =
  if count > 0 then
    let victims =
      List.sort (fun (a, i) (b, j) -> if a <> b then Int.compare b a else Int.compare j i) victims
    in
    let inputs = lazy (releasable_inputs t) in
    let rec go n = function
      | (_, id) :: rest when n > 0 && not (until ()) ->
          let retired =
            if not (Tbl.Int.mem t.passive.live id) then 0
            else
              match Proof.get t.proof id with
              | { rule = Input (axiom, _); _ } when Hashtbl.mem t.releasable axiom ->
                  withdraw t (Lazy.force inputs) axiom
              | _ | (exception Not_found) ->
                  retire t id;
                  1
          in
          t.metrics.budget_trimmed <- t.metrics.budget_trimmed + retired;
          go (n - retired) rest
      | _ -> ()
    in
    go count victims

let trim_passive t count = retire_heaviest t (trimmable t) count

(* A response is judged again only after this many more collection points
   (under pressure each of them sweeps), so that the search it leaves behind
   has run for a while. Until then the response is not repeated or escalated.
   Collection points come at fixed counts of inference batches and producer
   runs, so this is a deterministic wait. *)
let settle_collections = 2

(* A settled reading at this multiple of the budget, while an earlier
   response has not brought the footprint back under it, stops the worker. It
   is the guard against running out of memory when what grows is state the
   budget cannot discard; it needs no empty Passive. *)
let ceiling = 2

(* A response's pressure ends only at a settled reading below this share of
   the budget (3/4). The reading is exact at once, so without the margin the
   first reading after a trim would end the pressure: the withdrawn instances
   would return at once and be withdrawn again at the next response. *)
let relief_words budget = budget.heap_words / 4 * 3

(* The last-resort safety limit: the worker's own major heap as the collector
   reports it (Telemetry.budget_words: this Domain, and in a forked worker only
   what it added since the fork) at this multiple of the footprint budget stops
   the worker ("memory safety limit"). Unlike the budget it depends on the
   environment (OCAMLRUNPARAM, the collector's progress), so it is set far
   above what the budget lets a search reach: [safety] times the budget, and
   never below [safety_floor] (1 GiB), so that a small budget cannot trip it
   on the heap every run starts with. Measured under the default collector
   settings, a worker's major heap holds about two to eight words per
   footprint word. It only catches state the footprint does not count. *)
let safety = 16
let safety_floor = Footprint.of_mib 1024
let safety_words budget = max safety_floor (safety * budget.heap_words)

let note_response t =
  if t.metrics.budget_responses = 0 then t.metrics.budget_first_seconds <- elapsed t;
  t.metrics.budget_responses <- t.metrics.budget_responses + 1

(* The collection that ends a heap response. By default it is the adaptive
   memory sweep ([sweep]: the scheduling collectors plus the memory sweep, with
   the adaptive interval and guards restarting from it); the worker's first heap
   response ([first]) also resets the sweep interval to every collection point,
   and while the pressure lasts [periodic_collect] sweeps at every point anyway.
   A response never goes through [periodic_collect], which may skip the sweep.
   [set_budget_sweep] installs a replacement (a test seam). *)
let budget_sweep t ~first =
  match t.budget_sweep with
  | Some f -> f ~first
  | None ->
      sweep ~origin:Producer_schedule.Trace.Manual t;
      if first then t.sweep_interval <- 1

let set_budget_sweep t f = t.budget_sweep <- Some f

(* The memory budget responds between steps, outside [protect], so a response
   must not raise [Stop]. Its stages (collection, trimming, the sweep) are
   linear in the search state, and on the large Passive sets of a lean E worker
   one response took longer than the supervisor's stop grace. A response
   therefore checks a stop request and the deadline before each stage and
   while it trims; at either it records the stop, as [check_time] would at the
   next step, and returns. Before the deadline nothing changes. *)
let response_stopped t =
  t.stopped <> None
  ||
  let reason =
    if t.cancelled () then Some "cancelled"
    else if Deadline.expired_now t.deadline then Some "time limit"
    else None
  in
  match reason with
  | None -> false
  | Some _ ->
      t.stopped <- reason;
      seal t;
      true

(* Soft memory budgets, enforced after every engine step (a deterministic
   point) and read from the engine's own counts ([footprint]), so the same
   search reads and answers them identically under any collector setting,
   load, portfolio isolation or worker count. Over the node budget the worker
   collects and then trims trimmable Passive clauses to three quarters of the
   budget; it stops if it is still over. Over the footprint budget it drops
   every suspended Goal and transfer cursor (each scan continues from its
   marks) and runs [budget_sweep]. If the footprint is still over budget once
   that response has settled ([settle_collections]), the next response also
   trims a quarter of the trimmable Passive clauses (derived ones and
   releasable instances, which return later), and a settled reading at
   [ceiling] times the budget stops the worker. The pressure ends at a settled
   reading below [relief_words]. Every reading and response
   enters [budget_digest]. The collector's reading is only reported
   ([peak_domain_words]) and guards the [safety] limit. A response stops at a
   stop request or the deadline ([response_stopped]) before each stage and
   between retires. *)
let enforce_budget ?words t =
  if t.root = None && t.stopped = None && not t.busy then (
    let budget = t.config.budget and m = t.metrics in
    let words = match words with Some w -> w | None -> reading t in
    m.budget_checks <- m.budget_checks + 1;
    m.budget_digest <- Footprint.mix m.budget_digest words;
    if words > m.peak_footprint_words then m.peak_footprint_words <- words;
    (* The collector's view, reported only, and the safety limit. *)
    let heap = Telemetry.budget_words () in
    if heap > m.peak_domain_words then m.peak_domain_words <- heap;
    if budget.heap_words > 0 && heap >= safety_words budget then (
      m.budget_digest <- Footprint.mix m.budget_digest 5;
      t.stopped <- Some "memory safety limit";
      seal t);
    let until () = response_stopped t in
    if
      t.stopped = None && budget.proof_nodes > 0
      && budget_nodes t >= budget.proof_nodes
      && not (until ())
    then (
      m.budget_digest <- Footprint.mix m.budget_digest 1;
      note_response t;
      t.metrics.budget_node_responses <- t.metrics.budget_node_responses + 1;
      if Ground_boolean.proof_size t.ground_boolean > 0 then Ground_boolean.release t.ground_boolean;
      collect t;
      let target = budget.proof_nodes / 4 * 3 in
      let excess = budget_nodes t - target in
      let victims = if until () then [] else trimmable t in
      if excess > 0 && victims <> [] then (
        retire_heaviest ~until t victims (min excess (List.length victims));
        if not (until ()) then collect t);
      if t.stopped = None && budget_nodes t >= budget.proof_nodes then (
        t.stopped <- Some "proof node budget exhausted";
        seal t));
    if t.stopped = None && budget.heap_words > 0 && m.collections >= t.budget_settled then
      if words < relief_words budget then t.budget_escalate <- false
      else if words < budget.heap_words then ()
      else if t.budget_escalate && words / ceiling >= budget.heap_words then (
        m.budget_digest <- Footprint.mix m.budget_digest 4;
        t.stopped <- Some "memory budget exhausted";
        seal t)
      else if not (until ()) then (
        let first = m.budget_heap_responses = 0 in
        m.budget_digest <- Footprint.mix m.budget_digest (if t.budget_escalate then 3 else 2);
        note_response t;
        m.budget_heap_responses <- m.budget_heap_responses + 1;
        m.budget_cursor_drops <-
          m.budget_cursor_drops + Goal.drop_cursors t.goals + Goal_transfer.drop_cursors t.transfer;
        (if t.budget_escalate then
           let victims = trimmable t in
           retire_heaviest ~until t victims (max 1 (List.length victims / 4)));
        if not (until ()) then (
          budget_sweep t ~first;
          t.budget_escalate <- true;
          t.budget_settled <- m.collections + settle_collections)))

(* A heap response is in effect and no settled reading has shown relief. *)
let memory_pressure t = t.budget_escalate

(* Schema instances the budget withdrew wait while this holds: under pressure,
   and until the reading is back at half the budget, so that a returning
   instance has room and is not withdrawn again at the next response. *)
let holds_instances t =
  t.budget_escalate || (t.config.budget.heap_words > 0 && reading t > t.config.budget.heap_words / 2)

(* [Heuristic.loop.eqn_subsume], backward (E's eliminate_backward_subsumed_clauses with a unit
   subsumer): a selected unorientable positive unit equation deletes the active clauses with a
   positive literal it subsumes below the top. An oriented one has rewritten them already. The
   candidates are the feature-vector survivors without the literal prints, which apply at the top
   only. *)
let eqn_backward t (step : step) =
  match step.clause with
  | [ { positive = true; atom = E (l, r) } ]
    when not (Ordering.greater ~order:t.order l r || Ordering.greater ~order:t.order r l) ->
      let l = Clause.map_vars (fun (_, i) -> V (1, i)) l
      and r = Clause.map_vars (fun (_, i) -> V (1, i)) r in
      let matches p q x y =
        match Subsumption.term ~guard:(fun () -> check_time t) [] p x with
        | exception Subsumption.No_match -> false
        | sigma -> (
            match Subsumption.term ~guard:(fun () -> check_time t) sigma q y with
            | exception Subsumption.No_match -> false
            | _ -> true)
      in
      let at x y = if matches l r x y || matches r l x y then Some step.id else None in
      let candidates =
        if t.config.subsumption_indexed then
          Subsumption_index.backward_vector t.subsumption_index step.clause
        else Index.all t.index
      in
      List.iter
        (fun (s : step) ->
          if
            s.id <> step.id && Index.mem t.index s.id
            && Avatar.can_reduce t.avatar ~target:s.id ~using:step.id
            && List.exists
                 (function
                   | { positive = true; atom = E (x, y) } -> below_top at x y <> None | _ -> false)
                 s.clause
            && reduce t ~target:s.id ~using:step.id
          then (
            t.metrics.eqn_backward <- t.metrics.eqn_backward + 1;
            Tbl.Int.replace t.dead s.id ()))
        candidates
  | _ -> ()

let backward_simplify t (step : step) =
  let clause = step.clause in
  if t.config.subsumption && t.config.backward_subsumption then
    Telemetry.with_stage t.timing "subsumption" (fun () ->
        let candidates =
          if discount_strategy t.config.strategy then
            (* E backward-subsumes the processed clauses only. *)
            if t.config.subsumption_indexed then
              Subsumption_index.backward t.subsumption_index clause
            else Index.all t.index
          else if t.config.subsumption_indexed then
            Subsumption_index.backward t.retained_subsumption clause
          else
            let count = Tbl.Int.length t.retained_index.live in
            t.retained_subsumption.baseline <- t.retained_subsumption.baseline + count;
            t.retained_subsumption.candidates <- t.retained_subsumption.candidates + count;
            Index.all t.retained_index
        in
        List.iter
          (fun (s : step) ->
            let active = Index.mem t.index s.id in
            if
              s.id <> step.id
              && Avatar.can_reduce t.avatar ~target:s.id ~using:step.id
              && subsumes t clause s.clause
              && reduce t ~target:s.id ~using:step.id
            then (
              t.metrics.backward_subsumed <- t.metrics.backward_subsumed + 1;
              if active && discount_strategy t.config.strategy then Tbl.Int.replace t.dead s.id ()))
          candidates;
        if eqn_subsume_strategy t.config.strategy then eqn_backward t step)

(* E's destructive equality resolution (er_varlit_destructive, er_strong_destructive):
   C \/ x != s with x not in s is equivalent to C[x := s]. The replacement is an
   ordinary Equality_resolve step whose substitution binds x; the original clause
   is retired like any forward-simplified clause. *)
(* E's ClauseRemoveSuperfluousLiterals (EqnListRemoveResolved) in every ForwardModifyClause: a
   negative literal whose two sides are the same term is false and goes, an equality resolution
   with the empty substitution ([Heuristic.loop.resolved], at admission and selection); otherwise
   such a literal is resolved only by a generating equality resolution. *)
let resolved_literal t (step : step) =
  if not (match t.config.strategy.heuristic with Some h -> h.loop.resolved | None -> false) then
    None
  else
    let rec find i = function
      | [] -> None
      | { positive = false; atom = E (a, b) } :: _ when a = b -> Some i
      | _ :: rest -> find (i + 1) rest
    in
    Option.map
      (fun i ->
        {
          Contraction.clause = Clause.remove i (Clause.scope 1 step.clause);
          rule = Equality_resolve (step.id, i, []);
          using = [];
        })
      (find 0 step.clause)

let destructive_er t (step : step) =
  match resolved_literal t step with
  | Some _ as result -> result
  | None -> (
      let mode =
        match t.config.strategy.heuristic with
        | None -> Heuristic.Er_off
        | Some { vampire = Some _; _ } ->
            (* Vampire's equality resolution with deletion (Shell/EqResWithDeletion.cpp) is
               preprocessing: input clauses only, until none applies. *)
            if Hashtbl.mem t.vampire_inputs step.id then Heuristic.Er_strong else Heuristic.Er_off
        | Some { destructive_er; _ } -> destructive_er
      in
      match mode with
      | Heuristic.Er_off -> None
      | destructive_er ->
          let xs = Clause.scope 1 step.clause in
          let candidate l =
            if l.positive then None
            else
              let binding x s =
                match (destructive_er, s) with
                | Heuristic.Er_varlit, V y when y <> x -> Some (x, s)
                | Heuristic.Er_strong, _
                  when not (List.mem x (Wire.variables [ { positive = true; atom = E (s, s) } ])) ->
                    Some (x, s)
                | _ -> None
              in
              match l.atom with
              | E (V x, s) -> (
                  match binding x s with
                  | Some _ as b -> b
                  | None -> ( match s with V y -> binding y (V x) | _ -> None))
              | E (s, V x) -> binding x s
              | _ -> None
          in
          let rec find i = function
            | [] -> None
            | l :: rest -> (
                match candidate l with Some b -> Some (i, b) | None -> find (i + 1) rest)
          in
          Option.map
            (fun (i, (x, s)) ->
              let rec apply = function
                | V v when v = x -> s
                | V _ as v -> v
                | Fn (f, ts) -> Fn (f, List.map apply ts)
              in
              {
                Contraction.clause = List.map (Clause.map_literal apply) (Clause.remove i xs);
                rule = Equality_resolve (step.id, i, [ (x, s) ]);
                using = [];
              })
            (find 0 xs))

let record_explanation_with normalize ?support t clause rule =
  check_time t;
  (match rule with
  | Component _ -> invalid_arg "Engine.record_explanation: component assumption"
  | _ -> ());
  let derived = Avatar.dependencies t.avatar rule in
  let support = Option.value ~default:derived support in
  if support <> derived then invalid_arg "Engine.record_explanation: inconsistent support";
  if t.metrics.generated >= t.config.limits.max_generated then stop t "generated clause limit";
  let clause = normalize clause in
  check_time t;
  t.metrics.generated <- t.metrics.generated + 1;
  let step = store t clause rule in
  note_sos t step rule;
  Transfer_policy.derived t.emission_observer step;
  ignore (Avatar.remember_explanation t.avatar ~support step);
  t.metrics.retained <- t.metrics.retained + 1;
  step

let record_explanation ?support t clause rule =
  record_explanation_with Clause.normalize ?support t clause rule

let record_ground_explanation ?support t clause rule =
  let normalize clause =
    let guard () = check_time t in
    if not (Ground_boolean.ground ~guard clause) then
      invalid_arg "Engine.record_ground_explanation: nonground clause";
    let rec sorted = function
      | [] -> true
      | [ _ ] ->
          guard ();
          true
      | a :: (b :: _ as rest) ->
          guard ();
          compare a b < 0 && sorted rest
    in
    (* Ground normalization has no renaming. Reuse a sorted resolvent and its
       immutable terms; arbitrary input still receives the same set ordering. *)
    if sorted clause then clause else List.sort_uniq compare clause
  in
  record_explanation_with normalize ?support t clause rule

let record t clause rule =
  check_time t;
  if t.metrics.generated >= t.config.limits.max_generated then stop t "generated clause limit";
  t.metrics.generated <- t.metrics.generated + 1;
  let step = store t (Clause.normalize clause) rule in
  note_sos t step rule;
  Transfer_policy.derived t.emission_observer step;
  focus_register t step.id;
  let entry = Avatar.remember t.avatar ~variants:t.config.variants step in
  (* Explanation intermediates are proof ancestors, not searchable knowledge.
     They must neither suppress later admission nor become permanent GC roots. *)
  (match rule with Component _ -> () | _ -> entry.role <- Avatar.Retired);
  t.metrics.retained <- t.metrics.retained + 1;
  step

(* A lean worker's forward rewriting to normal form within one admission ([config.normal_form]),
   E's ForwardModifyClause. [rewrite_once] runs until no demodulator applies, at most
   [normal_form_bound] times; each rewrite is still one Paramodulate certificate step. A rewrite
   result that is rewritten again is recorded as a proof-only node (as explanation intermediates
   are: no variant tables, never a search candidate), so only the last result returns to
   [contract] and runs emission and admission. The steps are the ones iterated one-step admission
   takes, since [rewrite_once] picks the leftmost-outermost position and the oldest live rule, and
   recording a clause changes no demodulator; the duplicate and subsumption checks of the
   intermediate clauses are gone, and a chain stops at a tautology, which emission drops. A chain
   cut at the bound continues at the next admission. *)
let normal_form_bound = 1024

(* The id of a rewrite result before it is recorded: rewrite_once only copies it into the
   Paramodulate step it returns, which [retarget] then points at the recorded node. *)
let provisional = min_int

let retarget into = function
  | Paramodulate (p, i, reverse, _, j, path, sigma) ->
      Paramodulate (p, i, reverse, into, j, path, sigma)
  | rule -> rule

let demodulator rule = List.hd (Wire.parents rule)

(* At most this many memoized normal-form subterms ([normal_terms]). *)
let normal_terms_limit = 1 lsl 16

(* EQ-UNIT: a unit clause's [peak] in the variables [Clause.normalize] gives the clause (numbered
   in order of first occurrence, the literal first); [None] for any other clause. *)
let renamed_peak clause peak =
  match (clause, peak) with
  | [ literal ], Some peak -> (
      match Clause.rename_variables [ literal; { positive = true; atom = E (peak, peak) } ] with
      | [ _; { atom = E (peak, _); _ } ] -> Some peak
      | _ -> None)
  | _ -> None

let scoped_peak = Option.map (Clause.map_vars (fun (_, i) -> V (2, i)))

(* A lean worker with [Heuristic.loop.full_rewrite] and forward_demod 1 rewrites a new clause with
   its orientable rules only (E's RuleRewrite); the [full_target] gets every rule (FullRewrite). *)
let rules_only t (step : step) =
  full_rewrite_strategy t.config.strategy
  && (not t.config.strategy.ordered_rewriting)
  && step.id <> t.full_target

let normal_form ?peak t (step : step) =
  let guard () = check_time t in
  let rules = t.demodulator in
  let oriented_only = rules_only t step in
  (* The memo of irreducible subterms holds for the level it is filled at: with two levels
     ([Heuristic.loop.full_rewrite]) a FullRewrite has its own. *)
  let memo =
    if full_rewrite_strategy t.config.strategy && not oriented_only then t.normal_terms_full
    else t.normal_terms
  in
  if t.normal_generation <> rules.generation then (
    Physical.reset t.normal_terms;
    Physical.reset t.normal_terms_full;
    t.normal_generation <- rules.generation);
  let first =
    (* The memo holds for any target that is no rule itself; only the stored clause's own
       (hash-consed) terms are worth remembering. *)
    if Tbl.Int.mem rules.live step.id then
      Demodulation.rewrite_first ~guard ~oriented_only rules step
    else
      Demodulation.rewrite_first ~guard ~oriented_only ~skip:(Physical.mem memo)
        ~irreducible:(fun term ->
          if Physical.length memo < normal_terms_limit then Physical.replace memo term ())
        rules step
  in
  match first with
  | None -> None
  | Some (clause, rule) ->
      (* [peak] (EQ-UNIT) follows the chain: in the variables of [clause] at every step, and the
         emission of the result receives it ([t.peak]). A rewrite copies the target into scope 2. *)
      let rec go clause rule using steps peak =
        let finish ?(normal = false) () =
          t.peak <- peak;
          if normal then t.normal_form_rule <- Some rule;
          t.metrics.normal_form_chains <- t.metrics.normal_form_chains + 1;
          t.metrics.normal_form_steps <- t.metrics.normal_form_steps + steps;
          t.metrics.demodulated <- t.metrics.demodulated + steps;
          Some { Contraction.clause; rule; using = List.sort_uniq compare using }
        in
        if steps >= normal_form_bound then (
          t.metrics.normal_form_bounded <- t.metrics.normal_form_bounded + 1;
          finish ())
        else
          (* The node [record_explanation_with] stores for this result is exactly [normalized],
             the clause the next rewrite reads its literal index and variables from. *)
          let normalized = Clause.normalize clause in
          (* A tautology stays one under further rewriting: emission drops it now. *)
          if Clause.tautology_sorted normalized then finish ()
          else
            match
              Demodulation.rewrite_first ~guard ~oriented_only rules
                { id = provisional; clause = normalized; rule }
            with
            | None -> finish ~normal:true ()
            | Some (next, next_rule) ->
                let recorded = record_explanation_with Fun.id t normalized rule in
                go next (retarget recorded.id next_rule) (demodulator next_rule :: using) (steps + 1)
                  (scoped_peak (renamed_peak clause peak))
      in
      go clause rule [ demodulator rule ] 1 (scoped_peak peak)

(* Forward demodulation of an admitted or selected clause: to normal form in a lean worker with
   [normal_form], one step otherwise (production). *)
let demodulate ?peak t (step : step) =
  if
    (not t.config.demodulation)
    || match vampire t with Some v -> not v.forward_demodulation | None -> false
  then None
  else
    Telemetry.with_stage t.timing "demodulation" (fun () ->
        if lean t && t.config.normal_form then normal_form ?peak t step
        else
          Option.map
            (fun (clause, rule) ->
              t.metrics.demodulated <- t.metrics.demodulated + 1;
              { Contraction.clause; rule; using = [ demodulator rule ] })
            (Demodulation.rewrite_once
               ~guard:(fun () -> check_time t)
               ~oriented_only:(rules_only t step) t.demodulator step))

(* Whether this worker's Contraction also rewrites with the equivalences of two-literal clauses
   (see [cut]). *)
let literal_rewriting t =
  match vampire t with
  | Some v -> v.literal_rewriting
  | None -> not (discount_strategy t.config.strategy)

(* Unit deletion and literal rewriting (Contraction), then subsumption resolution. *)
let cut t (step : step) =
  if
    (not t.config.subsumption)
    || match vampire t with Some v -> not v.subsumption_resolution | None -> false
  then None
  else
    Telemetry.with_stage t.timing "subsumption" (fun () ->
        (* Literal rewriting with the equivalences of two-literal clauses (Contraction's binary
           sides) is Vampire's forward literal rewriting: a Vampire slice uses it only with flr=on
           (with [flr_rewrite]), under Vampire's condition; unit deletion is its forward
           subsumption resolution with units. E has none. [Contraction.Legacy] (the evaluation
           hook AXIOM_EQUIVALENCE=legacy) deletes units that the equivalence does not make
           redundant, which loses refutations (HEN012-1); the default rewrites only when the
           retirement is a redundancy deletion ([config.equivalence]). The DISCOUNT loop does not
           use it, as E. *)
        let binary = literal_rewriting t in
        match Contraction.find ~binary ~guard:(fun () -> check_time t) t.contraction step with
        | Some _ as result -> result
        | None -> (
            let exception Exhausted in
            let left = ref 2048 in
            let guard () =
              check_time t;
              decr left;
              if !left < 0 then raise Exhausted
            in
            try
              let candidates =
                if t.config.subsumption_indexed then
                  Subsumption_index.resolution ~guard t.subsumption_index step.clause
                else Index.all t.index
              in
              List.find_map
                (fun (side : step) ->
                  guard ();
                  if side.id = step.id then None
                  else (
                    t.metrics.resolution_trials <- t.metrics.resolution_trials + 1;
                    match Subsumption.resolve ~guard side step with
                    | None -> None
                    | Some (clause, rule) ->
                        t.metrics.subsumption_resolved <- t.metrics.subsumption_resolved + 1;
                        Some { Contraction.clause; rule; using = [ side.id ] }))
                candidates
            with Exhausted -> None))

(* A DISCOUNT admission's only contraction ([Heuristic.loop.discount]): unit simplify-reflect with
   the active units (E's ForwardModifyClause); the Contraction holds active clauses only. *)
let unit_cut t (step : step) =
  if not t.config.subsumption then None
  else
    Telemetry.with_stage t.timing "subsumption" (fun () ->
        Contraction.find ~binary:false ~guard:(fun () -> check_time t) t.contraction step)

(* Forward literal rewriting (flr=on). Equivalence pairs come from retained two-literal clauses C
   and their complementary variants D (RewriteRuleIndex::handleClause, handleEquivalence): C = A | B
   and D = ~A' | ~B' make A equivalent to ~B; the direction that decreases in the literal order,
   with no new variables, is a rule, both when they are incomparable. A literal L of a new clause
   whose atom is an instance of a rule's left literal is replaced by the instance of the other side
   (ForwardLiteralRewriting::perform) when L is greater: one resolution step of the clause with
   the rule clause (L negative) or its counterpart (L positive). The rules are checked for being
   live when used. *)
let flr_live t id = Tbl.Int.mem t.retained_index.live id
let flr_complement (l : literal) = { l with positive = not l.positive }
let flr_variables (l : literal) = Wire.variables [ l ]

let flr_contains_all a b =
  let va = flr_variables a in
  List.for_all (fun v -> List.mem v va) (flr_variables b)

(* The rules of a key oldest first: Vampire takes the first generalization its RewriteRuleIndex
   (a substitution tree, built in insertion order) returns, which here is the oldest rule that
   applies. *)
let flr_add_rule t rule =
  let key = Clause.key { rule.lhs with positive = true } in
  Hashtbl.replace t.flr_rules key
    (Option.value ~default:[] (Hashtbl.find_opt t.flr_rules key) @ [ rule ])

let flr_retain t (step : step) =
  match (vampire t, step.clause) with
  | Some { literal_rewriting = true; _ }, [ a; b ] -> (
      let canon c = Clause.normalize c in
      let complement = canon (List.map flr_complement step.clause) in
      match Hashtbl.find_opt t.flr_partial complement with
      | Some d when flr_live t d && d <> step.id -> (
          Hashtbl.remove t.flr_partial complement;
          (* C = a | b with D its complementary variant: a <=> ~b. Compare the positive side. *)
          let order = t.order in
          let gt l r = Ordering.literal_greater ~order l r in
          let a', b' = if a.positive then (a, flr_complement b) else (flr_complement a, b) in
          let rule lhs position = { lhs; position; clause = step.id; counterpart = d } in
          let from_a () = if flr_contains_all a b then flr_add_rule t (rule a 0) in
          let from_b () = if flr_contains_all b a then flr_add_rule t (rule b 1) in
          match (gt a' b', gt b' a') with
          | true, _ -> from_a ()
          | _, true -> from_b ()
          | _ ->
              from_a ();
              from_b ())
      | _ -> Hashtbl.replace t.flr_partial (canon step.clause) step.id)
  | _ -> ()

let flr_rewrite t (step : step) =
  match vampire t with
  | Some { literal_rewriting = true; _ } when Hashtbl.length t.flr_rules > 0 ->
      let ys = Clause.scope 2 step.clause in
      let attempt i (l : literal) (rule : flr_rule) =
        if rule.clause = step.id || rule.counterpart = step.id then None
        else if not (flr_live t rule.clause && flr_live t rule.counterpart) then None
        else
          let premise = Proof.get t.proof (if l.positive then rule.counterpart else rule.clause) in
          let xs = Clause.scope 1 premise.clause in
          (* The premise literal complementary to [l] and the premise's other literal. *)
          List.find_map
            (fun j ->
              let p = List.nth xs j in
              if p.positive = l.positive then None
              else
                let matches target =
                  try Some (Subsumption.atom [] p.atom target) with Subsumption.No_match -> None
                in
                let sigma =
                  match matches l.atom with
                  | Some s -> Some s
                  | None -> ( match l.atom with E (s, u) -> matches (E (u, s)) | _ -> None)
                in
                match sigma with
                | None -> None
                | Some sigma -> (
                    let app = function
                      | V v -> ( match List.assoc_opt v sigma with Some s -> s | None -> V v)
                      | t -> t
                    in
                    let rec subst = function
                      | V _ as v -> app v
                      | Fn (f, ts) -> Fn (f, List.map subst ts)
                    in
                    match List.nth xs (1 - j) with
                    | other ->
                        let rhs = Clause.map_literal subst other in
                        if List.exists (fun (s, _) -> s = 1) (flr_variables rhs) then None
                        else if not (Ordering.literal_greater ~order:t.order l rhs) then None
                        else
                          Some
                            {
                              Contraction.clause = rhs :: Clause.remove i ys;
                              rule = Resolve (premise.id, j, step.id, i, sigma);
                              using = [ premise.id ];
                            }))
            [ 0; 1 ]
      in
      let rec literals i = function
        | [] -> None
        | (l : literal) :: rest -> (
            let rules =
              Option.value ~default:[]
                (Hashtbl.find_opt t.flr_rules (Clause.key { l with positive = true }))
            in
            match List.find_map (attempt i l) rules with
            | Some _ as r -> r
            | None -> literals (i + 1) rest)
      in
      literals 0 ys
  | _ -> None

let rewrite_ordinary t (step : step) =
  match demodulate t step with Some _ as result -> result | None -> cut t step

let rewrite t (step : step) =
  match destructive_er t step with
  | Some _ as result -> result
  | None -> (
      match vampire t with
      | Some _ -> (
          (* Vampire's order (SaturationAlgorithm::createFromOptions adds each forward simplifier to
             the front): subsumption resolution, then demodulation. *)
          match cut t step with
          | Some _ as result -> result
          | None -> (
              match demodulate t step with Some _ as result -> result | None -> flr_rewrite t step))
      | None -> rewrite_ordinary t step)

(* E's ForwardModifyClause for a lean worker with [normal_form]: destructive equality resolution,
   then rewriting to normal form, before the forward subsumption of admission. A rewritten clause
   is replaced and its normal form is the one that is checked (E's order). The normal form a chain
   just reached ([normal_form_result]) is not searched again. *)
let modify ?peak t (step : step) =
  let normal = step.id = t.normal_form_result in
  if normal then t.normal_form_result <- -1;
  (* [Heuristic.loop.replacing]: E inserts the initial clauses without ForwardModifyClause;
     destructive equality resolution reaches an initial clause when it is selected
     (replacing_inferences). *)
  let initial =
    replacing_strategy t.config.strategy
    && (step.id = t.full_target || match step.rule with Input _ -> true | _ -> false)
  in
  (* The given clause's replacement is still in ForwardContractClause, whose ForwardModifyClause
     removes resolved literals ([Heuristic.loop.resolved]); only destructive equality resolution
     waits for replacing_inferences. *)
  match
    if not initial then destructive_er t step
    else if step.id = t.full_target then resolved_literal t step
    else None
  with
  | Some _ as result -> result
  | None -> if normal then None else demodulate ?peak t step

(* EQ-UNIT test budgets: rule trials per test and rewrite steps per term. An exhausted test keeps
   the clause. *)
let joinability_work = 20000
let joinability_steps = 64

(* Connectedness runs on most unit-unit conclusions, so its budget is smaller, and it tries one
   variable order (the reversed order found about 1.6x the connected conclusions at 1.7x the cost
   on LAT009-1, 5 s, e208). *)
let connected_work = 4000
let connected_flip = false

(* The normal-form memo ([normal_terms]) as a test: a stored subterm in which no rule whose instance
   decreases in every ground instance applies, while the demodulators are those it was filled
   under. *)
let known_irreducible t =
  if t.config.normal_form && t.normal_generation = t.demodulator.generation then
    Some (Physical.mem t.normal_terms)
  else None

(* [ground_redundant t step]: an unorientable positive unit equation of a lean worker that is
   ground joinable with the active unit equations ([test_rules]). It needs a constant (ground
   instances). *)
let ground_redundant t (step : step) =
  t.config.eq_ground_joinable && unit_equality t && (test_rules t).minimal <> None
  &&
  match step.clause with
  | [ { positive = true; atom = E (s, u) } ]
    when s <> u
         && (not (Ordering.greater ~order:t.order s u))
         && not (Ordering.greater ~order:t.order u s) ->
      Telemetry.with_stage t.timing "joinability" (fun () ->
          check_time t;
          Joinability.ground_joinable ?irreducible:(known_irreducible t)
            ~normal:t.config.normal_form ~work:joinability_work ~steps:joinability_steps
            ~order:t.order ~wmin:t.least_weight t.joinability (test_rules t) s u)
  | _ -> false

(* The substitution of a certificate step, applied to a term as the kernel applies it (bindings may
   refer to bound variables). *)
let rec instantiate sigma depth = function
  | V v as x -> (
      match List.assoc_opt v sigma with
      | Some u when depth < 64 -> instantiate sigma (depth + 1) u
      | _ -> x)
  | Fn (f, ts) -> Fn (f, List.map (instantiate sigma depth) ts)

(* The peak of a superposition conclusion between two positive unit equations (EQ-UNIT
   connectedness): [rule] = Paramodulate (p, i, reverse, q, j, path, sigma) rewrote side
   [List.hd path] of the equation [q] (scope 2); the peak is that side instantiated. *)
let peak_of t clause rule =
  match (clause, rule) with
  | [ { positive = true; atom = E (x, y) } ], Paramodulate (_, _, _, q, _, side :: _, sigma)
    when x <> y -> (
      match Clause.scope 2 (Proof.get t.proof q).clause with
      | [ { positive = true; atom = E (l, r) } ] ->
          Some (instantiate sigma 0 (if side = 0 then l else r))
      | _ -> None)
  | _ -> None

(* [connected t step peak]: [step], an unorientable positive unit equation in normal form, is
   connected below [peak] ({!Joinability.connected}), the peak of the superposition it comes from,
   in its variables. An orientable conclusion is kept although it may be connected too: it becomes a
   rewrite rule, and deleting such conclusions removed demodulators the E heuristics rely on
   (LAT009-1 with y1346: 224 given to the proof without the test, none within 660 given with it;
   KLE044-10 with e208 likewise), and cost 3-4 s of 15 s. *)
let connected t (step : step) peak =
  match (step.clause, peak) with
  | [ { positive = true; atom = E (a, b) } ], Some peak
    when a <> b && not (Ordering.greater ~order:t.order a b || Ordering.greater ~order:t.order b a)
    ->
      Telemetry.with_stage t.timing "connectedness" (fun () ->
          check_time t;
          Joinability.connected ?irreducible:(known_irreducible t) ~normal:t.config.normal_form
            ~flip:connected_flip ~work:connected_work ~steps:joinability_steps ~order:t.order
            ~wmin:t.least_weight t.joinability (test_rules t) ~peak a b)
  | _ -> false

(* The indexes of an active clause: generating inferences, forward subsumption and subsumption
   resolution, demodulation. A Vampire slice member's Otter loop already indexed a retained clause
   for forward simplification ([vampire_simplifying]); it is not added twice. *)
(* A Vampire slice member's activated literal enters its substitution tree ([vampire_tries]):
   the arguments' top symbols in the order the tree binds them (its special variables, argument
   by argument and then their arguments, breadth first), variables by first occurrence (the tree
   holds normalized literals). *)
let vampire_symbols (l : literal) =
  let vars = Hashtbl.create 8 in
  let rec normalize = function
    | V v -> if not (Hashtbl.mem vars v) then Hashtbl.replace vars v (Hashtbl.length vars)
    | Fn (_, ts) -> List.iter normalize ts
  in
  List.iter normalize (Clause.atom_terms l.atom);
  let queue = Queue.create () in
  List.iter (fun t -> Queue.add t queue) (Clause.atom_terms l.atom);
  let out = ref [] in
  while not (Queue.is_empty queue) do
    match Queue.take queue with
    | V v -> out := Vvar (Hashtbl.find vars v) :: !out
    | Fn (f, ts) ->
        out := Vsym (f, List.length ts) :: !out;
        List.iter (fun t -> Queue.add t queue) ts
  done;
  Array.of_list (List.rev !out)

let vampire_index t (given : step) eligible =
  List.iteri
    (fun i (l : literal) ->
      if eligible i then (
        let key = Clause.key l in
        let root =
          match Hashtbl.find_opt t.vampire_tries key with
          | Some r -> r
          | None ->
              let r = { children = Hashtbl.create 4; sorted = false; in_order = None } in
              Hashtbl.replace t.vampire_tries key r;
              r
        in
        let symbols = vampire_symbols l in
        ignore
          (Array.fold_left
             (fun node sym ->
               match Hashtbl.find_opt node.children sym with
               | Some (_, child) -> child
               | None ->
                   let child = { children = Hashtbl.create 2; sorted = false; in_order = None } in
                   Hashtbl.replace node.children sym (Hashtbl.length node.children, child);
                   node.in_order <- None;
                   if Hashtbl.length node.children > 3 then node.sorted <- true;
                   child)
             root symbols);
        t.vampire_inserted <- t.vampire_inserted + 1;
        Hashtbl.replace t.vampire_paths (given.id, i) (symbols, t.vampire_inserted)))
    given.clause

(* The resolution partners of a Vampire slice member's given clause in BinaryResolution's order:
   by the given's literal (in its order), then in the order the partner literals' substitution tree
   returns them (its leaves left to right, one leaf's literals in insertion order). *)
let vampire_partners t (hits : (step * (int * int)) list) =
  let id = function
    | Vvar _ -> -1
    | Vsym (f, n) -> (
        match t.order.vampire with
        | Some o -> Option.value ~default:max_int (Hashtbl.find_opt o.ids (Ordering.Function f, n))
        | None -> 0)
  in
  let top_compare a b =
    match (a, b) with
    | Vvar x, Vvar y -> compare x y
    | Vvar _, Vsym _ -> -1
    | Vsym _, Vvar _ -> 1
    | Vsym _, Vsym _ -> compare (id a) (id b)
  in
  (* A partner's place: the rank of each of its symbols among its node's children (insertion
     rank, or sorted rank once the node is sorted), then its insertion count. *)
  let rank (node : vampire_trie) sym =
    if not node.sorted then
      match Hashtbl.find_opt node.children sym with Some (r, _) -> r | None -> max_int
    else
      let sorted =
        match node.in_order with
        | Some s -> s
        | None ->
            let s =
              Hashtbl.fold (fun k _ acc -> k :: acc) node.children []
              |> List.sort top_compare |> Array.of_list
            in
            node.in_order <- Some s;
            s
      in
      let rec find i =
        if i >= Array.length sorted then max_int else if sorted.(i) = sym then i else find (i + 1)
      in
      find 0
  in
  let roots = Hashtbl.create 4 in
  let place ((s : step), (_, j)) =
    match Hashtbl.find_opt t.vampire_paths (s.id, j) with
    | None -> [ max_int ]
    | Some (symbols, count) -> (
        let key = Clause.key (List.nth s.clause j) in
        let root =
          match Hashtbl.find_opt roots key with
          | Some r -> r
          | None ->
              let r = Hashtbl.find_opt t.vampire_tries key in
              Hashtbl.replace roots key r;
              r
        in
        let rec walk node k acc =
          if k >= Array.length symbols then List.rev (count :: acc)
          else
            match Hashtbl.find_opt node.children symbols.(k) with
            | Some (_, child) -> walk child (k + 1) (rank node symbols.(k) :: acc)
            | None -> List.rev (count :: acc)
        in
        match root with Some r -> walk r 0 [] | None -> [ count ])
  in
  List.map (fun ((_, (i, _)) as hit) -> ((i, place hit), hit)) hits
  |> List.stable_sort (fun (a, _) (b, _) -> compare a b)
  |> List.map snd

let index_active t (given : step) =
  let eligible = Calculus.candidates t.calculus given in
  Index.add ~eligible t.index given;
  if
    t.config.subsumption && t.config.subsumption_indexed
    && not (Tbl.Int.mem t.subsumption_index.live given.id)
  then Subsumption_index.add t.subsumption_index given;
  if t.config.equality_indexed then Equality_index.add ~eligible t.equality_index given;
  if t.config.demodulation && not (Tbl.Int.mem t.demodulator.live given.id) then
    Demodulation.add t.demodulator given;
  Option.iter (fun e -> Demodulation.add e given) t.equations;
  if vampire t <> None then vampire_index t given eligible;
  match vampire t with
  | Some { unit_resulting = true; _ } -> (
      let push table key =
        Hashtbl.replace table key (given.id :: Option.value ~default:[] (Hashtbl.find_opt table key))
      in
      match given.clause with
      | [ l ] -> push t.urr_units (Clause.key l)
      | ls -> List.iter (push t.urr_nonunits) (List.sort_uniq compare (List.map Clause.key ls)))
  | _ -> ()

(* Splitter::doSplitting for a Vampire slice member with AVATAR: the clause's variable-disjoint
   components get names (a new name's component clause enters the search once the model asserts
   it, [synchronize]) and the clause itself is replaced by the split constraint: it leaves the
   search, as Vampire never activates a clause it split. Vampire splits a clause when it enters
   Passive, or with sac=on when it is selected. Returns whether it split. *)
let vampire_split t (step : step) =
  match (vampire t, step.rule) with
  | Some v, rule
    when v.avatar && t.config.avatar && match rule with Component _ -> false | _ -> true ->
      let avatar = t.avatar in
      let first = Tbl.Int.length avatar.components in
      if Avatar.split avatar ~guard:(fun () -> check_time t) step then (
        for id = first to Tbl.Int.length avatar.components - 1 do
          Hashtbl.replace t.vampire_parents id step.id;
          let component = Tbl.Int.find avatar.components id in
          let recorded = record t component.clause (Component id) in
          match Ground.unit recorded with
          | Some literal ->
              let known =
                Option.value ~default:[] (Tbl.Atom.find_opt t.component_atoms literal.atom)
              in
              List.iter
                (fun (positive, other) ->
                  if positive <> literal.positive then
                    let conflict = record t [] (Resolve (recorded.id, 0, other, 0, [])) in
                    Avatar.conflict avatar ~guard:(fun () -> check_time t) conflict)
                known;
              Tbl.Atom.replace t.component_atoms literal.atom
                ((literal.positive, recorded.id) :: known)
          | None -> ()
        done;
        retire t step.id;
        true)
      else false
  | _ -> false

(* Vampire's Otter and LRS loops simplify with Passive and Active clauses (Otter's
   simplifying container); DISCOUNT only with Active ones. *)
let vampire_simplifying t =
  match vampire t with Some v -> v.saturation <> Vampire.Discount | None -> false

(* A Vampire slice's split-queue features of a clause: its number of positive literals. *)
let vampire_features (step : step) =
  [| List.fold_left (fun n (l : literal) -> if l.positive then n + 1 else n) 0 step.clause |]

(* Vampire's LRS limit maintenance (LRS::poppedFromUnprocessed, shouldUpdateLimits,
   PassiveClauseContainer::updateLimits) on the work clock: after more than 10 activations, at
   every 500th clause that enters forward simplification (every 51st while limits are set), an
   estimate of the reachable activations from the work spent and the worker's budget; with an
   estimate below the Passive size, the limits from simulating that many selections. Retroactive
   deletion (lrd) is not ported: only new clauses are dropped ([lrs_drops]), Vampire's default. *)
let lrs_update t =
  match vampire t with
  | Some { saturation = Vampire.Lrs; _ } when t.metrics.given > 10 ->
      t.lrs_counter <- t.lrs_counter + 1;
      if t.lrs_counter = 500 || (t.lrs_limits <> None && t.lrs_counter > 50) then (
        t.lrs_counter <- 0;
        let now = work_reading t in
        let budget = int_of_float (t.config.limits.seconds *. work_units_per_second) in
        match
          Vampire.reachable ~activations:t.metrics.given
            ~elapsed:(now - int_of_float t.allocated_start)
            ~since_first:(now - Option.value ~default:now t.lrs_first)
            ~budget
        with
        | None -> ()
        | Some n when Passive.split t.passive ->
            (* Split containers: every leaf has limits of its own. *)
            ignore (Passive.update_split_limits t.passive ~count:n : bool);
            t.lrs_limits <-
              (if Passive.split_limited t.passive then Some Vampire.no_limits else None)
        | Some n when n > Passive.length t.passive -> t.lrs_limits <- None
        | Some n -> (
            match Passive.simulate_balance t.passive ~count:n with
            | Some evals -> t.lrs_limits <- Some (Vampire.limits_of evals)
            | None -> ()))
  | _ -> ()

(* lrs_preemptive_deletes (on by default): a new clause beyond every limit is not kept. *)
let lrs_drops t (step : step) =
  match (vampire t, t.lrs_limits) with
  | Some v, Some limits ->
      let age = Option.value ~default:0 (Hashtbl.find_opt t.vampire_ages step.id)
      and weight =
        Vampire.selection_weight v ~goal:(Hashtbl.mem t.vampire_goals step.id) step.clause
      in
      if Passive.split t.passive then
        Passive.split_exceeds t.passive ~features:(vampire_features step) ~age ~weight
      else Vampire.exceeds_all_limits limits ~age ~weight
  | _ -> false

(* Without forward subsumption (fs=off) Vampire keeps a clause that repeats a retained one. The
   port keeps repeated input clauses only (e.g. two inputs that equality resolution with deletion
   makes equal): its exact-duplicate check also absorbs the repeated conclusions of symmetric
   inference pairs, which Vampire does not generate. *)
let vampire_keeps_duplicates t =
  match vampire t with Some v -> not v.forward_subsumption | None -> false

(* A Vampire set-of-support clause (sos=on): an input clause, or its equality resolution with
   deletion, that is not a negated conjecture. It goes to Active without being selected. *)
let vampire_sos t (step : step) =
  match vampire t with
  | Some v ->
      v.sos && Hashtbl.mem t.vampire_inputs step.id && not (Hashtbl.mem t.vampire_goals step.id)
  | None -> false

(* The premises of the generating inference behind a clause that [emit] stores ([origins]): those
   that [origin_next] passes on, else the rule's parents. *)
let origin_premises origin rule =
  match origin with
  | Some premises -> premises
  | None -> ( match rule with Input _ | Component _ -> [] | _ -> Wire.parents rule)

let dead_premise t premises = List.exists (fun p -> Tbl.Int.mem t.dead p) premises

(* [Heuristic.loop.orphans] with duplicate deletion. E drops a Passive clause whose generating
   inference has a premise that backward simplification retired ([orphan]). That loses nothing in
   E because E deletes no clause on account of an unprocessed one: it has no duplicate deletion
   and subsumes with processed clauses only. Here a duplicate check also accepts a Passive repeat
   (at emission without [Heuristic.loop.duplicates], and in [admit] for a FullRewrite target), and
   the clause it drops ([clause], [premises] as in [origins]) then lives on only in that repeat.
   So unless the dropped clause is an orphan itself or an active clause repeats it, its Passive
   repeats stop being orphans. Otherwise both copies could go: in the minimal case of
   tests/unit/heuristic_tests.ml, the backward-rewrite replacement X = a, a FullRewrite target, is
   dropped for a Passive X = a whose premises that rewrite retired, the Passive copy is then dropped
   as an orphan, and x1276 runs out of Passive clauses on an unsatisfiable input. *)
let absorb_duplicate t ~except ~premises support clause =
  if not (dead_premise t premises) then
    let repeats =
      Avatar.duplicates t.avatar
        ~guard:(fun () -> check_time t)
        ~variants:t.config.variants ~except support clause
    in
    if not (List.exists (fun id -> Index.mem t.index id) repeats) then
      List.iter (fun id -> Tbl.Int.remove t.origins id) repeats

let rec emit t clause rule =
  (* E clause facts for the direct conclusion only, never for its consequences. *)
  let initial = t.inherit_initial || match rule with Input _ -> true | _ -> false
  and processed = t.mark_processed
  and unfolded_input = t.unfolded_next
  and rewritten = t.rewrite_emit
  and normal = match t.normal_form_rule with Some r -> r == rule | None -> false
  and peak = t.peak
  and full = t.full_next
  and origin = t.origin_next
  and simplified = t.vampire_simplified
  and vampire_input = t.vampire_input
  and vampire_position = t.vampire_position
  and vampire_number = t.vampire_number
  and direct = t.vampire_direct in
  t.vampire_number <- None;
  t.vampire_direct <- false;
  t.full_next <- false;
  t.origin_next <- None;
  t.vampire_simplified <- None;
  t.vampire_input <- None;
  t.vampire_position <- None;
  t.peak <- None;
  t.inherit_initial <- false;
  t.mark_processed <- false;
  t.unfolded_next <- false;
  t.rewrite_emit <- false;
  t.normal_form_rule <- None;
  check_time t;
  match t.vampire_batch with
  | Some pending when not direct ->
      (* A new clause of a Vampire activation waits until the activation has generated all of
         its clauses ([vampire_process_batch]); its number is the order of creation, unless the
         inference gave it one ([urr_generate]). *)
      let number =
        match vampire_number with
        | Some k -> k
        | None ->
            t.vampire_count <- t.vampire_count + 1;
            t.vampire_count
      in
      (match !given_trace with
      | Some write when !new_trace ->
          write
            (Printf.sprintf "%s\t%d\t%d\tgen\t%s\t%s\t0\t%s\n" t.config.strategy.name
               t.metrics.given number
               (match simplified with Some p -> "simplifies:" ^ string_of_int p | None -> "")
               (String.concat "," (List.map string_of_int (Wire.parents rule)))
               (Given_trace.clause clause))
      | _ -> ());
      t.vampire_batch <-
        Some
          ({
             vn_clause = clause;
             vn_rule = rule;
             vn_simplified = simplified;
             vn_peak = peak;
             vn_rewritten = rewritten;
             vn_number = number;
           }
          :: pending)
  | _ ->
      if t.metrics.generated >= t.config.limits.max_generated then stop t "generated clause limit";
      t.metrics.generated <- t.metrics.generated + 1;
      let raw = clause in
      let clause, obvious =
        Telemetry.with_stage t.timing "simplification" (fun () ->
            let clause = Clause.normalize clause in
            if Clause.tautology_sorted clause then (
              t.metrics.tautologies <- t.metrics.tautologies + 1;
              (clause, true))
            else
              let clause =
                List.map
                  (Clause.map_literal (fun term -> Term.to_wire t.terms (Term.of_wire t.terms term)))
                  clause
              in
              t.probe <- Avatar.probe clause;
              let duplicate =
                match rule with
                | Component _ -> false
                (* DISCOUNT keeps a duplicate until it is selected. *)
                | _ when duplicates_strategy t.config.strategy -> false
                | _ when t.presat_running && presat_duplicates_strategy t.config.strategy -> false
                | _
                  when vampire_keeps_duplicates t
                       && (vampire_input <> None
                          ||
                          match (rule, simplified) with
                          | Equality_resolve _, Some p -> Hashtbl.mem t.vampire_inputs p
                          | _ -> false) ->
                    false
                | _ ->
                    Avatar.duplicate ~probe:t.probe t.avatar
                      ~guard:(fun () -> check_time t)
                      ~variants:t.config.variants ~except:(-1)
                      (Avatar.dependencies t.avatar rule)
                      clause
              in
              if duplicate then t.metrics.duplicates <- t.metrics.duplicates + 1;
              (clause, duplicate))
      in
      (* A clause dropped here that is not a tautology was dropped as a duplicate. (Outside the stage
     closure, so that the closure of every other worker stays as it is.) *)
      if obvious && orphans_strategy t.config.strategy && not (Clause.tautology_sorted clause) then
        absorb_duplicate t ~except:(-1) ~premises:(origin_premises origin rule)
          (Avatar.dependencies t.avatar rule)
          clause;
      let redundant = obvious in
      if redundant then t.metrics.redundant <- t.metrics.redundant + 1
      else (
        if Proof.stored t.proof >= t.config.limits.max_retained then stop t "retained clause limit";
        let step = store t clause rule in
        if full then t.full_target <- step.id;
        (if discount_strategy t.config.strategy then
           let premises = origin_premises origin rule in
           if premises <> [] then Tbl.Int.replace t.origins step.id premises);
        if unfolded_input then Hashtbl.replace t.unfolded_inputs step.id ();
        if rewritten then t.rewrite_result <- step.id;
        if normal then t.normal_form_result <- step.id;
        if lean t then (
          if initial then Hashtbl.replace t.initial_ids step.id ();
          if processed then Hashtbl.replace t.processed_ids step.id ();
          note_sos t step rule;
          if vampire t <> None then
            note_vampire t step rule ?input:vampire_input ?position:vampire_position
              ?number:vampire_number simplified);
        Transfer_policy.derived ~direct:true t.emission_observer step;
        focus_register t step.id;
        ignore (Avatar.remember ~probe:t.probe t.avatar ~variants:t.config.variants step);
        Ground_boolean.note t.ground_boolean
          ~guard:(fun () -> check_time t)
          ~support:(Avatar.dependency t.avatar step.id)
          step;
        observe t "derived" step;
        let parents = Wire.parents rule in
        let previous =
          List.fold_left (fun n id -> max n (List.length (Proof.get t.proof id).clause)) 0 parents
        in
        if List.length clause < previous then
          reward t parents (min 8 (2 * (previous - List.length clause)));
        t.metrics.retained <- t.metrics.retained + 1;
        if clause = [] then (
          reward ~closed:true t parents 32;
          if Avatar.dependency t.avatar step.id <> [] then (
            t.on_conflict
              ~guard:(fun () -> check_time t)
              (List.map (Proof.get t.proof) (Wire.parents rule));
            Avatar.conflict t.avatar ~guard:(fun () -> check_time t) step;
            Transfer_policy.admitted t.emission_observer Goal_transfer.Conditional_empty step)
          else (
            t.root <- Some step.id;
            Transfer_policy.admitted t.emission_observer Goal_transfer.Unconditional_empty step;
            raise Stop))
        else (
          t.admit_peak <- (match peak with None -> None | Some _ -> renamed_peak raw peak);
          admit t step))

and contract t (step : step) ({ clause; rule; using } : Contraction.result) =
  match (step.clause, Clause.normalize clause) with
  | [ old ], [ changed ] when old.atom = changed.atom && old.positive <> changed.positive ->
      (* Under the legacy equivalence rule (Contraction.Legacy: AXIOM_EQUIVALENCE=legacy and
         the Vampire slices) an equivalence can rewrite a unit to its own complement; the
         default never rewrites a unit, and the other contractions keep polarity or delete a
         literal. Close that conflict before retirement or duplicate elimination loses the
         pair. Its resolvents are not a replacement of a given clause ([capture]). *)
      if t.capture = Armed then t.capture <- Off;
      t.peak <- None;
      let consequence = record t clause rule in
      observe t "derived" consequence;
      Calculus.resolve t.calculus step consequence (emit t);
      reduce_using t ~target:step.id ~using
  | _ ->
      let hidden = reduce_using t ~target:step.id ~using in
      (* E simplifies a clause in place: its replacement keeps its E clause facts. *)
      t.inherit_initial <-
        Hashtbl.mem t.initial_ids step.id
        && ((not (cp_initial_strategy t.config.strategy))
           || match rule with Equality_resolve (_, _, _ :: _) -> true | _ -> false);
      t.mark_processed <- Hashtbl.mem t.processed_ids step.id;
      t.rewrite_emit <- (match rule with Paramodulate _ -> true | _ -> false);
      (* The replacement of a FullRewrite target is rewritten at the same level (E's
         ForwardContractClause runs to a fixed point). *)
      t.full_next <- step.id = t.full_target && full_rewrite_strategy t.config.strategy;
      if discount_strategy t.config.strategy then
        t.origin_next <- Some (Option.value ~default:[] (Tbl.Int.find_opt t.origins step.id));
      t.vampire_simplified <- Some step.id;
      emit t clause rule;
      hidden

and admit t (step : step) =
  lrs_update t;
  let avatar = t.avatar in
  let early = lean t && t.config.normal_form && vampire t = None in
  (* DISCOUNT defers subsumption and the full contraction to the selection; the given clause's
     own replacement ([full_target]) is contracted now, as E's ForwardContractClause does. *)
  let deferred = discount_strategy t.config.strategy && step.id <> t.full_target in
  let peak = t.admit_peak in
  t.admit_peak <- None;
  (* A forward rewrite result that is rewritten again in its own admission ran the admission
     as an intermediate ([rewrite_reentries]). *)
  let entering = step.id = t.rewrite_result in
  if entering then t.rewrite_result <- -1;
  let replace (result : Contraction.result) =
    (match result.rule with
    | Paramodulate _ when entering -> t.metrics.rewrite_reentries <- t.metrics.rewrite_reentries + 1
    | _ -> ());
    let hidden = contract t step result in
    if not hidden then retain t step
  in
  if
    ((not deferred) || not (duplicates_strategy t.config.strategy))
    (* [Heuristic.loop.presat_duplicates]: the given's replacement meets the active clauses in its
       contraction below, as E's meets only the processed set. *)
    && (not (t.presat_running && presat_duplicates_strategy t.config.strategy))
    && (not (vampire_keeps_duplicates t && Hashtbl.mem t.vampire_inputs step.id))
    && Avatar.duplicate ~probe:t.probe avatar
         ~guard:(fun () -> check_time t)
         ~variants:t.config.variants ~except:step.id
         (Avatar.dependency avatar step.id)
         step.clause
  then (
    t.metrics.duplicates <- t.metrics.duplicates + 1;
    (* With [Heuristic.loop.duplicates] only a FullRewrite target (the replacement of the given
       clause or of a backward-rewritten active clause) reaches this check. *)
    if orphans_strategy t.config.strategy then
      absorb_duplicate t ~except:step.id
        ~premises:(Option.value ~default:[] (Tbl.Int.find_opt t.origins step.id))
        (Avatar.dependency avatar step.id)
        step.clause;
    retire t step.id;
    t.metrics.redundant <- t.metrics.redundant + 1)
  else if not (Avatar.enabled avatar (Tbl.Int.find avatar.entries step.id)) then
    t.metrics.redundant <- t.metrics.redundant + 1
  else if lrs_drops t step then (
    retire t step.id;
    t.lrs_discarded <- t.lrs_discarded + 1;
    t.metrics.redundant <- t.metrics.redundant + 1)
  else if vampire_sos t step then
    (* SaturationAlgorithm::addInputSOSClause: only the immediate simplifications. *)
    match destructive_er t step with
    | Some result -> replace result
    | None -> retain t step
  else
    match if early then modify ?peak t step else None with
    | Some result -> replace result
    | None -> (
        if
          t.config.subsumption && (not deferred)
          && (match vampire t with Some v -> v.forward_subsumption | None -> true)
          && Telemetry.with_stage t.timing "subsumption" (fun () ->
              match forward_subsumer ~except:step.id t step.clause with
              | Some using when reduce t ~target:step.id ~using:using.id ->
                  t.metrics.subsumed <- t.metrics.subsumed + 1;
                  true
              | _ -> false)
        then t.metrics.redundant <- t.metrics.redundant + 1
        else
          match
            if deferred && early then unit_cut t step
            else if early then cut t step
            else rewrite t step
          with
          | Some result -> replace result
          | None ->
              if connected t step peak || ground_redundant t step then (
                retire t step.id;
                t.metrics.redundant <- t.metrics.redundant + 1)
              else (
                retain t step;
                derive t step))

(* The default rule Contraction.Derive (AXIOM_EQUIVALENCE=derive): a retained clause that only
   the legacy rule would rewrite with an equivalence keeps its place, and the rewritten clause is
   added as an ordinary consequence (its resolvent with the side clause), so nothing is deleted. It
   runs after [retain], so the consequence is never taken for a given clause's replacement. *)
and derive t (step : step) =
  if
    t.contraction.equivalence = Contraction.Derive
    && t.config.subsumption && literal_rewriting t
    && not (discount_strategy t.config.strategy && step.id <> t.full_target)
  then
    match
      Telemetry.with_stage t.timing "subsumption" (fun () ->
          Contraction.derive ~guard:(fun () -> check_time t) t.contraction step)
    with
    | None -> ()
    | Some { clause; rule; _ } ->
        if t.capture = Armed then t.capture <- Off;
        t.peak <- None;
        emit t clause rule

and retain t (step : step) =
  match vampire t with
  | Some v when (not v.split_at_activation) && (not (vampire_sos t step)) && vampire_split t step ->
      (* forwardSimplify's last step: a split clause does not enter Passive. *)
      ()
  | _ ->
      (* General clauses use forward simplification. Reserve backward sweeps for
     selected units, rather than paying for every generated candidate. *)
      if t.capture = Armed then t.capture <- Captured step.id;
      let ground = Ground.unit step in
      let weight =
        match t.config.strategy.weight with Strategy.Standard_weight -> Clause.weight step.clause
      in
      let kind = Passive.classify step.clause in
      (* [Heuristic.loop.presat]: E's evaluation counter orders equal evaluations and is the FIFO
     weight; otherwise the clause id, which grows with creation and so in evaluation order unless a
     clause re-enters Passive (as at the end of presaturation). *)
      let order =
        if presat_strategy t.config.strategy then (
          t.evaluations <- t.evaluations + 1;
          t.evaluations)
        else step.id
      in
      let evals =
        Option.map
          (fun (h : Heuristic.t) ->
            Telemetry.with_stage t.timing "evaluation" (fun () ->
                match h.vampire with
                | Some v ->
                    Vampire.evaluations v
                      ~age:(Option.value ~default:0 (Hashtbl.find_opt t.vampire_ages step.id))
                      ~goal:(Hashtbl.mem t.vampire_goals step.id)
                      step.clause
                | None ->
                    Evaluation.evaluate ~order:t.order ~selection:h.selection
                      ?rank:
                        (match t.calculus.e_code with
                        | None -> None
                        | Some code -> Some (Eselection.e_rank ~code step.clause))
                      ~prefer_initial:
                        (h.prefer_initial
                        && ((not (replacing_strategy t.config.strategy)) || t.inserting_initial))
                      h.queues
                      {
                        initial = Hashtbl.mem t.initial_ids step.id;
                        sos = Hashtbl.mem t.sos_ids step.id;
                        processed = Hashtbl.mem t.processed_ids step.id;
                        conjecture = t.conjecture;
                        age = order;
                        level =
                          (if t.sine = None then 0
                           else Option.value ~default:0 (Hashtbl.find_opt t.levels step.id));
                        relevance = t.relevance;
                      }
                      step.clause))
          t.config.strategy.heuristic
      in
      let sos = vampire_sos t step in
      let number = Hashtbl.find_opt t.vampire_numbers step.id in
      (match !given_trace with
      | Some write when !new_trace && lean t ->
          let tag =
            match step.rule with
            | Input _ -> "input"
            | Component _ -> "component"
            | Resolve _ -> "resolve"
            | Factor _ -> "factor"
            | Equality_resolve _ -> "er"
            | Equality_factor _ -> "ef"
            | Paramodulate _ -> "pm"
          in
          write
            (Printf.sprintf "%s\t%d\t%d\tnew\t%s\t%s\t0\t%s\n" t.config.strategy.name
               t.metrics.given step.id tag
               (String.concat "," (List.map string_of_int (Wire.parents step.rule)))
               (Given_trace.clause step.clause))
      | _ -> ());
      let features = if Passive.split t.passive then Some (vampire_features step) else None in
      if sos then ()
      else if t.config.clause_weight = Passive.Size then
        Passive.add ~kind ?evals ~order ?number ?features t.passive step.id weight
      else
        Passive.add ~kind ?evals ~order ?number ?features
          ~unit_weight:(weight + (4 * max 0 (List.length step.clause - 1)))
          t.passive step.id weight;
      (match (!eval_trace, evals) with
      | Some write, Some evals when lean t && not sos ->
          write
            (Printf.sprintf "%d\t%d\t%d\t%s%s\t%s\t%s\n" step.id order t.metrics.given
               (if Hashtbl.mem t.initial_ids step.id then "i" else "-")
               (if Hashtbl.mem t.processed_ids step.id then "p" else "-")
               (String.concat ","
                  (Array.to_list (Array.map (fun (p, w) -> Printf.sprintf "%d:%g" p w) evals)))
               (Given_trace.clause step.clause))
      | _ -> ());
      (match !selection_guide with Some g when lean t -> g.retained step | _ -> ());
      (* A unit given of [Heuristic.loop.e_calculus] resolves with active clauses only, so no lean
     search reads a posting of the retained index (it keeps the clause's ticket), as E indexes no
     unprocessed clause. *)
      (* A live id added again gets a new ticket: the goal table's collection must test the old
         one. *)
      if Index.mem t.retained_index step.id then Goal.supersede t.goals step.id;
      if Calculus.e_calculus t.calculus then
        Index.add ~eligible:(fun _ -> false) t.retained_index step
      else Index.add t.retained_index step;
      flr_retain t step;
      Transfer_policy.admitted t.emission_observer Goal_transfer.Retained step;
      (* DISCOUNT: a Passive clause simplifies nothing; it joins the Contraction when activated. *)
      let discount = discount_strategy t.config.strategy in
      if t.config.subsumption && not discount then Contraction.add t.contraction step;
      observe t "retained" step;
      Directions.observe t.directions "admitted" step.rule;
      let guard () = check_time t in
      if not (lean t) then (
        Focus.note t.focus ~guard (step.id, Tbl.Int.find t.retained_index.live step.id) step;
        Goal.note t.goals ~guard
          ~support:(Avatar.dependency t.avatar step.id)
          (step.id, Tbl.Int.find t.retained_index.live step.id)
          step;
        Passive.prefer t.passive step.id (Focus.credit t.focus step.id + pressure t step));
      (match
         if lean t then None
         else
           Focus.request t.focus (step.id, Tbl.Int.find t.retained_index.live step.id) step.clause
       with
      | None -> ()
      | Some wanted ->
          t.on_demand ~guard [ wanted ];
          Index.sample ~guard t.retained_index { wanted with positive = not wanted.positive }
          |> List.iter (fun (candidate : step) ->
              Passive.prefer t.passive candidate.id (pressure t candidate)));
      Option.iter
        (fun literal ->
          Option.iter
            (fun (_, old) -> count_ground_unit t old (-1))
            (Tbl.Int.find_opt t.ground_units step.id);
          Tbl.Int.replace t.ground_units step.id (step, literal);
          count_ground_unit t literal 1;
          t.knowledge_epoch <- t.knowledge_epoch + 1;
          let listed = Tbl.Literal.find_opt t.ground_literals literal in
          if Option.is_none listed && Tbl.Literal.mem t.ground_literals (complementary literal) then
            t.ground_clashes <- t.ground_clashes + 1;
          Tbl.Literal.replace t.ground_literals literal (step.id :: Option.value ~default:[] listed);
          (* Exact ground conflicts are cheap and should not wait for a scheduled
         congruence rebuild or for the unit to become a given clause. *)
          List.iter
            (fun other ->
              t.ground.conflicts <- t.ground.conflicts + 1;
              emit t [] (Resolve (step.id, 0, other, 0, [])))
            (Option.value ~default:[]
               (Tbl.Literal.find_opt t.ground_literals
                  { literal with positive = not literal.positive })))
        ground;
      if t.config.subsumption && t.config.subsumption_indexed && not discount then
        Subsumption_index.add t.retained_subsumption step;
      if sos then (
        index_active t step;
        observe t "active" step)
      else if vampire_simplifying t then (
        if t.config.subsumption && t.config.subsumption_indexed then
          Subsumption_index.add t.subsumption_index step;
        if t.config.demodulation then Demodulation.add t.demodulator step);
      (* [Heuristic.loop.e_calculus]: a clause's unary inferences wait for its selection; a Vampire
     slice's run when it is activated ([process_given]). *)
      if not (Calculus.e_calculus t.calculus || t.presat_running || vampire t <> None) then
        Telemetry.with_stage t.timing "inference" (fun () ->
            Calculus.unary t.calculus step (emit t))

(* SaturationAlgorithm's order for a Vampire slice member: an activation's new clauses wait in
   [vampire_batch] (_newClauses, a stack) until it has generated all of them; then they enter the
   unprocessed queue newest first (newClausesToUnprocessed), which is processed front to back
   (doUnprocessedLoop: forward simplification, then Passive), and the clauses that processing one
   of them creates (its simplified replacement) join the back of the queue, newest first. *)

let vampire_process_batch t =
  match t.vampire_batch with
  | None -> ()
  | Some first ->
      let unprocessed = Queue.create () in
      List.iter (fun n -> Queue.add n unprocessed) first;
      t.vampire_batch <- Some [];
      Fun.protect
        ~finally:(fun () -> t.vampire_batch <- None)
        (fun () ->
          while not (Queue.is_empty unprocessed) do
            let n = Queue.take unprocessed in
            t.vampire_simplified <- n.vn_simplified;
            t.peak <- n.vn_peak;
            t.rewrite_emit <- n.vn_rewritten;
            t.vampire_number <- Some n.vn_number;
            t.vampire_direct <- true;
            emit t n.vn_clause n.vn_rule;
            match t.vampire_batch with
            | Some (_ :: _ as more) ->
                List.iter (fun m -> Queue.add m unprocessed) more;
                t.vampire_batch <- Some []
            | _ -> ()
          done)

let emit_consumed t ~recorded ~accepted clause rule =
  let previous = t.emission_observer in
  t.emission_observer <- Some (Transfer_policy.observer ~recorded ~accepted);
  Fun.protect ~finally:(fun () -> t.emission_observer <- previous) (fun () -> emit t clause rule)

(* Equational-definition unfolding ([Unfold], [add_initial_axioms]). [through] rewrites a stored
   clause with the removed definitions in removal order, recording every step as a proof ancestor
   that the search does not see ([record]); it returns the last node. *)
let rec through t sources (current : step) =
  match Unfold.next sources current with
  | None -> current
  | Some ((clause, rule), sources) -> through t sources (record t clause rule)

(* An input clause through the removed definitions: unchanged, it is emitted as given. Otherwise
   its input node and every step but the last are recorded, and the last paramodulation step is
   emitted in its place, an initial clause (E unfolds the clause in place). *)
let emit_unfolded t clause rule =
  match t.unfolded with
  | [] -> emit t clause rule
  | sources -> (
      let provisional clause rule = { id = -1; clause = Clause.normalize clause; rule } in
      match Unfold.next sources (provisional clause rule) with
      | None -> emit t clause rule
      | Some _ ->
          (* The memory budget keeps the input clauses of a fixed axiom; it keeps their unfolded
             forms too. A releasable axiom's unfolded clauses are ordinary derived clauses. *)
          let fixed =
            match rule with Input (a, _) -> not (Hashtbl.mem t.releasable a) | _ -> false
          in
          let last clause rule =
            t.inherit_initial <- true;
            t.unfolded_next <- fixed;
            emit t clause rule
          in
          let rec go sources (current : step) =
            match Unfold.next sources current with
            | None -> last current.clause current.rule
            | Some ((clause, rule), sources) ->
                if Option.is_none (Unfold.next sources (provisional clause rule)) then
                  last clause rule
                else go sources (record t clause rule)
          in
          go sources (record t clause rule))

let split_step t avatar =
  match Avatar.take_split avatar ~guard:(fun () -> check_time t) with
  | None -> ()
  | Some parent ->
      let first = Tbl.Int.length avatar.components in
      if Avatar.split avatar ~guard:(fun () -> check_time t) parent then
        for id = first to Tbl.Int.length avatar.components - 1 do
          if vampire t <> None then Hashtbl.replace t.vampire_parents id parent.id;
          let component = Tbl.Int.find avatar.components id in
          let step = record t component.clause (Component id) in
          match Ground.unit step with
          | Some literal ->
              let known =
                Option.value ~default:[] (Tbl.Atom.find_opt t.component_atoms literal.atom)
              in
              List.iter
                (fun (positive, other) ->
                  if positive <> literal.positive then
                    let conflict = record t [] (Resolve (step.id, 0, other, 0, [])) in
                    Avatar.conflict avatar ~guard:(fun () -> check_time t) conflict)
                known;
              Tbl.Atom.replace t.component_atoms literal.atom ((literal.positive, step.id) :: known)
          | None -> ()
        done

let ground_step t =
  (match
     Ground_boolean.advance t.ground_boolean
       ~guard:(fun () -> check_time t)
       ~get:(Proof.get t.proof)
       ~record:(record_ground_explanation ~support:[] t)
   with
  | None -> ()
  | Some step ->
      t.root <- Some step.id;
      raise Stop);
  let epoch = t.knowledge_epoch in
  if epoch <> t.ground_epoch then
    (* Without a unit equation, run_units only compares the unit atoms: a negative s <> s or a
       negative unit whose atom has a positive unit is a conflict. With neither, it finds none
       and only counts its run. *)
    if t.ground_equations = 0 && t.ground_clashes = 0 && t.ground_reflexive = 0 then
      t.ground.runs <- t.ground.runs + 1
    else
      Ground.run_units t.ground ~explanation:t.config.ground_explanation ~avatar:t.avatar
        ~guard:(fun () -> check_time t)
        ~record:(record t)
        ~conflict:(fun _ rule -> emit t [] rule)
        (Tbl.Int.fold (fun _ s steps -> s :: steps) t.ground_units []
        |> List.sort (fun ((a : step), _) (b, _) -> compare a.id b.id));
  t.ground_epoch <- epoch;
  t.ground_given <- t.metrics.given

let ground_ready t =
  (* Nor the ground unit congruence runs (Vampire's avatar_congruence_closure is off). *)
  if vampire t <> None then false
  else if lean t then
    (Ground_boolean.has_work t.ground_boolean || t.knowledge_epoch <> t.ground_epoch)
    && (Passive.length t.passive = 0 || t.metrics.given - t.ground_given >= 256)
  else
    Ground_boolean.has_work t.ground_boolean
    || t.knowledge_epoch <> t.ground_epoch
       && (Tbl.Int.length t.ground_units < 128
          || Passive.length t.passive = 0
          || t.metrics.given - t.ground_given >= 32
          || t.knowledge_epoch - t.ground_epoch >= max 1 (Tbl.Int.length t.ground_units / 8))

(* Branch changes happen between inferences. All old invalid memberships are
   removed before any restored clause can use the indices for simplification. *)
let synchronize t =
  let avatar = t.avatar in
  while avatar.dirty && t.root = None && t.stopped = None do
    let changed =
      Telemetry.with_stage t.timing "boolean" (fun () ->
          Avatar.solve avatar ~guard:(fun () -> check_time t))
    in
    if avatar.unsat then t.root <- Some 0
    else
      Telemetry.with_stage t.timing "branch_update" (fun () ->
          let entries = Avatar.affected_entries avatar ~guard:(fun () -> check_time t) changed in
          Avatar.unlock avatar ~guard:(fun () -> check_time t) entries;
          List.iter
            (fun (e : Avatar.entry) ->
              check_time t;
              if Index.mem t.retained_index e.step.id && not (Avatar.enabled avatar e) then (
                deactivate t e.step.id;
                avatar.deactivated <- avatar.deactivated + 1))
            entries;
          List.iter
            (fun (e : Avatar.entry) ->
              check_time t;
              if Avatar.enabled avatar e && not (Index.mem t.retained_index e.step.id) then (
                avatar.reactivated <- avatar.reactivated + 1;
                admit t e.step))
            entries;
          List.iter
            (fun id ->
              let component = Tbl.Int.find avatar.components id in
              emit t component.clause (Component id))
            (Avatar.missing_components avatar changed))
  done

let protect f = try f () with Stop -> ()

let insert_axiom ?(releasable = false) t a =
  protect (fun () ->
      t.calculus.guard <- (fun () -> check_time t);
      check_time t;
      if List.exists (fun x -> x.axiom_id = a.axiom_id) t.axioms then
        invalid_arg "Engine: duplicate axiom id";
      t.axioms <- t.axioms @ [ a ];
      if releasable then Hashtbl.replace t.releasable a.axiom_id ();
      let cs =
        try
          Telemetry.with_stage t.timing "clausification" (fun () ->
              Clausify.run ~guard:(fun () -> check_time t) ~mode:t.config.cnf_mode a)
        with Clausify.Limit -> stop t "clausification limit"
      in
      List.iteri (fun i c -> emit_unfolded t c (Input (a.axiom_id, i))) cs)

(* [Heuristic.loop.uniq_order]: the initial clauses enter in E's evaluation order, ascending
   Uniqweight with ties in input order (ProofStateInit), so that their ids, the evaluation order of
   the queues, are E's. *)
let uniq_order t =
  match t.config.strategy.heuristic with Some h -> h.loop.uniq_order | None -> false

(* [name_of]: the source formula of an item's clause, whose written form E's ties read
   ([config.e_text]). *)
let by_uniq_weight ?text ?name_of clause_of items =
  let items = Array.of_list items in
  let names = Option.map (fun f -> Array.to_list (Array.map f items)) name_of in
  E_initial.order ?text ?names (Array.to_list (Array.map clause_of items))
  |> List.map (fun i -> items.(i))

(* [add_axiom] for every initial axiom at once, their clauses in Uniqweight order. *)
let insert_uniq_order t axioms =
  t.finished <- None;
  t.busy <- true;
  Fun.protect
    ~finally:(fun () -> t.busy <- false)
    (fun () ->
      protect (fun () ->
          t.calculus.guard <- (fun () -> check_time t);
          check_time t;
          let clauses =
            List.concat_map
              (fun (a : axiom) ->
                if List.exists (fun x -> x.axiom_id = a.axiom_id) t.axioms then
                  invalid_arg "Engine: duplicate axiom id";
                t.axioms <- t.axioms @ [ a ];
                let cs =
                  try
                    Telemetry.with_stage t.timing "clausification" (fun () ->
                        Clausify.run ~guard:(fun () -> check_time t) ~mode:t.config.cnf_mode a)
                  with Clausify.Limit -> stop t "clausification limit"
                in
                List.mapi (fun i c -> (a.axiom_id, i, c, a.name)) cs)
              axioms
          in
          List.iter
            (fun (id, i, c, _) -> emit_unfolded t c (Input (id, i)))
            (by_uniq_weight ?text:t.config.e_text
               ~name_of:(fun (_, _, _, name) -> Some name)
               (fun (_, _, c, _) -> c)
               clauses)))

(* EQ-UNIT needs the problem's least constant (instance rewriting, Demodulation.minimal) and the
   least weight of a ground term (Joinability.greater_in), both in the installed order. *)
let prepare_unit_equality t clauses =
  if
    unit_equality t
    && (t.config.eq_instances || t.config.eq_ground_joinable || t.config.eq_connected)
  then (
    let constants = Demodulation.constants_of clauses in
    Demodulation.set_minimal t.demodulator constants;
    Option.iter (fun e -> Demodulation.set_minimal e constants) t.equations;
    t.least_weight <- Joinability.least_weight t.order constants)

(* The SInE levels of the initial axioms, for a lean strategy whose queues read them. *)
let prepare_levels t (axioms : axiom list) =
  match t.config.strategy.heuristic with
  | Some h when Evaluation.uses_levels h.queues ->
      let clauses a = try Clausify.run ~mode:t.config.cnf_mode a with Clausify.Limit -> [] in
      t.sine <-
        Sine_levels.compute
          (List.map
             (fun (a : axiom) -> (a.axiom_id, clauses a, List.mem a.name t.config.goal_names))
             axioms)
  | _ -> ()

(* A strategy precedence is computed once from the initial axioms' clauses,
   before any of them is inserted. The production order needs no table. *)
(* E's pos_rank precedence tie-breaker over E's canonized input when the problem text gives E's
   symbol codes and written clauses ([config.e_text]), for the E-instance members
   ([Eorder.t.e_ranks]); [None] keeps the ranks over the clauses as they come. *)
let e_pos_ranks t (h : Heuristic.t) ?(names = fun () -> None) clauses =
  (* [Heuristic.loop.gen_order] reads E's symbol codes in its FP7 keys, [lit_order] in E's literal
     order. *)
  if h.loop.e_calculus && (h.loop.gen_order || h.loop.lit_order) then (
    let codes = E_initial.codes ?text:t.config.e_text clauses in
    let fallback key = (1 lsl 30) + (Hashtbl.hash key land 0xffff) in
    t.e_codes <-
      Some
        (fun ((head, _) as key) ->
          let c =
            match head with
            | Ordering.Function f -> codes.symbol (E_initial.symbol_name f)
            | Ordering.Predicate p -> codes.symbol p
            | Ordering.Definition (a, i) -> codes.symbol (Printf.sprintf "def%d_%d" a i)
            | Ordering.Truth -> codes.truth
          in
          if c = max_int then fallback key else c);
    if h.loop.lit_order then t.calculus.e_code <- t.e_codes);
  (* [names] is only computed here, so that every other strategy allocates as before (a lane's
     first slice is cut by the allocation clock). *)
  match t.config.e_text with
  | Some text when h.order.e_ranks -> Some (E_initial.pos_ranks ~text ?names:(names ()) clauses)
  | _ -> None

let prepare_ordering t axioms =
  prepare_levels t axioms;
  let install weights =
    Ordering.install t.order ~weights
      (List.concat_map
         (fun a -> try Clausify.run ~mode:t.config.cnf_mode a with Clausify.Limit -> [])
         axioms)
  in
  match t.config.strategy.heuristic with
  | Some { vampire = Some v; _ } ->
      (* A Vampire slice: its precedence, weights and literal order from the input clauses. *)
      let clauses a = try Clausify.run ~mode:t.config.cnf_mode a with Clausify.Limit -> [] in
      let goals = List.filter (fun (a : axiom) -> List.mem a.name t.config.goal_names) axioms in
      t.conjecture <-
        (if goals = [] then None
         else Some (Evaluation.conjecture_symbols (List.concat_map clauses goals)));
      let tagged =
        List.concat_map
          (fun (a : axiom) ->
            let goal = List.mem a.name t.config.goal_names in
            List.map (fun c -> (c, goal)) (clauses a))
          axioms
      in
      let goal = Array.of_list (List.map snd tagged) in
      Vampire.install ~goals:(fun i -> goal.(i)) v t.order (List.map fst tagged)
  | Some h ->
      (* A ported E heuristic: its E precedence and weights, and the symbols of the
         negated-conjecture axioms named by [goal_names]. *)
      let clauses a = try Clausify.run ~mode:t.config.cnf_mode a with Clausify.Limit -> [] in
      let goals = List.filter (fun (a : axiom) -> List.mem a.name t.config.goal_names) axioms in
      t.conjecture <-
        (if goals = [] then None
         else Some (Evaluation.conjecture_symbols (List.concat_map clauses goals)));
      let initial = List.concat_map clauses axioms in
      let others =
        List.filter (fun (a : axiom) -> not (List.mem a.name t.config.goal_names)) axioms
      in
      let axiom = Evaluation.conjecture_symbols (List.concat_map clauses others) in
      if Evaluation.uses_relevance h.queues then
        t.relevance <-
          Some
            (Evaluation.relevance_levels ~goals:(List.concat_map clauses goals)
               ~others:(List.concat_map clauses others));
      let ranks =
        e_pos_ranks t h
          ~names:(fun () ->
            Some
              (List.concat_map
                 (fun (a : axiom) -> List.map (fun _ -> Some a.name) (clauses a))
                 axioms))
          initial
      in
      let violations =
        Eorder.install ?conjecture:t.conjecture ~axiom ?ranks h.order t.order initial
      in
      t.order_violations <- List.length violations;
      prepare_unit_equality t initial
  | None -> (
      match t.config.strategy.precedence with
      | Strategy.Alphabetical -> ()
      | Invfreq -> install true
      | E_instance e ->
          let clauses a = try Clausify.run ~mode:t.config.cnf_mode a with Clausify.Limit -> [] in
          t.order_violations <-
            List.length (Eorder.install e t.order (List.concat_map clauses axioms)))

(* [releasable] lets the memory budget withdraw the axiom's Passive input
   clauses; the caller must then drain [released] and add the axiom again (with
   a fresh id) later. Only an injector that can do so may set it. *)
let add_axiom ?releasable t a =
  t.finished <- None;
  t.busy <- true;
  Fun.protect ~finally:(fun () -> t.busy <- false) (fun () -> insert_axiom ?releasable t a)

(* [prepare_ordering] on clauses already computed: the unfolded initial clauses, and the
   conjecture clauses when some axiom is a negated conjecture. *)
let install_order ?(others = []) ?(names = fun () -> None) t ~clauses ~goals =
  match t.config.strategy.heuristic with
  | Some { vampire = Some v; _ } ->
      t.conjecture <- Option.map Evaluation.conjecture_symbols goals;
      Vampire.install v t.order clauses
  | Some h ->
      t.conjecture <- Option.map Evaluation.conjecture_symbols goals;
      let axiom = Evaluation.conjecture_symbols (if goals = None then clauses else others) in
      if Evaluation.uses_relevance h.queues then
        t.relevance <-
          Some
            (Evaluation.relevance_levels ~goals:(Option.value ~default:[] goals)
               ~others:(if goals = None then clauses else others));
      let ranks = e_pos_ranks t h ~names clauses in
      let violations =
        Eorder.install ?conjecture:t.conjecture ~axiom ?ranks h.order t.order clauses
      in
      t.order_violations <- List.length violations;
      prepare_unit_equality t clauses
  | None -> (
      match t.config.strategy.precedence with
      | Strategy.Alphabetical -> ()
      | Invfreq -> Ordering.install t.order ~weights:true clauses
      | E_instance e -> t.order_violations <- List.length (Eorder.install e t.order clauses))

(** Diagnostics hook (the CLI's AXIOM_EQ_UNFOLD_REPORT): receives one line from every engine whose
    strategy enables equational-definition unfolding, after it planned the unfolding. *)
let unfold_report : (string -> unit) ref = ref (fun _ -> ())

let report_unfold t summary =
  t.unfold_summary <- Some summary;
  !unfold_report (Printf.sprintf "eq-unfold: strategy=%s %s" t.config.strategy.name summary)

let insert_unfolded t axioms positions (plan : Unfold.plan) =
  protect (fun () ->
      t.calculus.guard <- (fun () -> check_time t);
      check_time t;
      prepare_levels t axioms;
      List.iter
        (fun (a : axiom) ->
          if List.exists (fun x -> x.axiom_id = a.axiom_id) t.axioms then
            invalid_arg "Engine: duplicate axiom id";
          t.axioms <- t.axioms @ [ a ])
        axioms;
      let positions = Array.of_list positions in
      let removed = Array.make (Array.length positions) false in
      List.iter (fun (p, _) -> removed.(p) <- true) plan.removed;
      let goal p =
        let (a : axiom), _, _ = positions.(p) in
        List.mem a.name t.config.goal_names
      in
      let kept f =
        List.concat
          (List.mapi
             (fun p c -> if (not removed.(p)) && f p then [ c ] else [])
             (Array.to_list plan.clauses))
      in
      let goals =
        if List.exists (fun (a : axiom) -> List.mem a.name t.config.goal_names) axioms then
          Some (kept (fun p -> goal p || plan.conjecture.(p)))
        else None
      in
      install_order t
        ~names:(fun () ->
          Some
            (List.concat
               (List.mapi
                  (fun p _ ->
                    if removed.(p) then []
                    else
                      let (a : axiom), _, _ = positions.(p) in
                      [ Some a.name ])
                  (Array.to_list plan.clauses))))
        ~clauses:(kept (fun _ -> true))
        ~goals
        ~others:(kept (fun p -> not (goal p || plan.conjecture.(p))));
      (* The removed definitions, in removal order, each through the ones removed before it. *)
      List.iter
        (fun (p, d) ->
          let (a : axiom), i, clause = positions.(p) in
          let step = through t t.unfolded (record t clause (Input (a.axiom_id, i))) in
          match Unfold.source step d with
          | Some source -> t.unfolded <- t.unfolded @ [ source ]
          | None ->
              (* Not reached: the plan tested the same clause. Keep it searchable. *)
              emit t step.clause step.rule)
        plan.removed;
      let kept =
        List.filter (fun p -> not removed.(p)) (List.init (Array.length positions) Fun.id)
      in
      (* E orders the clauses after its preprocessing: by their unfolded forms. *)
      let kept =
        if uniq_order t then
          by_uniq_weight ?text:t.config.e_text
            ~name_of:(fun p ->
              let (a : axiom), _, _ = positions.(p) in
              Some a.name)
            (fun p -> plan.clauses.(p))
            kept
        else kept
      in
      List.iter
        (fun p ->
          let (a : axiom), i, clause = positions.(p) in
          emit_unfolded t clause (Input (a.axiom_id, i)))
        kept)

(* [Heuristic.sine_filter]: the axioms E's SInE keeps (an evaluation member only; a search that
   uses only some axioms still refutes the whole input, it may only miss a refutation). *)

(* A Vampire slice member's initial clauses (Vampire.preprocess): function definitions removed
   (unused ones, or all of them unfolded, through Unfold's certificate path), the remaining
   definitions first, the ordering counted on the preprocessed clauses and its SInE levels on the
   input. Equality resolution with deletion happens at admission ([destructive_er]). *)
let vampire_initial t v (axioms : axiom list) =
  let limited = ref false in
  let positions =
    try
      List.concat_map
        (fun (a : axiom) ->
          List.mapi (fun i c -> (a, i, c)) (Clausify.run ~mode:t.config.cnf_mode a))
        axioms
    with Clausify.Limit ->
      limited := true;
      []
  in
  let pa = Array.of_list positions in
  let goal p =
    let (a : axiom), _, _ = pa.(p) in
    List.mem a.name t.config.goal_names
  in
  let clauses = List.map (fun (_, _, c) -> c) positions in
  let pre = Vampire.preprocess v clauses in
  t.finished <- None;
  t.busy <- true;
  Fun.protect
    ~finally:(fun () -> t.busy <- false)
    (fun () ->
      protect (fun () ->
          t.calculus.guard <- (fun () -> check_time t);
          check_time t;
          if !limited then stop t "clausification limit";
          List.iter
            (fun (a : axiom) ->
              if List.exists (fun x -> x.axiom_id = a.axiom_id) t.axioms then
                invalid_arg "Engine: duplicate axiom id";
              t.axioms <- t.axioms @ [ a ])
            axioms;
          let goals = List.filteri (fun p _ -> goal p) clauses in
          t.conjecture <- (if goals = [] then None else Some (Evaluation.conjecture_symbols goals));
          Vampire.install ~goals:goal ~counted:pre.counted
            ~ids:
              (match t.config.vampire_symbols with
              | Some ids -> ids
              | None -> Vampire.parse_order (List.map (fun (a : axiom) -> a.formula) axioms))
            v t.order clauses;
          (match pre.plan with
          | None -> ()
          | Some plan ->
              report_unfold t
                (Printf.sprintf "vampire-fde definitions=%d rewritten=%d steps=%d symbols=%s"
                   (List.length plan.removed) plan.rewritten plan.steps
                   (String.concat "," (List.map (fun (_, d) -> Unfold.describe d) plan.removed)));
              List.iter
                (fun (p, d) ->
                  let (a : axiom), i, clause = pa.(p) in
                  let step = through t t.unfolded (record t clause (Input (a.axiom_id, i))) in
                  match Unfold.source step d with
                  | Some source -> t.unfolded <- t.unfolded @ [ source ]
                  | None ->
                      t.vampire_input <- Some (goal p);
                      emit t step.clause step.rule)
                plan.removed);
          (* SaturationAlgorithm::init: set-of-support clauses go to Active at once, in order;
             the others onto the new-clause stack, which is processed last to first. *)
          t.vampire_total <- Array.length pa;
          let sos p = v.sos && not (goal p) in
          let insert p =
            let (a : axiom), i, clause = pa.(p) in
            t.vampire_input <- Some (goal p);
            t.vampire_position <- Some p;
            emit_unfolded t clause (Input (a.axiom_id, i))
          in
          List.iter (fun p -> if sos p then insert p) pre.order;
          List.iter (fun p -> if not (sos p) then insert p) (List.rev pre.order)))

(** The initial axioms of a search, in order: [prepare_ordering], then [add_axiom] for each. When
    the strategy sets [unfold], E's equational-definition unfolding ([Unfold]) runs first over all
    their clauses: a removed definition and the input node of a rewritten clause become proof
    ancestors that the search does not see, each rewritten clause enters as its last paramodulation
    step, and the term ordering and conjecture symbols come from the unfolded clauses (E computes
    them after its preprocessing). With nothing to unfold this is exactly the plain sequence. *)
let sine_filtered t (axioms : axiom list) =
  match t.config.strategy.heuristic with
  | Some { sine_filter = Some (tolerance, depth); _ } -> (
      let clauses a = try Clausify.run ~mode:t.config.cnf_mode a with Clausify.Limit -> [] in
      match
        Sine_levels.compute
          ~params:{ Sine_levels.tolerance; generality = 0 }
          (List.map
             (fun (a : axiom) -> (a.axiom_id, clauses a, List.mem a.name t.config.goal_names))
             axioms)
      with
      | None -> axioms
      | Some levels ->
          List.filter (fun (a : axiom) -> Sine_levels.level levels a.axiom_id <= depth) axioms)
  | _ -> axioms

let rec add_initial_axioms t axioms =
  t.inserting_initial <- true;
  let axioms = sine_filtered t axioms in
  Fun.protect
    ~finally:(fun () -> t.inserting_initial <- false)
    (fun () -> add_initial_axioms_now t axioms)

and add_initial_axioms_now t axioms =
  t.presat_running <- presat_strategy t.config.strategy;
  let plain () =
    prepare_ordering t axioms;
    if uniq_order t then insert_uniq_order t axioms else List.iter (add_axiom t) axioms
  in
  match (vampire t, t.config.strategy.unfold) with
  | Some v, _ -> vampire_initial t v axioms
  | None, unfold -> (
      match unfold with
      | None -> plain ()
      | Some limit -> (
          let positions =
            try
              Some
                (List.concat_map
                   (fun (a : axiom) ->
                     List.mapi (fun i c -> (a, i, c)) (Clausify.run ~mode:t.config.cnf_mode a))
                   axioms)
            with Clausify.Limit -> None
          in
          let plan =
            match positions with
            | None -> None
            | Some positions -> (
                let goals =
                  Array.of_list
                    (List.map
                       (fun ((a : axiom), _, _) -> List.mem a.name t.config.goal_names)
                       positions)
                in
                (* [Heuristic.loop.uniq_order]: E looks for definitions in its canonical clause
                   order, which E's view of the problem text decides ([config.e_text]). *)
                let order =
                  match t.config.e_text with
                  | Some text when uniq_order t ->
                      Some
                        (E_initial.canonical_order ~text
                           ~names:(List.map (fun ((a : axiom), _, _) -> Some a.name) positions)
                           (List.map (fun (_, _, c) -> c) positions))
                  | _ -> None
                in
                try
                  Unfold.plan
                    ~guard:(fun () -> check_time t)
                    ~goal:(fun p -> goals.(p))
                    ?order ~limit
                    (List.map (fun (_, _, c) -> c) positions)
                with Stop -> None)
          in
          match (positions, plan) with
          | Some positions, Some plan ->
              report_unfold t
                (Printf.sprintf "definitions=%d rewritten=%d steps=%d symbols=%s"
                   (List.length plan.removed) plan.rewritten plan.steps
                   (String.concat "," (List.map (fun (_, d) -> Unfold.describe d) plan.removed)));
              t.finished <- None;
              t.busy <- true;
              Fun.protect
                ~finally:(fun () -> t.busy <- false)
                (fun () -> insert_unfolded t axioms positions plan)
          | _ ->
              report_unfold t "definitions=0";
              plain ()))

(* The replacement of an active clause that [using] rewrote. *)
let backward_replace t (using : Demodulation.rewrite) (s : step) changed rule =
  (* Remove the old target before simplification: it must not subsume
     its replacement. Its proof node remains available to replay. *)
  ignore (reduce t ~target:s.id ~using:using.parent);
  (* [Heuristic.loop.discount]: the retired clause is dead, so its Passive
     conclusions become orphans. With [Heuristic.loop.orphans] its replacement is
     not one: E replaces a backward-simplified processed clause by a fresh copy
     (ClauseMoveSimplified, whose ClauseArchive derivation is no generating
     inference) and never deletes it as an orphan. Inheriting the target's origins
     would drop such replacements of active clauses. The DISCOUNT workers that delete
     no orphans keep the inheritance, which nothing reads there, so that their
     allocation, and with it the work clock, stays the same ([origins]). *)
  if discount_strategy t.config.strategy then (
    Tbl.Int.replace t.dead s.id ();
    t.origin_next <-
      Some
        (if orphans_strategy t.config.strategy then []
         else Option.value ~default:[] (Tbl.Int.find_opt t.origins s.id)));
  t.metrics.backward_demodulated <- t.metrics.backward_demodulated + 1;
  t.metrics.demodulated <- t.metrics.demodulated + 1;
  t.mark_processed <- true;
  (* E rewrites a backward-rewritten clause with FullRewrite again before it
     re-enters (insert_new_clauses, CPIsIRVictim). *)
  t.full_next <- full_rewrite_strategy t.config.strategy;
  t.vampire_simplified <- Some s.id;
  emit t changed rule

(* [Heuristic.loop.gen_order]: E's order of the copies it moves to tmp_store
   (cco_simplification.c RemoveRewritableClausesIndexed): it collects the victims leaf by leaf of
   its FP7 index in visit order (FPIndexFindMatchable, popped, each leaf's clauses pushed), then
   pops them, so the leaves come in visit order and the newest victim of a leaf first. The copies
   are created, and evaluated, in that order. A replacement never simplifies another active clause
   here (DISCOUNT), so the rewrites can be computed first. *)
let backward_demodulate_e_order t (using : Demodulation.rewrite) targets =
  let code = match t.e_codes with Some c -> c | None -> fun k -> Hashtbl.hash k land 0xffff in
  let found =
    List.filter_map
      (fun (s : step) ->
        check_time t;
        if not (Index.mem t.index s.id) then None
        else
          match
            Demodulation.rewrite_once ~using ~guard:(fun () -> check_time t) t.demodulator s
          with
          | None -> None
          | Some ((_, rule) as result) ->
              let leaf =
                match rule with
                | Paramodulate (_, _, _, _, j, path, _) ->
                    E_genorder.leaf_key code (E_genorder.Term using.lhs)
                      (E_genorder.path_subject (List.nth s.clause j) path)
                | _ -> []
              in
              Some ((List.map (fun k -> -k) leaf, -s.id), (s, result)))
      targets
  in
  List.iter
    (fun (_, (s, (changed, rule))) -> backward_replace t using s changed rule)
    (List.stable_sort (fun (a, _) (b, _) -> compare a b) found)

let backward_demodulate t (using : Demodulation.rewrite) =
  Telemetry.with_stage t.timing "demodulation" (fun () ->
      let targets =
        if t.config.equality_indexed then
          Equality_index.rewrite_targets ~guard:(fun () -> check_time t) t.equality_index using.lhs
        else Index.all t.index
      in
      let targets =
        List.filter (fun (s : step) -> s.id <> using.parent) targets
        |> List.sort (fun (a : step) b -> compare a.id b.id)
      in
      t.metrics.backward_demodulation_candidates <-
        t.metrics.backward_demodulation_candidates + List.length targets;
      t.metrics.backward_demodulation_baseline <-
        t.metrics.backward_demodulation_baseline + max 0 (Tbl.Int.length t.index.live - 1);
      if gen_order_strategy t.config.strategy then backward_demodulate_e_order t using targets
      else
        List.iter
          (fun (s : step) ->
            check_time t;
            if Index.mem t.index s.id then
              match
                Demodulation.rewrite_once ~using ~guard:(fun () -> check_time t) t.demodulator s
              with
              | None -> ()
              | Some (changed, rule) -> backward_replace t using s changed rule)
          targets)

let activate t given =
  index_active t given;
  (if backward_strategy t.config.strategy then
     let table =
       match t.activations with
       | Some table -> table
       | None ->
           let table = Tbl.Int.create 64 in
           t.activations <- Some table;
           table
     in
     Tbl.Int.replace table given.id (Tbl.Int.length table));
  (* DISCOUNT: an active clause joins the Contraction (Passive clauses simplify nothing). *)
  if t.config.subsumption && discount_strategy t.config.strategy then
    Contraction.add t.contraction given;
  if t.presat_running then t.presat_active <- given.id :: t.presat_active;
  observe t "active" given;
  if t.config.lookahead > 0 && List.length given.clause > 1 then
    Directions.register t.directions ~epoch:t.index.generation
      (given.id, Tbl.Int.find t.retained_index.live given.id);
  t.on_active given;
  if
    t.config.backward_demodulation
    && match vampire t with Some v -> v.backward_demodulation | None -> true
  then
    let rules = Demodulation.orient_all t.demodulator given in
    (* E collects the victims of an unorientable unit's lterm pass, then of its rterm pass, on one
       stack, so the rterm pass's victims come out first. *)
    List.iter (backward_demodulate t)
      (if gen_order_strategy t.config.strategy then List.rev rules else rules)

(* Unit resulting resolution (urr=on, URResolution::generateClauses), item by item as
   URResolution keeps them. An item is the clause's literal array (Vampire's order: the selected
   literals first), the resolved slots emptied; [processLiteral] at position [idx] moves the best
   remaining literal there (getBestLiteralReady: the greatest weight minus distinct variables, the
   first on ties, by swapping), adds a copy that keeps that literal (unless all must go) and one
   item per unifying active unit, in that order, and drops the item. Not "full": when the item has
   at most one non-ground unresolved literal (counted before this resolution, the kept one
   included), the first unifier is enough. After the last position every item left yields its
   single remaining literal or the empty clause, in list order. A unit given also starts from the
   active non-unit clauses it resolves with (doBackwardInferences: the resolved literal is swapped
   to the front first). A result is certified as a chain of ordinary binary resolutions with the
   units; the intermediate clauses are proof-only nodes, the last one is emitted. *)
let urr_generate t (given : step) =
  match vampire t with
  | Some { unit_resulting = true; _ } ->
      let active id = Index.mem t.index id in
      let complement (l : literal) = { l with positive = not l.positive } in
      let units_for (l : literal) =
        Option.value ~default:[] (Hashtbl.find_opt t.urr_units (Clause.key (complement l)))
        |> List.filter active |> List.rev
      in
      let goodness (l : literal) = Vampire.literal_weight l - List.length (Wire.variables [ l ]) in
      let ground (l : literal) = Wire.variables [ l ] = [] in
      let nonground lits =
        Array.fold_left (fun n -> function Some l when not (ground l) -> n + 1 | _ -> n) 0 lits
      in
      (* Vampire's literal array of an active clause: the selected literals first. *)
      let vampire_order (s : step) clause =
        match Calculus.selected t.calculus s with
        | Some (_ :: _ as chosen) ->
            List.filteri (fun i _ -> List.mem i chosen) clause
            @ List.filteri (fun i _ -> not (List.mem i chosen)) clause
        | _ -> clause
      in
      let remaining lits = Array.to_list lits |> List.filter_map Fun.id in
      (* An item: the literal array, whether every literal must be resolved, the at-most-one
         non-ground flag, and the resolutions so far (unit id, the clause after it), newest first. *)
      let process items idx =
        List.concat_map
          (fun (lits, must, one, steps) ->
            check_time t;
            let lits = Array.copy lits in
            let n = Array.length lits in
            if n - idx > 1 then (
              let best = ref idx and value = ref (goodness (Option.get lits.(idx))) in
              for i = idx + 1 to n - 1 do
                let v = goodness (Option.get lits.(i)) in
                if v > !value then (
                  best := i;
                  value := v)
              done;
              if !best <> idx then (
                let x = lits.(idx) in
                lits.(idx) <- lits.(!best);
                lits.(!best) <- x));
            let lit = Option.get lits.(idx) in
            let keep = if must then [] else [ (lits, true, one, steps) ] in
            let scope = 2 + List.length steps in
            let exception Enough of (literal option array * bool * bool * (int * clause) list) list
              in
            let resolved =
              try
                List.fold_left
                  (fun acc uid ->
                    let u = List.hd (Clause.scope scope (Proof.get t.proof uid).clause) in
                    List.fold_left
                      (fun acc sigma ->
                        let ap = Clause.map_literal (Vampire.apply sigma) in
                        let lits' = Array.map (Option.map ap) lits in
                        lits'.(idx) <- None;
                        let one' = one || nonground lits' <= 1 in
                        let acc = (lits', must, one', (uid, remaining lits') :: steps) :: acc in
                        if one then raise (Enough acc) else acc)
                      acc
                      (Vampire.complementary_unifiers lit u))
                  [] (units_for lit)
                |> List.rev
              with Enough acc -> List.rev acc
            in
            keep @ resolved)
          items
      in
      let run items start n =
        let rec go items idx =
          if items = [] || idx >= n then items else go (process items idx) (idx + 1)
        in
        go items start
      in
      let replay (start : step) chain =
        (* [chain]: (unit id, expected clause after the resolution), oldest first. *)
        let rec go (current : step) = function
          | [] -> ()
          | (uid, expected) :: more -> (
              let xs = Clause.scope 1 current.clause in
              let u = List.hd (Clause.scope 2 (Proof.get t.proof uid).clause) in
              let target = Clause.normalize expected in
              let found =
                List.find_map
                  (fun (i, l) ->
                    List.find_map
                      (fun sigma ->
                        let resolvent =
                          List.map (Clause.map_literal (Vampire.apply sigma)) (Clause.remove i xs)
                        in
                        if Clause.normalize resolvent = target then
                          Some (resolvent, Resolve (current.id, i, uid, 0, sigma))
                        else None)
                      (Vampire.complementary_unifiers l u))
                  (List.mapi (fun i l -> (i, l)) xs)
              in
              match found with
              | None -> ()
              | Some (clause, rule) ->
                  if more = [] then emit t clause rule
                  else
                    let step = record t clause rule in
                    (* The chain's clause ages and goal flags, so the result's are Vampire's. *)
                    let age id = Option.value ~default:0 (Hashtbl.find_opt t.vampire_ages id) in
                    Hashtbl.replace t.vampire_ages step.id (max (age current.id) (age uid));
                    if Hashtbl.mem t.vampire_goals current.id || Hashtbl.mem t.vampire_goals uid
                    then Hashtbl.replace t.vampire_goals step.id ();
                    go step more)
        in
        go start chain
      in
      let xs =
        Array.of_list (List.map Option.some (Clause.scope 1 (vampire_order given given.clause)))
      in
      let forward =
        run [ (xs, Array.length xs < 2, nonground xs <= 1, []) ] 0 (Array.length xs)
        |> List.filter_map (fun (_, _, _, steps) ->
            if steps = [] then None else Some (given, steps))
      in
      let backward =
        match given.clause with
        | [ g ] ->
            let key = Clause.key (complement g) in
            let gl = List.hd (Clause.scope 2 given.clause) in
            Option.value ~default:[] (Hashtbl.find_opt t.urr_nonunits key)
            |> List.filter (fun id -> id <> given.id && active id)
            |> List.rev
            |> List.concat_map (fun did ->
                let d = Proof.get t.proof did in
                let ys =
                  Array.of_list (List.map Option.some (Clause.scope 1 (vampire_order d d.clause)))
                in
                let one = nonground ys <= 1 in
                List.concat
                  (List.mapi
                     (fun pos l ->
                       List.concat_map
                         (fun sigma ->
                           let lits = Array.copy ys in
                           let x = lits.(0) in
                           lits.(0) <- lits.(pos);
                           lits.(pos) <- x;
                           let ap = Clause.map_literal (Vampire.apply sigma) in
                           let lits = Array.map (Option.map ap) lits in
                           lits.(0) <- None;
                           let one' = one || nonground lits <= 1 in
                           run
                             [ (lits, false, one', [ (given.id, remaining lits) ]) ]
                             1 (Array.length lits)
                           |> List.map (fun (_, _, _, steps) -> (d, steps)))
                         (Vampire.complementary_unifiers (Option.get l) gl))
                     (Array.to_list ys)))
        | _ -> []
      in
      (* Vampire creates the clauses (and numbers them) in this order and adds them to its new
         clauses newest first (generateClauses pushes them on a list). *)
      let results = forward @ backward in
      let base = t.vampire_count in
      t.vampire_count <- base + List.length results;
      List.rev (List.mapi (fun i r -> (base + 1 + i, r)) results)
      |> List.iter (fun (number, ((start : step), steps)) ->
          t.vampire_number <- Some number;
          replay start (List.rev steps);
          t.vampire_number <- None)
  | _ -> ()

(* LookaheadLiteralSelector::doSelection for a Vampire slice with selection 11 or 1011, at
   activation: among the candidate literals (11: the literals negative for selection, and the unique
   maximal literal when it is positive; 1011: all), one per variant class, the one with the fewest
   inferences with the Active clauses (resolution partners in the inference index, superposition
   partners in the equality index, its own equality resolution), ties broken as pickTheBest. The
   partner counts are the indexes' candidates after their prefilters, not full unifications. *)
let vampire_lookahead t (v : Vampire.t) (given : step) =
  let xs = Array.of_list given.clause in
  let n = Array.length xs in
  let all = List.init n Fun.id in
  let greater i j = Ordering.literal_greater ~order:t.order xs.(i) xs.(j) in
  let maximal = List.filter (fun i -> not (List.exists (fun j -> j <> i && greater j i) all)) all in
  let negative i = Vampire.negative_for_selection v xs.(i) in
  let complete = abs v.selection = 11 in
  let remove_variants ids =
    List.fold_left
      (fun kept i ->
        if List.exists (fun j -> Clause.normalize [ xs.(j) ] = Clause.normalize [ xs.(i) ]) kept
        then kept
        else kept @ [ i ])
      [] ids
  in
  let negatives = List.filter negative all in
  if n <= 1 then all
  else if complete && negatives = [] then maximal
  else
    let candidates =
      if complete then
        remove_variants negatives
        @ match maximal with [ m ] when not (negative m) -> [ m ] | _ -> []
      else remove_variants all
    in
    match candidates with
    | [ i ] -> [ i ]
    | _ ->
        let count i =
          let l = xs.(i) in
          let fp = if t.index.fingerprint then Index.Fingerprint.atom l.atom else [||] in
          let resolution =
            List.fold_left
              (fun k (p : Index.posting) ->
                if
                  Index.live p && p.step.id <> given.id
                  && Index.fingerprint_matches t.index l.atom fp p
                  && Index.atoms l.atom p.value
                then k + 1
                else k)
              0 (Index.bucket t.index l)
          in
          let superposition =
            Seq.fold_left
              (fun k -> function Some (other, _, _) when other.id <> given.id -> k + 1 | _ -> k)
              0
              (Equality_index.cursor
                 ~eligible:(fun j -> j = i)
                 ~guard:(fun () -> check_time t)
                 t.equality_index ~variables:t.config.variable_positions given.clause)
          in
          let resolution_self =
            match (l.positive, l.atom) with
            | false, E (s, u) -> if Vampire.unify [ (s, u) ] <> None then 1 else 0
            | _ -> 0
          in
          resolution + superposition + resolution_self
        in
        let id key =
          match t.order.vampire with
          | Some o -> Option.value ~default:max_int (Hashtbl.find_opt o.ids key)
          | None -> 0
        in
        let counted = List.map (fun i -> (i, count i)) candidates in
        let least = List.fold_left (fun m (_, k) -> min m k) max_int counted in
        let best =
          List.fold_left
            (fun b (i, k) ->
              if k <> least then b
              else
                match b with
                | Some j when Vampire.lookahead_tie ~id xs.(j) xs.(i) >= 0 -> b
                | _ -> Some i)
            None counted
        in
        [ Option.get best ]

let select_literal t (given : step) emit =
  (match vampire t with
  | Some v when Vampire.lookahead v ->
      Tbl.Int.replace t.calculus.selected given.id (Some (vampire_lookahead t v given))
  | _ -> ());
  if t.config.lookahead > 0 && List.length given.clause > 1 then
    Directions.register t.directions ~epoch:t.index.generation
      (given.id, Tbl.Int.find t.retained_index.live given.id);
  let lookahead ?default () =
    Index.lookahead
      ~guard:(fun () -> check_time t)
      ~order:t.order ?default t.index ~budget:t.config.lookahead given.clause
  in
  let revised =
    if t.config.lookahead = 0 then None
    else
      match t.config.strategy.selection with
      | Strategy.First_negative -> Some (lookahead ())
      | Max_complex_avoid_pos_pred_lookahead -> (
          (* Only a negative selection is revised; no selection stays none. *)
          match Calculus.default_selection t.calculus given with
          | Some [ i ] -> Some (lookahead ~default:(Some i) ())
          | _ -> None)
      | Max_complex_avoid_pos_pred | Max_complex | Vampire_best_10 -> None
  in
  Option.iter
    (fun (selected, work, exhausted) ->
      t.metrics.lookahead_postings <- t.metrics.lookahead_postings + work;
      t.metrics.lookahead_exhausted <- t.metrics.lookahead_exhausted + exhausted;
      if selected <> Calculus.selected t.calculus given then (
        Tbl.Int.replace t.calculus.selected given.id selected;
        Goal_transfer.selection_changed t.transfer given.id;
        forget_work_owner t given.id;
        (match selected with
        | Some (_ :: _ :: _) -> t.metrics.positive_directions <- t.metrics.positive_directions + 1
        | _ -> ());
        t.metrics.lookahead_changed <- t.metrics.lookahead_changed + 1;
        (* Cover newly selected pivots, including a supplementary positive
           direction. Keep the choice fixed while the clause is active. *)
        Calculus.unary t.calculus given emit))
    revised

let prepare_inferences t given =
  (* A ticket is taken when its group is made. The lazy cursors yield only live postings, but a
     Vampire slice member's resolution partners are listed when the given's work is prepared
     ([vampire_partners]), and a listed partner can leave the retained index before its group is
     made: between the work's quanta an AVATAR model change disables it, or the given's own
     activation retires it by backward simplification. It then gets a stale ticket (no generation
     is negative), so Directions.advance cancels its group, as the cursor skips a dead posting. *)
  let ticket (s : step) =
    (s.id, match Tbl.Int.find t.retained_index.live s.id with g -> g | exception Not_found -> -1)
  in
  let work =
    Directions.prepare
      ~unit_retained:(not (Calculus.e_calculus t.calculus))
      ~guard:(fun () -> check_time t)
      ~calculus:t.calculus ~index:t.index
      ~retained:
        (* A unit given resolves with Passive clauses too; Vampire's generating inferences use
           Active clauses only. *)
        (if vampire t <> None then t.index else t.retained_index)
      ~equalities:t.equality_index ~indexed:t.config.indexed
      ~equality_indexed:t.config.equality_indexed ~ticket
      ?partners:(if vampire t <> None then Some (vampire_partners t) else None)
      given
  in
  if vampire t = None then work
  else
    (* A Vampire slice's unary inferences come after its binary ones ([process_given]). *)
    let unary =
      {
        Directions.parents = [ ticket given ];
        start = (fun () -> Seq.return (fun emit -> Calculus.unary t.calculus given emit));
      }
    in
    { work with groups = Seq.append work.groups (Seq.return unary) }

(* A conclusion of a generating inference: emitted now, or kept for [flush_batch]. *)
let emit_conclusion t clause rule =
  if t.config.eq_connected && unit_equality t then t.peak <- peak_of t clause rule;
  emit t clause rule

let conclude t clause rule =
  match t.e_batch with
  | Some batch -> t.e_batch <- Some ((clause, rule) :: batch)
  | None -> emit_conclusion t clause rule

(* [Heuristic.loop.sim_paramod]: a paramodulant as E's simultaneous one ({!E_simparamod.chain}),
   its intermediates recorded as proof-only nodes ([record]). The emitted clause keeps the
   inference's premises as its origin (E's orphan test) and has no EQ-UNIT peak. Returns the
   emitted conclusion when it replaced more than one occurrence. *)
let emit_simultaneous t clause rule =
  match rule with
  | Paramodulate (p, _, _, q, _, _, _) -> (
      match
        E_simparamod.chain ~record:(record t) ~from:(Proof.get t.proof p)
          ~into:(Proof.get t.proof q) clause rule
      with
      | Plain ->
          emit_conclusion t clause rule;
          None
      | Fallback recorded ->
          t.metrics.sim_fallbacks <- t.metrics.sim_fallbacks + 1;
          t.metrics.sim_steps <- t.metrics.sim_steps + recorded;
          emit_conclusion t clause rule;
          None
      | Simultaneous { clause; rule; steps } ->
          t.metrics.sim_paramodulants <- t.metrics.sim_paramodulants + 1;
          t.metrics.sim_steps <- t.metrics.sim_steps + steps;
          t.origin_next <- Some [ p; q ];
          emit t clause rule;
          Some (clause, rule, [ p; q ]))
  | _ ->
      emit_conclusion t clause rule;
      None

(* E's ParamodSim over a given clause's conclusions in E's creation order: with the given clause as
   the from clause, the first paramodulant per from position, into clause and into subterm (the
   rest are not made); with the given as the into clause, every one, the copies for further
   occurrences of the same subterm being the same clause. A paramodulant left plain (a fallback)
   replaced one occurrence only, so the other positions of its group still get theirs: dropping
   them would lose the replacements of the others. *)
let emit_simultaneous_batch t (given : step) sorted =
  (* Only paramodulants whose into subterm repeats enter these lists, so they are short. *)
  let made = ref [] and copies = ref [] in
  List.iter
    (fun (_, (clause, rule)) ->
      match rule with
      | Paramodulate (p, i, reverse, q, j, path, _) -> (
          let into = (Proof.get t.proof q).clause in
          let s = Clause.at (List.nth into j) path in
          (* A subterm that occurs once is replaced once, and no other position shares it. *)
          if not (E_simparamod.repeated s into) then emit_conclusion t clause rule
          else if p = given.id then (
            let key = (i, reverse, q, s) in
            if List.mem key !made then t.metrics.sim_merged <- t.metrics.sim_merged + 1
            else if Option.is_some (emit_simultaneous t clause rule) then made := key :: !made)
          else
            let key = (p, i, reverse, s) in
            match List.assoc_opt key !copies with
            | Some (clause, rule, origin) ->
                t.origin_next <- Some origin;
                emit t clause rule
            | None ->
                Option.iter
                  (fun made -> copies := (key, made) :: !copies)
                  (emit_simultaneous t clause rule))
      | _ -> emit_conclusion t clause rule)
    sorted

(* [Heuristic.loop.gen_order]: the given clause's conclusions in E's creation order
   ({!E_genorder.key}), equal keys in the order they were generated. *)
let flush_batch t (given : step) =
  match t.e_batch with
  | None -> ()
  | Some batch ->
      t.e_batch <- None;
      let code =
        match t.e_codes with
        | Some code -> code
        | None -> fun (h, a) -> Hashtbl.hash (h, a) land 0xffff
      in
      let rank = Option.map (fun code -> Eselection.e_rank ~code given.clause) t.calculus.e_code in
      let keyed =
        List.rev_map
          (fun ((_, rule) as c) ->
            (E_genorder.key ?rank ~order:t.order ~code ~get:(Proof.get t.proof) given rule, c))
          batch
      in
      let sorted = List.stable_sort (fun (a, _) (b, _) -> compare a b) keyed in
      let sorted =
        if top_once_strategy t.config.strategy then
          (* E's ComputeFromParamodulants: a partner's equation into the top of a positive literal
             of the given is the overlap the given made into that partner's top. *)
          List.filter
            (fun (_, (_, rule)) ->
              match rule with
              | Paramodulate (p, _, _, q, j, [ _ ], _) when q = given.id && p <> given.id -> (
                  match List.nth given.clause j with
                  | { positive = true; atom = E _ } ->
                      t.metrics.top_skipped <- t.metrics.top_skipped + 1;
                      false
                  | _ -> true)
              | _ -> true)
            sorted
        else sorted
      in
      if sim_paramod_strategy t.config.strategy then emit_simultaneous_batch t given sorted
      else List.iter (fun (_, (clause, rule)) -> emit_conclusion t clause rule) sorted

let advance_inference ?(quantum = 512) t work =
  let generated = t.metrics.generated in
  let emit = conclude t in
  Directions.advance ~quantum
    ~guard:(fun () -> check_time t)
    ~alive:(current_ticket t)
    ~yield:(fun () -> t.metrics.generated - generated >= 64 || t.avatar.dirty)
    ~cancelled:(fun () -> t.metrics.inference_cancelled <- t.metrics.inference_cancelled + 1)
    ~emit work

let process_inference t work =
  let id, _ = work.owner in
  trace_action t Producer_schedule.Trace.Process work.owner;
  let probing = not (Index.mem t.index id) in
  if probing then t.focus.probes <- t.focus.probes + 1;
  let started = cost_now () and generated = t.metrics.generated in
  let request =
    if (not (lean t)) && current_ticket t work.owner then (
      let step = Proof.get t.proof id in
      let previous = Work_table.find_opt t.transfer_work work in
      let request =
        Goal_transfer.request t.transfer ?previous ~support:(Avatar.dependency t.avatar id)
          work.owner step
      in
      Work_table.replace t.transfer_work work request;
      if Option.is_none previous then count_work_owner t id 1;
      Some request)
    else None
  in
  let complete = advance_inference ~quantum:(if probing then 128 else 512) t work in
  if complete then (
    if t.e_batch <> None then flush_batch t (Proof.get t.proof id);
    (* A Vampire slice member's activation has generated all of its clauses. *)
    if vampire t <> None then vampire_process_batch t;
    trace_action t Producer_schedule.Trace.Complete work.owner;
    Option.iter (Goal_transfer.complete_request t.transfer) request;
    if Work_table.mem t.transfer_work work then (
      Work_table.remove t.transfer_work work;
      count_work_owner t id (-1)));
  Focus.observe_batch t.focus id
    ~seconds:(cost_now () -. started)
    ~generated:(t.metrics.generated - generated);
  if current_ticket t work.owner then (
    let id, _ = work.owner in
    (* Publish a yielding given before selecting another one. Otherwise two
       suspended givens could miss their mutual inferences. *)
    if not (Index.mem t.index id) then (
      let given = Proof.get t.proof id in
      activate t given;
      (* A Vampire slice member splits when a clause enters Passive or is selected. *)
      if t.config.avatar && vampire t = None then
        Avatar.offer_split t.avatar ~guard:(fun () -> check_time t) given);
    if (not complete) && current_ticket t work.owner then (
      Queue.add work t.pending;
      trace_action t Producer_schedule.Trace.Yield work.owner;
      t.metrics.inference_yields <- t.metrics.inference_yields + 1;
      t.metrics.peak_pending_inferences <-
        max t.metrics.peak_pending_inferences (Queue.length t.pending)))

let revisit_direction t =
  if
    t.config.lookahead = 0
    || t.metrics.inference_ordinary_batches mod 16 <> 15
    || Queue.length t.pending >= 32
  then None
  else
    let guard () = check_time t in
    let fresh parents clause =
      let support =
        List.concat_map (Avatar.dependency t.avatar) parents |> List.sort_uniq compare
      in
      not (Avatar.duplicate t.avatar ~guard ~variants:t.config.variants ~except:(-1) support clause)
    in
    match
      Directions.next t.directions ~guard ~epoch:t.index.generation ~alive:(current_ticket t)
        ~get:(Proof.get t.proof) ~calculus:t.calculus ~index:t.index ~equalities:t.equality_index
        ~fresh
    with
    | None -> None
    | Some (((id, _) as ticket), proposal) ->
        trace_action t Producer_schedule.Trace.Revisit ticket;
        observe t "direction_sampled" (Proof.get t.proof id);
        let groups =
          List.map
            (fun (clause, rule) ->
              let parents =
                List.map (fun id -> (id, Tbl.Int.find t.retained_index.live id)) (Wire.parents rule)
              in
              { parents; start = (fun () -> Seq.return (fun emit -> emit clause rule)) })
            proposal.Directions.conclusions
        in
        Some { owner = ticket; current = None; groups = List.to_seq groups }

let take_pending t =
  (* Count dispatched live continuations, not the outer selection clock: pending
     work is normally taken only on every other ordinary turn. Stale owners do
     not consume a slot; cancellation after dispatch still does. *)
  let turn = t.pending_resumptions + 1 in
  let preferred = turn mod 4 = 0 in
  let work =
    if not preferred then Queue.take t.pending
    else
      let best =
        Queue.fold
          (fun best work ->
            if
              current_ticket t work.owner
              && ((not (current_ticket t best.owner))
                 || Focus.rank t.focus (fst work.owner) > Focus.rank t.focus (fst best.owner))
            then work
            else best)
          (Queue.peek t.pending) t.pending
      in
      let remaining =
        Queue.to_seq t.pending |> Seq.filter (fun work -> work != best) |> List.of_seq
      in
      Queue.clear t.pending;
      List.iter (fun work -> Queue.add work t.pending) remaining;
      best
  in
  if current_ticket t work.owner then (
    t.pending_resumptions <- turn;
    if preferred then t.focus.preferred_resumes <- t.focus.preferred_resumes + 1);
  trace_action t Producer_schedule.Trace.Pending work.owner;
  work

(* One line of the selection trace (AXIOM_MEASURE_GIVEN_TRACE, lean workers only): strategy,
   selection number, clause id, outcome, the queue and evaluation of the last
   Passive pick, and the clause. An outcome is [processed], [processed-now] (the replacement of
   the given before it, processed in the same selection), [subsumed] or [hidden-<rule>] (the
   given was simplified at selection). A diagnostic that compares a port's given clauses with
   E's (-l1); it never changes the search. *)
let trace_given t (step : step) outcome =
  match !given_trace with
  | Some write when lean t ->
      let queue, (priority, weight) = Passive.last_pick t.passive in
      write
        (Printf.sprintf "%s\t%d\t%d\t%s%s\t%d\t%d\t%g\t%s\n" t.config.strategy.name t.metrics.given
           step.id outcome
           (if t.presat_running then "-presat" else "")
           queue priority weight (Given_trace.clause step.clause))
  | _ -> ()

(* [Heuristic.loop.backward]: E's eliminate_unit_simplified_clauses (ClauseSetUnitSimplify with
   ClauseUnitSimplifyTest) for a unit given that is no rewrite rule: a negative unit ~A simplifies
   the processed clauses without a negative literal that have a positive literal A sigma, an
   unorientable positive unit s = t those with a negative literal (s = t) sigma. E moves each one
   out of the processed set, in its set order (non-units, then units, each in insertion order),
   and the copy loses the literal when it re-enters (ForwardModifyClause): here the copy is the
   unit deletion itself, a processed clause, rewritten at E's FullRewrite level. *)
let backward_unit_cut t (given : step) =
  match given.clause with
  | [ u ]
    when not
           (u.positive
           &&
           match u.atom with
           | E (l, r) -> Ordering.greater ~order:t.order l r || Ordering.greater ~order:t.order r l
           | P _ | D _ -> true) ->
      let ordinal (s : step) =
        match t.activations with
        | Some table -> Option.value ~default:max_int (Tbl.Int.find_opt table s.id)
        | None -> max_int
      in
      let victims =
        Index.all t.index
        |> List.filter (fun (s : step) ->
            s.id <> given.id
            &&
            let all_positive = List.for_all (fun (l : literal) -> l.positive) s.clause in
            if u.positive then not all_positive else all_positive)
        |> List.map (fun (s : step) -> ((if List.length s.clause > 1 then 0 else 1), ordinal s, s))
        |> List.sort (fun (a, b, _) (c, d, _) -> compare (a, b) (c, d))
      in
      List.iter
        (fun (_, _, (s : step)) ->
          check_time t;
          if Index.mem t.index s.id then
            let ys = Clause.scope 2 s.clause in
            let attempt atom =
              try Some (Subsumption.atom ~guard:(fun () -> check_time t) [] u.atom atom)
              with Subsumption.No_match -> None
            in
            let rec find j = function
              | [] -> None
              | (l : literal) :: rest -> (
                  if l.positive = u.positive then find (j + 1) rest
                  else
                    match
                      match attempt l.atom with
                      | Some _ as found -> found
                      | None -> ( match l.atom with E (a, b) -> attempt (E (b, a)) | _ -> None)
                    with
                    | Some sigma -> Some (j, sigma)
                    | None -> find (j + 1) rest)
            in
            match find 0 ys with
            | None -> ()
            | Some (j, sigma) ->
                ignore (reduce t ~target:s.id ~using:given.id);
                Tbl.Int.replace t.dead s.id ();
                t.origin_next <- Some [];
                t.metrics.backward_unit_cut <- t.metrics.backward_unit_cut + 1;
                t.mark_processed <- true;
                t.full_next <- full_rewrite_strategy t.config.strategy;
                emit t (Clause.remove j ys)
                  (Resolve (given.id, 0, s.id, j, Contraction.into_side sigma)))
        victims
  | _ -> ()

let process_given t (given : step) =
  t.metrics.processed <- t.metrics.processed + 1;
  (* [Heuristic.loop.backward]: E's order of backward simplification after activation (rewriting,
     subsumption, unit simplification). *)
  let e_backward = backward_strategy t.config.strategy && vampire t = None in
  (match vampire t with
  | Some v ->
      (* Vampire's backward subsumption is off unless the slice sets bs; its generating
         inferences, the unary ones included, run when the clause is activated. *)
      if v.backward_subsumption && List.length given.clause = 1 then backward_simplify t given
  | None ->
      if (not e_backward) && (List.length given.clause = 1 || discount_strategy t.config.strategy)
      then backward_simplify t given);
  if t.presat_running then (
    (* Presaturation (E's SelectNoGeneration): the given clause simplifies and joins the active
       set, and generates nothing. *)
    activate t given;
    if e_backward then (
      backward_simplify t given;
      backward_unit_cut t given))
  else (
    select_literal t given (emit t);
    if Calculus.e_calculus t.calculus then (
      (* E inserts the given clause into the processed set (and backward-rewrites with it) before
       generate_new_clauses, so its conclusions are admitted with the given as a rule. *)
      activate t given;
      if e_backward then (
        backward_simplify t given;
        backward_unit_cut t given);
      if gen_order_strategy t.config.strategy then t.e_batch <- Some [];
      Telemetry.with_stage t.timing "inference" (fun () ->
          Calculus.unary t.calculus given (if t.e_batch <> None then conclude t else emit t)));
    if vampire t <> None then t.vampire_batch <- Some [];
    if vampire t <> None then
      (* Vampire's generating inferences in its order (SaturationAlgorithm::createFromOptions adds
         each to the front): unit resulting resolution, then the binary inferences, then the unary
         ones (factoring, equality resolution, equality factoring), which join the given clause's
         work as its last group. *)
      Telemetry.with_stage t.timing "inference" (fun () -> urr_generate t given);
    process_inference t (prepare_inferences t given))

(* The end of presaturation ([Heuristic.loop.presat], E's ProofStateResetProcessed): every active
   clause leaves the active set and re-enters Passive with a new evaluation, as a processed clause,
   in E's set order: oriented positive units, unorientable positive units, negative units, the
   rest, each in activation order. *)
let end_presat t =
  t.presat_running <- false;
  let active = List.rev t.presat_active |> List.filter (fun id -> Index.mem t.index id) in
  t.presat_active <- [];
  let set id =
    match (Proof.get t.proof id).clause with
    | [ { positive = true; atom = E (l, r) } ] ->
        if Ordering.greater ~order:t.order l r || Ordering.greater ~order:t.order r l then 0 else 1
    | [ { positive = true; _ } ] -> 0
    | [ { positive = false; _ } ] -> 2
    | _ -> 3
  in
  let steps =
    List.stable_sort (fun a b -> compare (set a) (set b)) active |> List.map (Proof.get t.proof)
  in
  List.iter (fun (s : step) -> deactivate t s.id) steps;
  List.iter
    (fun (s : step) ->
      Hashtbl.replace t.processed_ids s.id ();
      retain t s)
    steps;
  (* Passive deletes lazily: the heap entries of the clauses' first evaluations are still there and
     would select them by those again, now that the clauses are live. *)
  Passive.rebuild t.passive

(* A given clause that a simplification at selection retired has a replacement when [contract]
   admitted one ([capture]: the first clause [retain] admitted meanwhile). A lean worker with
   [given_at_once] processes that replacement now, as E processes the given clause it simplified
   (ForwardContractClause, then ProcessClause); it was just admitted, so it is simplified and not
   subsumed by an active clause, and it leaves Passive without taking a selection turn. Otherwise
   the replacement waits in Passive like any new clause. *)
(* A selected clause that destructive equality resolution replaces is a processed given of E that
   generates nothing (ProcessClause: document_processing, then replacing_inferences): its
   replacement is a new clause, admitted at the new clauses' rewrite level, and waits in Passive.
   Only the members with [Heuristic.loop.replacing] separate the two; the others resolve
   destructively at selection. *)
let process_or_replace t (given : step) outcome =
  match if replacing_strategy t.config.strategy then destructive_er t given else None with
  | Some result ->
      trace_given t given (outcome ^ "-er");
      t.full_target <- -1;
      (* E's replacement is the processed clause itself (CPIsProcessed), re-evaluated. *)
      Hashtbl.replace t.processed_ids given.id ();
      ignore (contract t given result : bool)
  | None -> (
      match vampire t with
      | Some v when v.split_at_activation && vampire_split t given ->
          (* SaturationAlgorithm::activate with sac=on: a selected clause that splits is removed
             instead of activated. *)
          trace_given t given "split"
      | _ ->
          trace_given t given outcome;
          process_given t given)

let select_given t id =
  let given = Proof.get t.proof id in
  Option.iter
    (fun generation -> trace_action t Producer_schedule.Trace.Given (id, generation))
    (Tbl.Int.find_opt t.retained_index.live id);
  t.metrics.given <- t.metrics.given + 1;
  if t.lrs_first = None && vampire t <> None then t.lrs_first <- Some (work_reading t);
  observe t "selected" given;
  (* E rewrites the selected clause with FullRewrite (ProcessClause). *)
  if full_rewrite_strategy t.config.strategy then t.full_target <- given.id;
  (* [Heuristic.loop.replacing]: destructive equality resolution comes after the contraction (E's
     replacing_inferences, [process_or_replace]). Vampire's Otter and LRS loops do not simplify a
     clause when it is selected. *)
  let simplified =
    if vampire_simplifying t then None
    else if replacing_strategy t.config.strategy then
      (* ForwardContractClause removes resolved literals ([Heuristic.loop.resolved]) with the
         rewriting; destructive equality resolution waits for replacing_inferences. *)
      match resolved_literal t given with
      | Some _ as result -> result
      | None -> rewrite_ordinary t given
    else rewrite t given
  in
  let hidden, replacement =
    match simplified with
    | None -> (false, None)
    | Some result ->
        t.capture <- Armed;
        let hidden =
          try contract t given result
          with e ->
            t.capture <- Off;
            raise e
        in
        let replacement = match t.capture with Captured id -> Some id | Off | Armed -> None in
        t.capture <- Off;
        (hidden, replacement)
  in
  let subsumed =
    (not hidden) && t.config.subsumption && t.config.backward_subsumption
    && (not (vampire_simplifying t))
    && Telemetry.with_stage t.timing "subsumption" (fun () ->
        match forward_subsumer ~except:id t given.clause with
        | Some using when reduce t ~target:id ~using:using.id ->
            t.metrics.given_subsumed <- t.metrics.given_subsumed + 1;
            true
        | _ -> false)
  in
  (* EQ-UNIT: the rules activated since its admission may make the given ground joinable. *)
  let subsumed =
    subsumed
    || ((not hidden) && ground_redundant t given)
       &&
       (retire t id;
        t.metrics.given_subsumed <- t.metrics.given_subsumed + 1;
        true)
  in
  if (not hidden) && not subsumed then process_or_replace t given "processed"
  else (
    trace_given t given
      (match simplified with
      | None -> "subsumed"
      | Some { rule = Paramodulate _; _ } -> "hidden-rewrite"
      | Some { rule = Equality_resolve _; _ } -> "hidden-er"
      | Some _ -> "hidden-contract");
    match replacement with
    | Some next when hidden && Tbl.Int.mem t.passive.live next ->
        if lean t && t.config.given_at_once then (
          Passive.invalidate t.passive next;
          t.metrics.given_at_once <- t.metrics.given_at_once + 1;
          let next = Proof.get t.proof next in
          Option.iter
            (fun generation -> trace_action t Producer_schedule.Trace.Given (next.id, generation))
            (Tbl.Int.find_opt t.retained_index.live next.id);
          observe t "selected" next;
          process_or_replace t next "processed-now")
        else t.metrics.given_requeued <- t.metrics.given_requeued + 1
    | _ -> ());
  sample_memory t

let request_premises t tickets gain =
  tickets |> List.to_seq
  |> Seq.filter (fun ((id, _) as ticket) ->
      current_ticket t ticket && Tbl.Int.mem t.passive.live id)
  |> Seq.take 8
  |> Seq.iter (fun ((id, _) as ticket) ->
      Directions.request t.directions ticket;
      Passive.prefer t.passive id (Focus.credit t.focus id + gain))

let goal_redundant t ~guard parents clause =
  let support = List.concat_map (Avatar.dependency t.avatar) parents |> List.sort_uniq compare in
  Avatar.duplicate t.avatar ~guard ~variants:t.config.variants ~except:(-1) support clause

let goal_only_step ?(first = false) t =
  let guard () = check_time t in
  let discard parents clause =
    goal_redundant t ~guard parents clause
    || t.config.subsumption
       &&
       let support =
         List.concat_map (Avatar.dependency t.avatar) parents |> List.sort_uniq compare
       in
       let accept (s : step) =
         Avatar.subset (Avatar.dependency t.avatar s.id) support && subsumes t s.clause clause
       in
       if t.config.subsumption_indexed then
         Subsumption_index.exists_forward t.retained_subsumption clause accept
       else List.exists accept (Index.all t.retained_index)
  in
  let observations = t.transfer_observations in
  let source = ref Transfer_policy.Empty in
  let on_commit empty =
    source := if empty then Transfer_policy.Empty else Transfer_policy.Publication;
    Transfer_policy.commit observations !source
  in
  let record clause rule =
    let step = record t clause rule in
    Transfer_policy.ancestor observations !source step;
    step
  in
  let emit clause rule =
    emit_consumed t
      ~recorded:(Transfer_policy.result observations !source)
      ~accepted:(Transfer_policy.accepted observations !source)
      clause rule
  in
  let use _tickets _gain = observations.use_calls <- observations.use_calls + 1 in
  let demand ~guard:_ _clause = observations.demand_calls <- observations.demand_calls + 1 in
  let offer =
    Goal_transfer.offer t.transfer ~guard ~alive:(current_ticket t)
      ~blocked:(Avatar.blocked t.avatar ~guard)
  in
  let previous = t.focus.committing in
  t.focus.committing <- true;
  Fun.protect
    ~finally:(fun () -> t.focus.committing <- previous)
    (fun () ->
      Goal.advance ~offer ~on_commit ~first t.goals ~guard ~blocked:(Avatar.blocked t.avatar ~guard)
        ~alive:(current_ticket t) ~record ~emit ~redundant:discard ~use ~demand)

let consumer_ready t = Goal_transfer.has_work t.transfer

let consumer_step t =
  let guard () = check_time t in
  Goal_transfer.advance t.transfer ~guard ~alive:(current_ticket t)
    ~blocked:(Avatar.blocked t.avatar ~guard) ~record:(record t) ~emit:(emit_consumed t)

let focus_step t =
  let guard () = check_time t in
  Focus.advance t.focus ~guard ~alive:(current_ticket t) ~get:(Proof.get t.proof) ~record:(record t)
    ~emit:(emit t) ~redundant:(goal_redundant t ~guard) ~demand:t.on_demand

(* E drops an orphan when it would select it (HCBStandardClauseSelect, ClauseIsOrphaned): a Passive
   clause whose generating inference has a premise that backward simplification retired. The turn
   stays with the next clause of the same queue. *)
let orphan t id =
  match Tbl.Int.find_opt t.origins id with
  | Some premises -> dead_premise t premises
  | None -> false

let take_given t =
  match !selection_guide with
  | Some g when lean t -> (
      match g.pick t with
      | Some id when Tbl.Int.mem t.passive.live id ->
          Passive.invalidate t.passive id;
          Some id
      | _ -> Passive.take t.passive)
  | _ ->
      if orphans_strategy t.config.strategy && Tbl.Int.length t.dead > 0 then
        Passive.take
          ~skip:(fun id ->
            orphan t id
            &&
            (retire t id;
             t.metrics.orphans <- t.metrics.orphans + 1;
             true))
          t.passive
      else Passive.take t.passive

let infer_step t =
  protect (fun () ->
      Telemetry.with_stage t.timing "inference" (fun () ->
          t.calculus.guard <- (fun () -> check_time t);
          check_time t;
          t.metrics.inference_batches <- t.metrics.inference_batches + 1;
          let first_ready =
            Passive.length t.passive > 0 && t.metrics.given < t.config.limits.max_given
          in
          let open Directions.Schedule in
          let ready =
            (if
               Focus.has_work t.focus || (first_ready && not (Queue.is_empty t.directions.requested))
             then [ Demand ]
             else [])
            @ if first_ready || not (Queue.is_empty t.pending) then [ Continue ] else []
          in
          let effort () =
            t.metrics.generated + t.calculus.attempts + t.index.postings + t.retained_index.postings
            + t.equality_index.postings
          in
          let before = effort () and started = cost_now () in
          match choose t.work ready with
          | None -> if Passive.length t.passive > 0 then stop t "given clause limit"
          | Some job ->
              Producer_schedule.Trace.lane_select t.schedule_trace ~turn:t.work.turns ~ready
                ~selected:job ~batch:t.metrics.inference_batches ~demand_runs:t.work.lanes.(1).runs
                ~continue_runs:t.work.lanes.(2).runs;
              Fun.protect
                ~finally:(fun () ->
                  let charged_work =
                    max 1
                      (1 + effort () - before
                      + int_of_float (1000. *. min 1000000. (cost_now () -. started)))
                  in
                  charge t.work job charged_work;
                  Producer_schedule.Trace.lane_charge t.schedule_trace ~turn:(t.work.turns - 1)
                    ~selected:job ~work:charged_work ~batch:t.metrics.inference_batches
                    ~generated:t.metrics.generated ~attempts:t.calculus.attempts)
                (fun () ->
                  match job with
                  | First -> ()
                  | Demand -> (
                      let requested =
                        if first_ready then
                          Directions.demanded t.directions ~alive:(fun ((id, _) as ticket) ->
                              current_ticket t ticket && Tbl.Int.mem t.passive.live id)
                        else None
                      in
                      match requested with
                      | Some (id, _) ->
                          Passive.invalidate t.passive id;
                          select_given t id
                      | None -> if Focus.has_work t.focus then focus_step t)
                  | Continue -> (
                      t.metrics.inference_ordinary_batches <-
                        t.metrics.inference_ordinary_batches + 1;
                      match revisit_direction t with
                      | Some work -> process_inference t work
                      | None ->
                          if
                            (not (Queue.is_empty t.pending))
                            && ((not first_ready) || lean t || t.work.lanes.(2).runs mod 2 = 0)
                          then
                            (* Lean (E) mode finishes every inference of a given clause
                               before it selects the next given clause. *)
                            process_inference t (take_pending t)
                          else Option.iter (select_given t) (take_given t)))))

let ordinary_step ?synthesize ?enumerate t =
  if t.root = None && t.stopped = None then t.finished <- None;
  protect (fun () -> synchronize t);
  if t.presat_running && Passive.length t.passive = 0 && Queue.is_empty t.pending then
    protect (fun () -> end_presat t);
  let ready =
    (if Passive.length t.passive > 0 || (not (Queue.is_empty t.pending)) || Focus.has_work t.focus
     then [ Control.Infer ]
     else [])
    @ (if t.avatar.splits_ready && not (Queue.is_empty t.avatar.pending_splits) then
         [ Control.Split ]
       else [])
    @ (if ground_ready t then [ Control.Ground ] else [])
    @ (if synthesize <> None then [ Control.Synthesize ] else [])
    @ if enumerate <> None then [ Control.Enumerate ] else []
  in
  let gain () = t.focus.progress in
  let before = gain () and generated = t.metrics.generated in
  let started = cost_now () and stored = Proof.stored t.proof in
  let previous_batch = t.metrics.inference_batches in
  t.busy <- true;
  Fun.protect
    ~finally:(fun () -> t.busy <- false)
    (fun () ->
      protect (fun () ->
          check_time t;
          match Control.choose t.control ready with
          | None -> ()
          | Some operation ->
              Producer_schedule.Trace.control_select t.schedule_trace ~turn:t.control.turns ~ready
                ~selected:operation ~given:t.metrics.given ~pending:(Queue.length t.pending)
                ~generated:t.metrics.generated;
              (match operation with
              | Control.Infer -> infer_step t
              | Split -> split_step t t.avatar
              | Ground -> Telemetry.with_stage t.timing "ground" (fun () -> ground_step t)
              | Synthesize -> Option.iter (fun f -> f ()) synthesize
              | Enumerate -> Option.iter (fun f -> f ()) enumerate);
              let gain = gain () - before in
              let cost =
                t.metrics.generated - generated
                + max 0 (Proof.stored t.proof - stored)
                + int_of_float (1000. *. min 1000000. (cost_now () -. started))
              in
              Control.observe t.control operation ~gain ~cost;
              Producer_schedule.Trace.control_observe t.schedule_trace ~turn:(t.control.turns - 1)
                ~selected:operation ~gain ~cost ~generated:t.metrics.generated
                ~stored:(Proof.stored t.proof)));
  if
    t.config.collect_every > 0
    && t.metrics.inference_batches <> previous_batch
    && t.metrics.inference_batches mod t.config.collect_every = 0
  then periodic_collect t Producer_schedule.Trace.Ordinary

let ordinary_has_work t =
  t.presat_running
  || Passive.length t.passive > 0
  || (not (Queue.is_empty t.pending))
  || ((not (lean t)) && Focus.has_work t.focus)
  || (t.knowledge_epoch <> t.ground_epoch && vampire t = None)
  || Ground_boolean.has_work t.ground_boolean
  || t.avatar.dirty
  || (t.avatar.splits_ready && not (Queue.is_empty t.avatar.pending_splits))

let has_work t =
  ordinary_has_work t || ((not (lean t)) && (Goal.has_work t.goals || consumer_ready t))

let step ?synthesize ?enumerate t =
  if t.root = None && t.stopped = None then t.finished <- None;
  let open Producer_schedule in
  let ready =
    (if ordinary_has_work t || synthesize <> None || enumerate <> None then [ Ordinary ] else [])
    @ (if
         (not (lean t))
         && Goal.has_work t.goals
         && (t.metrics.given < t.config.limits.max_given || t.goals.metrics.expanded > 0)
       then [ Goal ]
       else [])
    @ if (not (lean t)) && consumer_ready t then [ Consumer ] else []
  in
  let effort = function
    | Ordinary ->
        t.metrics.generated + t.calculus.attempts + t.index.postings + t.retained_index.postings
        + t.equality_index.postings
    | Goal ->
        t.metrics.generated + t.goals.calculus.attempts + t.goals.index.postings
        + t.goals.equality.postings
    | Consumer -> t.metrics.generated + Goal_transfer.effort t.transfer
  in
  let producer_runs () = (snapshot t.producers Goal).runs + (snapshot t.producers Consumer).runs in
  let before = producer_runs () in
  t.busy <- true;
  Fun.protect
    ~finally:(fun () -> t.busy <- false)
    (fun () ->
      protect (fun () ->
          check_time_now t;
          t.calculus.guard <- (fun () -> check_time t);
          ignore
            (dispatch t.producers ready ~effort ~now:cost_now (function
              | Ordinary -> ordinary_step ?synthesize ?enumerate t
              | Goal -> Telemetry.with_stage t.timing "inference" (fun () -> goal_only_step t)
              | Consumer -> Telemetry.with_stage t.timing "inference" (fun () -> consumer_step t)))));
  if
    t.config.collect_every > 0
    && producer_runs () <> before
    && producer_runs () mod t.config.collect_every = 0
  then periodic_collect t Producer_schedule.Trace.Producer;
  enforce_budget t

let run_steps t n =
  let rec go n =
    if n > 0 && t.root = None && t.stopped = None && has_work t then (
      step t;
      go (n - 1))
  in
  go n

let finish t =
  while t.root = None && t.stopped = None && has_work t do
    step t
  done;
  seal t

let release_index (i : Index.t) =
  Tbl.Feature.reset i.buckets;
  Tbl.Int.reset i.live;
  Tbl.Int.reset i.cells;
  i.dirty <- [];
  i.stale <- 0;
  i.stale_postings <- 0;
  i.all <- [];
  i.cached <- None;
  i.size <- 0

let release_equality (q : Equality_index.t) =
  Tbl.Head_opt.reset q.sources;
  Tbl.Head_opt.reset q.targets;
  Tbl.Int.reset q.live;
  Tbl.Int.reset q.cells;
  q.dirty_sources <- [];
  q.dirty_targets <- [];
  q.stale <- 0

let release_subsumption (s : Subsumption_index.t) =
  Tbl.Feature.reset s.root.children;
  s.root.terminal <- [];
  s.root.size <- 0;
  s.root.stale <- 0;
  Feature_vector.clear s.vectors;
  Tbl.Int.reset s.live

let release_calculus (c : Calculus.t) =
  Tbl.Int.reset c.selected;
  Hashtbl.reset c.memo

(* Drops the search state of an engine that has ended without a refutation and will never run
   again, so that the collector reclaims it while the rest of its worker runs on (a time-shared
   engine that ended on its own, [Scheduler.sliced_search]). Every stored clause is held by several
   of these structures at once (the proof store, Passive, the indexes, AVATAR, Goal, the transfer
   requests, Focus, Directions), so a clause becomes garbage only when all of them are emptied:
   on development-corpus problems that ended at their limits, emptying all but AVATAR, Goal and
   Focus freed less than 20 % of the engine's reachable words, emptying all of them more than
   99 %. The configuration,
   the axioms, the stop reason, the timing and every counter stay, so the engine still reports its
   metrics; its live-set gauges (Passive, index and proof-store sizes) read 0, and so do its
   footprint and [has_work]. The engine is sealed first, at the time it ended. *)
let release t =
  if t.root <> None then invalid_arg "Engine.release: a refuted engine keeps its proof";
  seal t;
  Queue.clear t.pending;
  Work_table.reset t.transfer_work;
  Tbl.Int.reset t.transfer_owners;
  ignore (Proof.reclaim t.proof []);
  Tbl.Int.reset t.node_words;
  t.stored_words <- 0;
  t.census <- 0;
  let p = t.passive in
  p.weight <- Passive.Empty;
  p.unit_weight <- Passive.Empty;
  p.age <- Passive.Empty;
  p.preferred <- Passive.Empty;
  Array.fill p.kinds 0 (Array.length p.kinds) Passive.Empty;
  Tbl.Int.reset p.preference;
  Tbl.Int.reset p.live;
  Tbl.Int.reset p.classes;
  Option.iter
    (fun (m : Passive.mix) ->
      Array.fill m.heaps 0 (Array.length m.heaps) Passive.EEmpty;
      Hashtbl.reset m.evals)
    p.mix;
  List.iter release_index [ t.index; t.retained_index ];
  List.iter release_subsumption [ t.subsumption_index; t.retained_subsumption ];
  release_equality t.equality_index;
  let release_rules (d : Demodulation.t) =
    Tbl.Head.reset d.rules;
    Tbl.Int.reset d.live;
    Tbl.Int.reset d.cells;
    Tbl.Head.reset d.cache;
    Tbl.Head.reset d.trees;
    Tbl.Head.reset d.unoriented_cache;
    d.dirty <- [];
    d.stale <- 0;
    d.version <- d.version + 1
  in
  release_rules t.demodulator;
  Option.iter release_rules t.equations;
  t.peak <- None;
  t.admit_peak <- None;
  let c = t.contraction in
  release_index c.units;
  release_index c.binary;
  Contraction.Keys.reset c.classes;
  Tbl.Int.reset c.steps;
  Tbl.Int.reset c.inverse;
  Tbl.Feature.reset c.partnered;
  c.touched <- [];
  let a = t.avatar in
  List.iter Tbl.Int.reset [ a.support_users; a.lock_users ];
  Tbl.Int.reset a.entries;
  Tbl.Int.reset a.components;
  Tbl.Int.reset a.splits;
  t.probe <- Avatar.probe [];
  Avatar.Seen.reset a.seen;
  Tbl.Clause.reset a.names;
  Avatar.Variants.reset a.variants;
  Tbl.Clause_ints.reset a.component_variants;
  Tbl.Ints.reset a.constraints;
  Queue.clear a.pending_splits;
  a.constraints_rev <- [];
  a.conflict_cores <- [];
  a.dirty <- false;
  a.splits_ready <- false;
  let g = t.goals in
  release_index g.index;
  release_equality g.equality;
  release_calculus g.calculus;
  Tbl.Int.reset g.states;
  Tbl.Clause_ints.reset g.memo;
  Tbl.Pair.reset g.roots;
  List.iter Queue.clear [ g.cache; g.promotion; g.ready; g.continuing ];
  Queue.clear g.revisits;
  Queue.clear g.refresh_order;
  g.fresh_states <- [];
  g.fresh_roots <- [];
  g.refresh_left <- 0;
  let r = t.transfer in
  release_index r.recipe_index;
  release_equality r.recipe_equality;
  Term.clear r.terms;
  List.iter Tbl.Int.reset [ r.ancestor_ids; r.direct_ids; r.accepted_ids ];
  Tbl.Int.reset r.offers;
  Tbl.Int.reset r.requests;
  Tbl.Int.reset r.request_owners;
  Tbl.Clause_ints.reset r.memo;
  List.iter Queue.clear [ r.request_ready; r.request_sweep ];
  r.fresh_offers <- [];
  r.request_refresh_left <- 0;
  let f = t.focus in
  release_index f.units;
  release_index f.goals;
  Tbl.Int.reset f.entries;
  Tbl.Feature.reset f.by_literal;
  Tbl.Pair.reset f.queued;
  Tbl.Pair.reset f.saved;
  Queue.clear f.requests;
  List.iter Queue.clear [ f.goal_order; f.pending ];
  f.fresh_entries <- [];
  Term.clear f.scratch;
  let s = t.directions in
  release_calculus s.probe;
  Tbl.Int.reset s.entries;
  Tbl.Pair.reset s.requests;
  List.iter Queue.clear [ s.queue; s.requested ];
  release_calculus t.calculus;
  Ground_boolean.clear t.ground_boolean;
  Tbl.Int.reset t.ground_units;
  Tbl.Literal.reset t.ground_literals;
  t.ground_clashes <- 0;
  t.ground_reflexive <- 0;
  t.ground_equations <- 0;
  Tbl.Atom.reset t.component_atoms;
  t.ground_epoch <- t.knowledge_epoch;
  Term.clear t.terms;
  Physical.reset t.normal_terms;
  Physical.reset t.normal_terms_full;
  List.iter Hashtbl.reset [ t.initial_ids; t.processed_ids; t.sos_ids; t.unfolded_inputs ];
  Hashtbl.reset t.levels;
  Hashtbl.reset t.releasable;
  t.normal_form_rule <- None

let certificate t ~theory =
  Option.map
    (fun root ->
      let extract avatar =
        Proof.extract ?avatar ~cnf_mode:t.config.cnf_mode t.proof ~theory ~axioms:t.axioms ~root
      in
      if not t.avatar.unsat then extract None
      else if vampire t <> None then
        (* A Vampire slice member splits every clause that enters Passive, so its incremental
           Boolean proof is long: certify a fresh refutation of the same clauses. *)
        extract (Some (Avatar.certificate ~fresh:true t.avatar))
      else
        let incremental = extract (Some (Avatar.certificate t.avatar)) in
        if not t.config.fresh_refutation then incremental
        else
          (* The search has ended: solve the same Boolean inputs once more in a new solver and
             keep whichever certificate has fewer steps after pruning (the incremental one on a
             tie, or when the new solve does not refute within its budget). The incremental
             refutation rests on clauses learned over the whole run. *)
          match Avatar.fresh_certificate t.avatar with
          | None -> incremental
          | Some avatar ->
              let fresh = extract (Some avatar) in
              if fst (Proof.statistics fresh) < fst (Proof.statistics incremental) then fresh
              else incremental)
    t.root

(* Exhausting a trimmed clause set is not saturation of the input. *)
let trimming_note t =
  if t.metrics.budget_trimmed = 0 then ""
  else
    let n = t.metrics.budget_trimmed in
    Printf.sprintf " after the memory budget discarded %d passive clause%s" n
      (if n = 1 then "" else "s")

let reason t =
  match t.stopped with
  | Some reason -> reason
  | None when t.metrics.budget_trimmed > 0 ->
      "finite clause set exhausted" ^ trimming_note t ^ "; consistency not established"
  | None -> "finite clause set saturated; consistency not established"
