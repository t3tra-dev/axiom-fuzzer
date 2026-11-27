let quote s = "\"" ^ String.concat "\"\"" (String.split_on_char '"' s) ^ "\""
let row xs = String.concat "," xs ^ "\n"
let integer = string_of_int
let number x = Printf.sprintf "%.9g" x

let stage_names =
  [
    "enumeration";
    "guidance";
    "clausification";
    "simplification";
    "subsumption";
    "demodulation";
    "inference";
    "boolean";
    "branch_update";
    "ground";
    "collection";
  ]

let r13_header =
  [
    "r13_transfer";
    "r13_store_enabled";
    "r13_consumer_enabled";
    "r13_isolated";
    "r13_legacy_feedback";
    "r13_goal_publication_commits";
    "r13_goal_empty_commits";
    "r13_goal_use_calls";
    "r13_goal_use_applied";
    "r13_goal_demand_calls";
    "r13_goal_demand_applied";
    "r13_offered";
    "r13_merged";
    "r13_invalidated";
    "r13_blocked";
    "r13_store_live";
    "r13_consumers_live";
    "r13_slices";
    "r13_resumed";
    "r13_resolution_attempts";
    "r13_outgoing_attempts";
    "r13_incoming_attempts";
    "r13_conclusions";
    "r13_tautologies";
    "r13_stale_results";
    "r13_ancestor_recorded";
    "r13_emit_calls";
    "r13_direct_recorded";
    "r13_accepted";
    "r13_retained";
    "r13_unconditional";
    "r13_conditional";
    "r13_feedback";
    "r13_producer_turns";
    "r13_ordinary_ready";
    "r13_ordinary_selected";
    "r13_ordinary_runs";
    "r13_ordinary_work";
    "r13_ordinary_effort";
    "r13_ordinary_milliseconds";
    "r13_goal_ready";
    "r13_goal_selected";
    "r13_goal_runs";
    "r13_goal_work";
    "r13_goal_effort";
    "r13_goal_milliseconds";
    "r13_consumer_ready";
    "r13_consumer_selected";
    "r13_consumer_runs";
    "r13_consumer_work";
    "r13_consumer_effort";
    "r13_consumer_milliseconds";
    "r13_goal_ids";
    "r13_consumer_ids";
    "r13_goal_final_ids";
    "r13_consumer_final_ids";
  ]

let r14_header =
  [
    "r14_requests_enabled";
    "r14_feedback_enabled";
    "r14_request_opened";
    "r14_request_sealed";
    "r14_request_drained";
    "r14_request_invalidated";
    "r14_request_slices";
    "r14_request_resumed";
    "r14_request_live";
    "r14_request_open";
    "r14_request_draining";
    "r14_work_bindings";
    "r14_trace_json";
  ]

(* Version 5 fixes one column order for both CSVs: version 4's 309 observation columns
   ([base_header]); in the summary, its 18 portfolio and reference columns ([summary_header]); then
   the groups every worker computes about itself, in merge order (the strategy group
   [strategy_header], the single-worker slice group [slice_header], then the caps and memory-budget
   group [budget_header]: [worker_group_header]); and last the columns the process supervisor adds
   ([process_header] per worker row, [isolation_header] in the summary). The summary's reference
   columns end with the reference's own heap reading ([reference_peak_domain_words]). Later column
   groups of a worker go after these groups and before the supervisor's columns. Version 6 is
   version 5 (the strategy, slice, caps and budget, and process groups) plus the deterministic
   budget's three columns ([peak_footprint_words], [budget_checks], [budget_digest]). *)
let version = "6"

(* Single-worker probe slices (Scheduler.config.slices). The row's engine
   columns describe the engine that produced the proof, or the continuing
   engine when there is none; these columns cover the whole worker, and
   slice_main_given/generated/retained always describe the continuing
   engine. *)
let slice_header =
  [
    "slice_policy";
    "slice_main_slices";
    "slice_probe_slices";
    "slice_main_steps";
    "slice_probe_steps";
    "slice_main_work";
    "slice_probe_work";
    "slice_main_share";
    "slice_main_seconds";
    "slice_probe_seconds";
    "slice_probes_created";
    "slice_peak_live_probes";
    "slice_probe_given";
    "slice_probe_generated";
    "slice_winner";
    "slice_winner_slice";
    "slice_probe_admitted";
    "slice_probe_admit_seconds";
    "slice_probe_skipped";
    "slice_probe_revived";
    "slice_main_given";
    "slice_main_generated";
    "slice_main_retained";
  ]

let slice_values (w : Scheduler.worker_metrics) =
  let s = w.slices in
  [
    quote s.policy;
    integer s.main_slices;
    integer s.probe_slices;
    integer s.main_steps;
    integer s.probe_steps;
    integer s.main_work;
    integer s.probe_work;
    number (Slices.main_share s);
    number s.main_seconds;
    number s.probe_seconds;
    integer s.probes_created;
    integer s.peak_live_probes;
    integer s.probe_given;
    integer s.probe_generated;
    quote s.winner;
    integer s.winner_slice;
    integer s.probe_admitted;
    number s.probe_admit_seconds;
    integer s.probe_skipped;
    integer s.probe_revived;
    integer w.continuing.metrics.given;
    integer w.continuing.metrics.generated;
    integer w.continuing.metrics.retained;
  ]

(* Hard caps and soft budgets as configured, then the budget's own activity. *)
let budget_header =
  [
    "limit_given";
    "limit_generated";
    "limit_retained";
    "budget_heap_words";
    "budget_proof_nodes";
    "budget_responses";
    "budget_heap_responses";
    "budget_node_responses";
    "budget_cursor_drops";
    "budget_trimmed";
    "budget_first_seconds";
    "peak_domain_words";
    "budget_deferred";
    "budget_released";
    "budget_reinjected";
    "peak_footprint_words";
    "budget_checks";
    "budget_digest";
  ]

let budget_values (w : Scheduler.worker_metrics) =
  let e = w.engine in
  let m = e.metrics and limits = e.config.limits and budget = e.config.budget in
  [
    integer limits.max_given;
    integer limits.max_generated;
    integer limits.max_retained;
    integer budget.heap_words;
    integer budget.proof_nodes;
    integer m.budget_responses;
    integer m.budget_heap_responses;
    integer m.budget_node_responses;
    integer m.budget_cursor_drops;
    integer m.budget_trimmed;
    number m.budget_first_seconds;
    integer m.peak_domain_words;
    integer m.budget_deferred;
    integer m.budget_released;
    integer m.budget_reinjected;
    integer m.peak_footprint_words;
    integer m.budget_checks;
    Printf.sprintf "%016x" m.budget_digest;
  ]

(* Every observation column of version 4. *)
let base_header =
  [
    "metrics_version";
    "worker";
    "result";
    "generated";
    "retained";
    "given";
    "unifications";
    "index_candidates";
    "index_baseline";
    "heap_words";
    "seconds";
    "replay_seconds";
    "clauses_per_second";
    "retention_ratio";
    "axiom_instances";
    "proof_steps";
    "injected_axioms";
    "injected_instances";
    "used_axioms";
    "unification_successes";
    "tautologies";
    "duplicates";
    "variants";
    "memory_samples";
    "subsumed";
    "subsumption_trials";
    "subsumption_exhausted";
    "subsumption_candidates";
    "subsumption_baseline";
    "backward_subsumed";
    "given_subsumed";
    "subsumption_resolved";
    "resolution_trials";
    "unit_deleted";
    "literal_rewritten";
    "contraction_trials";
    "contraction_exhausted";
    "paramodulation_candidates";
    "paramodulation_baseline";
    "ordering_rejected";
    "demodulated";
    "ordered";
    "demodulation";
    "backward_demodulation";
    "backward_demodulated";
    "backward_demodulation_candidates";
    "backward_demodulation_baseline";
    "guided";
    "guided_compounds";
    "guidance_observed";
    "guidance_processed";
    "guidance_stale";
    "guidance_literals";
    "guidance_rejected_literals";
    "guidance_candidates";
    "guidance_unique";
    "guidance_duplicates";
    "guidance_filtered";
    "guidance_dropped";
    "guidance_dropped_events";
    "guidance_offered";
    "guidance_already_injected";
    "guidance_peak_pending";
    "guidance_matches";
    "guidance_complementary";
    "guidance_constrained";
    "guidance_history_patterns";
    "guidance_history_offered";
    "guidance_replaced";
    "guidance_exhausted_matches";
    "guidance_demands";
    "guidance_demanded_offered";
    "exhaustive_instances";
    "guided_instances";
    "guided_used_instances";
    "live_clauses";
    "active_clauses";
    "passive_clauses";
    "proof_nodes";
    "collections";
    "reclaimed_proof_nodes";
    "reclaimed_term_nodes";
    "subsumption_indexed";
    "equality_indexed";
    "backward_subsumption";
    "variants_enabled";
    "selection";
    "allocated_words";
    "weight_ratio";
    "indexed";
    "cnf_mode";
    "fingerprint";
    "resolution_postings";
    "resolution_fingerprint_rejected";
    "resolution_occurrences";
    "equality_postings";
    "equality_fingerprint_rejected";
    "equality_occurrences";
    "lookahead_budget";
    "lookahead_postings";
    "lookahead_exhausted";
    "lookahead_changed";
    "positive_directions";
    "direction_probes";
    "direction_retries";
    "direction_admitted";
    "direction_rejected";
    "demand_requests";
    "demand_selected";
    "work_first_runs";
    "work_demand_runs";
    "work_continue_runs";
    "work_first_cost";
    "work_demand_cost";
    "work_continue_cost";
    "inference_batches";
    "inference_ordinary_batches";
    "inference_yields";
    "inference_cancelled";
    "peak_pending_inferences";
    "focus_requests";
    "focus_matches";
    "focus_trials";
    "focus_progress";
    "focus_probes";
    "focus_preferred_resumes";
    "focus_preferred_selected";
    "focus_plans";
    "focus_plan_trials";
    "focus_plan_steps";
    "focus_plan_closed";
    "focus_plan_exhausted";
    "focus_plan_stale";
    "focus_plan_dropped";
    "focus_plan_redundant";
    "focus_plan_deferred";
    "focus_plan_reused";
    "focus_plan_invalidated";
    "focus_plan_prioritized";
    "focus_plan_useful";
    "goal_created";
    "goal_expanded";
    "goal_attempts";
    "goal_shared";
    "goal_resumed";
    "goal_woken";
    "goal_waiting";
    "goal_depth_cut";
    "goal_weight_cut";
    "goal_slices";
    "goal_widened";
    "goal_roots";
    "goal_invalidated";
    "goal_evicted";
    "goal_retired";
    "goal_committed";
    "goal_closed";
    "goal_conditional";
    "goal_blocked";
    "goal_redundant";
    "goal_age_total";
    "goal_age_max";
    "goal_fresh_selected";
    "goal_continued_selected";
    "goal_wait_total";
    "goal_wait_max";
    "goal_height_max";
    "goal_depth_max";
    "goal_promoted";
    "goal_promotion_stale";
    "goal_resolution_attempts";
    "goal_equality_attempts";
    "goal_first_trials";
    "goal_delta_queries";
    "goal_reused";
    "negative_selected";
    "one_positive_selected";
    "many_positive_selected";
    "negative_wait_total";
    "one_positive_wait_total";
    "many_positive_wait_total";
    "negative_wait_max";
    "one_positive_wait_max";
    "many_positive_wait_max";
    "clause_weight";
    "avatar_enabled";
    "avatar_components";
    "avatar_splits";
    "avatar_component_reused";
    "avatar_conflicts";
    "avatar_sat_calls";
    "avatar_model_changes";
    "avatar_model_examined";
    "avatar_minimized";
    "avatar_deactivated";
    "avatar_reactivated";
    "avatar_locked";
    "avatar_unlocked";
    "avatar_lock_limited";
    "avatar_max_support";
    "avatar_boolean_proof_nodes";
    "avatar_sat_decisions";
    "avatar_sat_propagations";
    "avatar_sat_conflicts";
    "avatar_sat_learned";
    "avatar_sat_backjumps";
    "ground_runs";
    "ground_merges";
    "ground_conflicts";
    "ground_explanation_steps";
    "ground_boolean_inputs";
    "ground_boolean_derived_inputs";
    "ground_boolean_atoms";
    "ground_boolean_nodes";
    "ground_boolean_calls";
    "ground_boolean_yields";
    "ground_boolean_conflicts";
    "ground_boolean_replay_steps";
    "ground_boolean_final_steps";
    "ground_boolean_released";
    "ground_boolean_rebuilt";
    "ground_boolean_solve_seconds";
    "ground_boolean_replay_seconds";
    "inference_turns";
    "split_turns";
    "ground_turns";
    "synthesis_turns";
    "enumeration_turns";
    "reason";
  ]
  @ List.map (fun s -> s ^ "_seconds") stage_names
  @ r13_header @ r14_header

(* The worker's strategy, then the diagnostics of a ported E heuristic: the KBO admissibility
   repairs of its generated weights and the selections served by each queue of its queue mix
   ("n0;n1;..."; empty without a mix). They follow the observation columns of a worker row and
   the portfolio and reference columns of the summary CSV, where they describe the proving worker
   (empty for a reference proof). Only the supervisor's process columns come after them. *)
let strategy_header = [ "strategy"; "order_violations"; "mix_selections" ]

(* The groups every worker computes about itself after its observation columns, in merge order:
   the strategy group, the slice group, then the caps and memory-budget group. *)
let worker_group_header = strategy_header @ slice_header @ budget_header

(* The columns a worker computes about itself ([values]; in process mode, in the worker
   process). *)
let header = base_header @ worker_group_header

let r13_values (w : Scheduler.worker_metrics) =
  let e = w.engine in
  let observations = e.transfer_observations and m = e.transfer.metrics in
  let goal_groups =
    [
      ("publication_ancestors", observations.publication_ancestors);
      ("publication_results", observations.publication_results);
      ("publication_accepted", observations.publication_accepted);
      ("empty_ancestors", observations.empty_ancestors);
      ("empty_results", observations.empty_results);
      ("empty_accepted", observations.empty_accepted);
    ]
  in
  let consumer_groups =
    [
      ("ancestors", e.transfer.ancestor_ids);
      ("direct", e.transfer.direct_ids);
      ("accepted", e.transfer.accepted_ids);
    ]
  in
  let final = Hashtbl.create 32 in
  Option.iter
    (fun (c : Wire.certificate) ->
      List.iter (fun (s : Wire.step) -> Hashtbl.replace final s.id ()) c.steps)
    w.certificate;
  let ids_json keep groups =
    let field (key, ids) =
      "\"" ^ key ^ "\":["
      ^ String.concat "," (Transfer_policy.ids ids |> List.filter keep |> List.map string_of_int)
      ^ "]"
    in
    quote ("{" ^ String.concat "," (List.map field groups) ^ "}")
  in
  let service kind =
    let s = Producer_schedule.snapshot e.producers kind in
    List.map integer [ s.ready; s.selected; s.runs; s.work; s.effort; s.milliseconds ]
  in
  [
    Transfer_policy.name;
    "true";
    "true";
    "true";
    "false";
    integer observations.publication_commits;
    integer observations.empty_commits;
    integer observations.use_calls;
    integer observations.use_applied;
    integer observations.demand_calls;
    integer observations.demand_applied;
    integer m.offered;
    integer m.merged;
    integer m.invalidated;
    integer m.blocked;
    integer (Tbl.Int.length e.transfer.offers);
    (* Legacy broad-consumer gauge; live requests have separate columns. *)
    integer 0;
    integer m.slices;
    integer m.resumed;
    integer m.resolution_attempts;
    integer m.outgoing_attempts;
    integer m.incoming_attempts;
    integer m.conclusions;
    integer m.tautologies;
    integer m.stale_results;
    integer m.ancestor_recorded;
    integer m.emit_calls;
    integer m.direct_recorded;
    integer m.accepted;
    integer m.retained;
    integer m.unconditional;
    integer m.conditional;
    integer m.feedback;
    integer (Producer_schedule.turns e.producers);
  ]
  @ service Producer_schedule.Ordinary
  @ service Producer_schedule.Goal
  @ service Producer_schedule.Consumer
  @ [
      ids_json (fun _ -> true) goal_groups;
      ids_json (fun _ -> true) consumer_groups;
      ids_json (Hashtbl.mem final) goal_groups;
      ids_json (Hashtbl.mem final) consumer_groups;
    ]

let r14_values (w : Scheduler.worker_metrics) =
  let e = w.engine in
  let m = e.transfer.request_metrics in
  let opened, draining = Goal_transfer.request_counts e.transfer in
  [
    "true";
    "false";
    integer m.opened;
    integer m.sealed;
    integer m.drained;
    integer m.invalidated;
    integer m.slices;
    integer m.resumed;
    integer (opened + draining);
    integer opened;
    integer draining;
    integer (Engine.Work_table.length e.transfer_work);
    quote (Producer_schedule.Trace.json e.schedule_trace);
  ]

let base_values (w : Scheduler.worker_metrics) =
  let e = w.engine in
  let m = e.metrics in
  let duration = Engine.elapsed e in
  let instances =
    List.fold_left (fun n (s : Scheduler.schema_metrics) -> n + s.injected) 0 w.schemas
  in
  let g = w.guidance in
  let exhaustive =
    List.fold_left (fun n (s : Scheduler.schema_metrics) -> n + s.exhaustive_injected) 0 w.schemas
  in
  let guided =
    List.fold_left (fun n (s : Scheduler.schema_metrics) -> n + s.guided_injected) 0 w.schemas
  in
  let avatar f = integer (f e.avatar) in
  let sat f = avatar (fun a -> f (Boolean.statistics a.Avatar.solver)) in
  [
    version;
    integer w.worker_id;
    (if w.proof_steps = 0 then "UNKNOWN" else "UNSAT");
    integer m.generated;
    integer m.retained;
    integer m.given;
    integer e.calculus.attempts;
    integer (e.index.candidates + e.retained_index.candidates);
    integer (e.index.scans + e.retained_index.scans);
    integer m.peak_live_words;
    number duration;
    number w.replay_seconds;
    number (float m.generated /. max 0.000001 duration);
    number (float m.retained /. float (max 1 m.generated));
    integer w.used_instances;
    integer w.proof_steps;
    integer (List.length e.axioms);
    integer instances;
    integer w.used_axioms;
    integer e.calculus.successes;
    integer m.tautologies;
    integer m.duplicates;
    integer m.variants;
    integer m.memory_samples;
    integer m.subsumed;
    integer m.subsumption_trials;
    integer m.subsumption_exhausted;
    integer (e.subsumption_index.candidates + e.retained_subsumption.candidates);
    integer (e.subsumption_index.baseline + e.retained_subsumption.baseline);
    integer m.backward_subsumed;
    integer m.given_subsumed;
    integer m.subsumption_resolved;
    integer m.resolution_trials;
    integer e.contraction.unit_deleted;
    integer e.contraction.literal_rewritten;
    integer e.contraction.trials;
    integer e.contraction.exhausted;
    integer e.equality_index.candidates;
    integer e.equality_index.baseline;
    integer e.calculus.ordering_rejected;
    integer m.demodulated;
    string_of_bool e.config.ordered;
    string_of_bool e.config.demodulation;
    string_of_bool e.config.backward_demodulation;
    integer m.backward_demodulated;
    integer m.backward_demodulation_candidates;
    integer m.backward_demodulation_baseline;
    string_of_bool w.guided_enabled;
    string_of_bool w.guided_compounds;
    integer g.observed;
    integer g.processed;
    integer g.stale;
    integer g.literals;
    integer g.rejected_literals;
    integer g.candidates;
    integer g.unique;
    integer g.duplicates;
    integer g.filtered;
    integer g.dropped;
    integer g.dropped_events;
    integer g.offered;
    integer g.already_injected;
    integer g.peak_pending;
    integer g.matches;
    integer g.complementary;
    integer g.constrained;
    integer g.history_patterns;
    integer g.history_offered;
    integer g.replaced;
    integer g.exhausted_matches;
    integer g.demands;
    integer g.demanded_offered;
    integer exhaustive;
    integer guided;
    integer w.guided_used;
    integer (Tbl.Int.length e.retained_index.live);
    integer (Tbl.Int.length e.index.live);
    integer (Passive.length e.passive);
    integer (Proof.stored e.proof);
    integer m.collections;
    integer m.reclaimed_nodes;
    integer m.reclaimed_terms;
    string_of_bool e.config.subsumption_indexed;
    string_of_bool e.config.equality_indexed;
    string_of_bool e.config.backward_subsumption;
    string_of_bool e.config.variants;
    string_of_bool e.config.selection;
    number m.allocated_words;
    integer e.config.weight_ratio;
    string_of_bool e.config.indexed;
    Wire.cnf_mode_name e.config.cnf_mode;
    string_of_bool e.config.fingerprint;
    integer (e.index.postings + e.retained_index.postings);
    integer (e.index.fingerprint_rejected + e.retained_index.fingerprint_rejected);
    integer (e.index.occurrences + e.retained_index.occurrences);
    integer e.equality_index.postings;
    integer e.equality_index.fingerprint_rejected;
    integer e.equality_index.occurrences;
    integer e.config.lookahead;
    integer m.lookahead_postings;
    integer m.lookahead_exhausted;
    integer m.lookahead_changed;
    integer m.positive_directions;
    integer e.directions.probes;
    integer e.directions.retries;
    integer e.directions.useful;
    integer e.directions.rejected;
    integer e.directions.demand_requests;
    integer e.directions.demand_selected;
    integer e.work.lanes.(0).runs;
    integer e.work.lanes.(1).runs;
    integer e.work.lanes.(2).runs;
    integer e.work.lanes.(0).work;
    integer e.work.lanes.(1).work;
    integer e.work.lanes.(2).work;
    integer m.inference_batches;
    integer m.inference_ordinary_batches;
    integer m.inference_yields;
    integer m.inference_cancelled;
    integer m.peak_pending_inferences;
    integer e.focus.requested;
    integer e.focus.matches;
    integer e.focus.trials;
    integer e.focus.progress;
    integer e.focus.probes;
    integer e.focus.preferred_resumes;
    integer e.passive.preferred_selected;
    integer e.focus.plans;
    integer e.focus.plan_trials;
    integer e.focus.plan_steps;
    integer e.focus.plan_closed;
    integer e.focus.plan_exhausted;
    integer e.focus.plan_stale;
    integer e.focus.plan_dropped;
    integer e.focus.plan_redundant;
    integer e.focus.plan_deferred;
    integer e.focus.plan_reused;
    integer e.focus.plan_invalidated;
    integer e.focus.plan_prioritized;
    integer e.focus.plan_useful;
    integer e.goals.metrics.created;
    integer e.goals.metrics.expanded;
    integer e.goals.metrics.attempts;
    integer e.goals.metrics.shared;
    integer e.goals.metrics.resumed;
    integer e.goals.metrics.woken;
    integer e.goals.metrics.waiting;
    integer e.goals.metrics.depth_cut;
    integer e.goals.metrics.weight_cut;
    integer e.goals.metrics.slices;
    integer e.goals.metrics.widened;
    integer e.goals.metrics.roots;
    integer e.goals.metrics.invalidated;
    integer e.goals.metrics.evicted;
    integer e.goals.metrics.retired;
    integer e.goals.metrics.committed;
    integer e.goals.metrics.closed;
    integer e.goals.metrics.conditional;
    integer e.goals.metrics.blocked;
    integer e.goals.metrics.redundant;
    integer e.goals.metrics.age_total;
    integer e.goals.metrics.age_max;
    integer e.goals.metrics.fresh_selected;
    integer e.goals.metrics.continued_selected;
    integer e.goals.metrics.wait_total;
    integer e.goals.metrics.wait_max;
    integer e.goals.metrics.height_max;
    integer e.goals.metrics.depth_max;
    integer e.goals.metrics.promoted;
    integer e.goals.metrics.promotion_stale;
    integer e.goals.metrics.resolution_attempts;
    integer e.goals.metrics.equality_attempts;
    integer e.goals.metrics.first_trials;
    integer e.goals.metrics.delta_queries;
    integer e.goals.metrics.reused;
    integer e.passive.kind_selected.(0);
    integer e.passive.kind_selected.(1);
    integer e.passive.kind_selected.(2);
    integer e.passive.kind_wait_total.(0);
    integer e.passive.kind_wait_total.(1);
    integer e.passive.kind_wait_total.(2);
    integer e.passive.kind_wait_max.(0);
    integer e.passive.kind_wait_max.(1);
    integer e.passive.kind_wait_max.(2);
    Passive.policy_name e.config.clause_weight;
    string_of_bool e.config.avatar;
    avatar (fun a -> Tbl.Int.length a.components);
    avatar (fun a -> Tbl.Int.length a.splits);
    avatar (fun a -> a.component_reused);
    avatar (fun a -> a.conflicts);
    avatar (fun a -> a.sat_calls);
    avatar (fun a -> a.model_changes);
    avatar (fun a -> a.model_examined);
    avatar (fun a -> a.minimized);
    avatar (fun a -> a.deactivated);
    avatar (fun a -> a.reactivated);
    avatar (fun a -> a.locked);
    avatar (fun a -> a.unlocked);
    avatar (fun a -> a.lock_limited);
    avatar (fun a -> a.max_support);
    avatar (fun a -> Boolean.proof_size a.solver);
    sat (fun s -> s.decisions);
    sat (fun s -> s.propagations);
    sat (fun s -> s.conflicts);
    sat (fun s -> s.learned_clauses);
    sat (fun s -> s.nonchronological_backjumps);
    integer e.ground.runs;
    integer e.ground.merges;
    integer e.ground.conflicts;
    integer e.ground.explanations;
    integer e.ground_boolean.statistics.inputs;
    integer e.ground_boolean.statistics.derived_inputs;
    integer (Tbl.Atom.length e.ground_boolean.atoms);
    integer (Boolean.proof_size e.ground_boolean.solver);
    integer e.ground_boolean.statistics.calls;
    integer e.ground_boolean.statistics.yields;
    integer e.ground_boolean.statistics.conflicts;
    integer e.ground_boolean.statistics.replayed;
    integer
      (match w.certificate with
      | None -> 0
      | Some certificate -> Ground_boolean.final_steps e.ground_boolean certificate);
    integer e.ground_boolean.statistics.released;
    integer e.ground_boolean.statistics.rebuilt;
    number e.ground_boolean.statistics.solve_seconds;
    number e.ground_boolean.statistics.replay_seconds;
    integer e.control.arms.(0).runs;
    integer e.control.arms.(1).runs;
    integer e.control.arms.(2).runs;
    integer e.control.arms.(3).runs;
    integer e.control.arms.(4).runs;
    quote w.reason;
  ]
  @ List.map (fun s -> number (Telemetry.seconds e.timing s)) stage_names
  @ r13_values w @ r14_values w

let strategy_values (w : Scheduler.worker_metrics) =
  let e = w.engine in
  [
    quote w.strategy.name;
    integer e.order_violations;
    quote
      (String.concat ";"
         (Array.to_list (Array.map string_of_int (Passive.mix_selections e.passive))));
  ]

let worker_group_values w = strategy_values w @ slice_values w @ budget_values w
let values w = base_values w @ worker_group_values w

(* Worker rows of the forked-process portfolio are computed by [values] in each worker process.
   A lost worker (killed, crashed, or with an undecodable report) keeps a row that names the
   worker and the reason; its counters and worker-group columns are empty. *)
let blank ~worker ~result ~reason =
  List.map
    (function
      | "metrics_version" -> version
      | "worker" -> worker
      | "result" -> result
      | "reason" -> quote reason
      | _ -> "")
    header

let remote_values (w : Scheduler.remote_worker) =
  match w.remote_row with
  | Some values -> values
  | None -> blank ~worker:(integer w.remote_id) ~result:"UNKNOWN" ~reason:w.remote_reason

(* A worker row split into its observation columns and its worker-group columns. *)
let split_row values =
  let n = List.length base_header in
  (List.filteri (fun i _ -> i < n) values, List.filteri (fun i _ -> i >= n) values)

let process_header = [ "worker_pid"; "worker_exit"; "worker_cpu_seconds"; "worker_peak_rss_bytes" ]

(* The worker CSV appends per-process columns; Domain workers share one process. *)
let worker_header = header @ process_header

let process_values (p : Scheduler.process_stats) =
  [ integer p.pid; p.exit; number p.cpu_seconds; number p.peak_rss_bytes ]

let remote (r : Scheduler.result) =
  match r.processes with
  | None -> []
  | Some p ->
      List.sort (fun a b -> compare a.Scheduler.remote_id b.Scheduler.remote_id) p.remote_workers

(* The summary's portfolio and reference columns (version 4) and the supervisor's isolation
   columns. *)
let summary_header =
  [
    "workers";
    "total_generated";
    "total_retained";
    "total_given";
    "total_allocated_words";
    "portfolio_seconds";
    "output_seconds";
    "process_peak_rss_bytes";
    "proof_source";
    "reference_enabled";
    "reference_trials";
    "reference_cumulative_trials";
    "reference_script_trials";
    "reference_byte_trials";
    "reference_stage";
    "reference_seconds";
    "reference_resumed";
    "reference_reason";
    "reference_peak_domain_words";
  ]

let isolation_header =
  [ "isolation"; "lost_workers"; "processes_cpu_seconds"; "processes_peak_rss_bytes" ]

let workers (r : Scheduler.result) =
  String.trim
    (row worker_header
    ^ String.concat ""
        (List.map (fun w -> row (values w @ [ ""; "domain"; ""; "" ])) r.workers
        @ List.map
            (fun w -> row (remote_values w @ process_values w.Scheduler.remote_process))
            (remote r)))

let summary ~output_seconds (r : Scheduler.result) =
  let selected, selected_groups =
    match
      ( List.find_opt (fun (w : Scheduler.worker_metrics) -> w.worker_id = r.worker_id) r.workers,
        List.find_opt (fun (w : Scheduler.remote_worker) -> w.remote_id = r.worker_id) (remote r) )
    with
    | Some w, _ -> (base_values w, worker_group_values w)
    | None, Some w -> split_row (remote_values w)
    | None, None ->
        let instances axioms =
          List.length (List.filter (fun (a : Wire.axiom) -> Wire.is_instance a.origin) axioms)
        in
        let used = match r.certificate with None -> [] | Some c -> c.axioms in
        ( List.map
            (function
              | "metrics_version" -> version
              | "worker" -> "reference"
              | "result" -> if r.certificate = None then "UNKNOWN" else "UNSAT"
              | "seconds" -> (
                  match r.reference_report with None -> "0" | Some rr -> number rr.seconds)
              | "replay_seconds" -> number r.replay_seconds
              | "proof_steps" ->
                  integer
                    (match r.certificate with None -> 0 | Some c -> fst (Proof.statistics c))
              | "used_axioms" -> integer (List.length used)
              | "axiom_instances" -> integer (instances used)
              | "cnf_mode" -> Wire.cnf_mode_name r.cnf_mode
              | "reason" -> quote r.reason
              | _ -> "")
            base_header,
          List.map (fun _ -> "") worker_group_header )
  in
  let reference_values =
    match r.reference_report with
    | None -> [ "false"; "0"; "0"; "0"; "0"; "0"; "0"; "false"; quote "disabled"; "-1" ]
    | Some rr ->
        [
          "true";
          integer rr.trials;
          integer rr.tested;
          integer rr.script_tested;
          integer rr.byte_tested;
          integer rr.stage;
          number rr.seconds;
          string_of_bool rr.resumed;
          quote rr.reason;
          integer rr.peak_domain_words;
        ]
  in
  let reported =
    List.map (fun (w : Scheduler.worker_metrics) -> Scheduler.counters w.engine) r.workers
    @ List.filter_map (fun (w : Scheduler.remote_worker) -> w.remote_counters) (remote r)
  in
  let total f = List.fold_left (fun n c -> n + f c) 0 reported in
  let allocated =
    List.fold_left (fun n (c : Scheduler.counters) -> n +. c.allocated_words) 0. reported
  in
  let isolation_values =
    match r.processes with
    | None -> [ "domains"; "0"; ""; number (Telemetry.peak_rss_bytes ()) ]
    | Some p ->
        let processes =
          List.map (fun (w : Scheduler.remote_worker) -> w.remote_process) p.remote_workers
          @ Option.to_list p.reference_process
        in
        [
          "processes";
          integer (List.length p.lost);
          number (p.supervisor_cpu_seconds +. p.children_cpu_seconds);
          number
            (List.fold_left
               (fun n (s : Scheduler.process_stats) -> n +. s.peak_rss_bytes)
               p.supervisor_peak_rss_bytes processes);
        ]
  in
  String.trim
    (row (base_header @ summary_header @ worker_group_header @ isolation_header)
    ^ row
        (selected
        @ [
            integer (List.length r.workers + List.length (remote r));
            integer (total (fun c -> c.generated));
            integer (total (fun c -> c.retained));
            integer (total (fun c -> c.given));
            number allocated;
            number r.wall_seconds;
            number output_seconds;
            number (Telemetry.peak_rss_bytes ());
            quote r.proof_source;
          ]
        @ reference_values @ selected_groups @ isolation_values))

let schema_name = function
  | Wire.Comprehension -> "comprehension"
  | Separation -> "separation"
  | Replacement -> "replacement"
  | Unrestricted_separation -> "unrestricted_separation"
  | Registered (name, _) -> name

let schema_values (w : Scheduler.worker_metrics) =
  List.map
    (fun (s : Scheduler.schema_metrics) ->
      let formula_metric n = match s.schema with Wire.Registered _ -> "" | _ -> integer n in
      [
        integer w.worker_id;
        quote (schema_name s.schema);
        integer s.candidates;
        integer s.injected;
        formula_metric s.max_size;
        formula_metric s.max_parameters;
        integer s.exhaustive_candidates;
        integer s.guided_candidates;
        integer s.exhaustive_injected;
        integer s.guided_injected;
      ])
    w.schemas

let schemas (r : Scheduler.result) =
  String.trim
    (row
       [
         "worker";
         "schema";
         "candidates";
         "injected";
         "max_size";
         "max_parameters";
         "exhaustive_candidates";
         "guided_candidates";
         "exhaustive_injected";
         "guided_injected";
       ]
    ^ String.concat ""
        (List.map row
           (List.concat_map schema_values r.workers
           @ List.concat_map (fun (w : Scheduler.remote_worker) -> w.remote_schema_rows) (remote r)
           )))
