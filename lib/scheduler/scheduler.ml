type config = {
  engine : Engine.config;
  max_size : int;
  parameters : int;
  max_instances : int;
  quantum : int;
  guided : bool;
  max_guided_instances : int;
  guidance : Guided.config;
  reference : bool;
  reference_config : Reference.config;
  reference_only : bool;
  portfolio : Strategy.portfolio;
      (** Strategy of each heuristic worker; [engine.strategy] is the base. The default, [Balanced]
          with the production base, runs production on the first half of the workers (queue phases
          0, 1, ...) and the diversified members round-robin on the rest ([Strategy.balanced]); one
          worker runs production time-shared with the first diversified member ([slices],
          [Slices.share]) when the input has no schemas, and production alone otherwise. [Uniform]
          runs production alone on every worker, also on a single one (the all-production policy,
          for A/A checks). *)
  phase_base : int;
      (** Queue phase offset of every worker: a worker runs at [phase_base] plus the phase its
          portfolio gives it ([Strategy.resolve]: the worker index for production-queue strategies,
          the copy index for ported E heuristics). Internal (A/A checks and per-phase grids); the
          CLI default is 0. *)
  worker_phase : int option;
      (** This worker's queue phase, set by [worker_configs]. [None], in a configuration that was
          not resolved per worker, means [phase_base] plus the worker id. *)
  unfold : int option option;
      (** Replaces the equational-definition unfolding setting ([Strategy.t.unfold]) of every worker
          strategy: [Some None] turns it off, [Some (Some limit)] on with that eq-unfold-limit.
          Internal (A/A checks and per-member rows); [None], the default, keeps each strategy's own
          setting. *)
  loop : Heuristic.loop option;
      (** Replaces the E loop details ([Heuristic.loop]) of every ported E heuristic worker.
          Internal (fidelity screens); [None], the default, keeps each heuristic's own. *)
  slices : Slices.policy option;
      (** Probe slices of a single heuristic worker ([single_slices]). [None], the default, follows
          the portfolio: one [Balanced] worker whose input has no schemas runs [Slices.share]
          (production with e208 at queue phase 0, 1:1 on the work clock); every other single worker
          runs alone. [Some p] (the internal AXIOM_SLICES hook, for evaluation) runs [p] on a single
          worker whatever its portfolio and input; [Some Slices.off] runs it alone. Two or more
          workers cover phases and strategies in parallel and never slice ([worker_configs]). *)
  lane : Probe_lane.config;
      (** Schema probe lane of every heuristic worker, for theories with schemas (TPTP inputs have
          none). The default, [Probe_lane.default], uses only general mechanisms (fixed-axiom
          engine, instance probes spread over schemas and shapes, finite-model pool, and the
          observational source: the theory's own formulas, one per truth table over the pool) and no
          condition prior. [Probe_lane.disabled] runs exactly the main search. *)
}

let default_config =
  {
    engine = Engine.default_config;
    max_size = 0;
    parameters = 0;
    max_instances = max_int;
    quantum = 1;
    guided = true;
    max_guided_instances = max_int;
    guidance = Guided.default_config;
    reference = true;
    reference_config = Reference.default_config;
    reference_only = false;
    portfolio = Strategy.Balanced;
    phase_base = 0;
    worker_phase = None;
    unfold = None;
    loop = None;
    slices = None;
    lane = Probe_lane.default;
  }

type generator = Exhaustive | Guided
type trace = { axiom : Wire.axiom; predicate : string; generator : generator }

type schema_metrics = {
  schema : Wire.schema;
  mutable candidates : int;
  mutable injected : int;
  mutable max_size : int;
  mutable max_parameters : int;
  mutable exhaustive_candidates : int;
  mutable guided_candidates : int;
  mutable exhaustive_injected : int;
  mutable guided_injected : int;
}

type worker_metrics = {
  worker_id : int;
  strategy : Strategy.t;
  engine : Engine.t;
  certificate : Wire.certificate option;
  schemas : schema_metrics list;
  reference_tested : int;
  replay_seconds : float;
  used_axioms : int;
  used_instances : int;
  proof_steps : int;
  reason : string;
  guidance : Guided.metrics;
  guided_enabled : bool;
  guided_compounds : bool;
  guided_used : int;
  slices : Slices.stats;
  continuing : Engine.t;
      (** The worker's own-phase engine; [engine] differs only when a probe slice produced the
          proof. A schema-lane proof leaves both describing the continuing engine. *)
  lane : Probe_lane.stats option;
}

type counters = {
  generated : int;
  retained : int;
  given : int;
  unifications : int;
  postings : int;  (** resolution and equality postings visited (the CLI [Metrics:] line) *)
  heap_words : int;
  seconds : float;
  allocated_words : float;
  collection_seconds : float;  (** time in engine collection (the CLI [Heuristic N:] line) *)
  budget_responses : int;
  budget_cursor_drops : int;
  budget_trimmed : int;
  peak_domain_words : int;
      (** largest major-heap reading of the worker's Domain (reported only; the collector's view) *)
  peak_footprint_words : int;  (** largest footprint reading of the memory budget *)
  budget_checks : int;
  budget_digest : int;  (** digest of every budget reading and response (Engine.budget_digest) *)
}
(** Engine totals that survive the engine itself (process workers report these). *)

let counters (e : Engine.t) =
  {
    generated = e.metrics.generated;
    retained = e.metrics.retained;
    given = e.metrics.given;
    unifications = e.calculus.attempts;
    postings = e.index.postings + e.retained_index.postings + e.equality_index.postings;
    heap_words = e.metrics.peak_live_words;
    seconds = Engine.elapsed e;
    allocated_words = e.metrics.allocated_words;
    collection_seconds = Telemetry.seconds e.timing "collection";
    budget_responses = e.metrics.budget_responses;
    budget_cursor_drops = e.metrics.budget_cursor_drops;
    budget_trimmed = e.metrics.budget_trimmed;
    peak_domain_words = e.metrics.peak_domain_words;
    peak_footprint_words = e.metrics.peak_footprint_words;
    budget_checks = e.metrics.budget_checks;
    budget_digest = e.metrics.budget_digest;
  }

type process_stats = {
  pid : int;
  exit : string;  (** "exit N", "signal N" (OCaml signal number) or "running" *)
  cpu_seconds : float;  (** user + system CPU reported by the process; 0 if it never reported *)
  peak_rss_bytes : float;  (** peak RSS reported by the process; 0 if it never reported *)
}

type remote_worker = {
  remote_id : int;
  remote_row : string list option;
      (** Worker-metrics CSV fields computed in the worker process; [None] if it was lost. *)
  remote_schema_rows : string list list;
  remote_counters : counters option;
  remote_reason : string;
  remote_process : process_stats;
}

type process_info = {
  remote_workers : remote_worker list;
  reference_process : process_stats option;
  supervisor_cpu_seconds : float;
  children_cpu_seconds : float;
      (** OS-accounted CPU of the reaped children, killed ones included *)
  supervisor_peak_rss_bytes : float;
  lost : string list;  (** Workers whose result was lost: killed, crashed or undecodable. *)
}
(** Present only for the forked-process portfolio ([Portfolio]). *)

type result = {
  certificate : Wire.certificate option;
  reason : string;
  engine : Engine.t;
  traces : trace list;
  reference_tested : int;
  replay_seconds : float;
  worker_id : int;
  workers : worker_metrics list;
  wall_seconds : float;
  proof_source : string;
  reference_report : Reference.report option;
  axioms : Wire.axiom list;
  cnf_mode : Wire.cnf_mode;
  processes : process_info option;
}

(** The error raised when the kernel rejects a certificate that the search produced. Both portfolios
    use it: a Domain worker's own check and the process supervisor's re-check of a certificate its
    worker had accepted. *)
let rejected_search_proof e = "independent replay rejected search proof: " ^ e

(* A probe lane runs the worker's phase plus the lane offset, with the lane's
   strategy (default: the worker's). Probes search the continuing engine's
   axioms (the fixed axioms and every instance injected so far, with the same
   ids), have no guidance hooks, and stop at the worker's deadline.

   A lane whose probe ends before its budget is dead: a capped, cancelled or
   timed-out lane for good, a saturated lane until the continuing engine has
   more axioms. A probe search is deterministic in its phase, strategy, axioms
   and budget, so a restart-lane slice whose budget does not exceed one that a
   fresh engine of the lane already completed on the same axioms would only
   replay it: such a slice is skipped and its turn goes to the continuing
   engine.

   Every probe engine carries the worker's memory budgets (config.engine.budget).
   The engine that holds at least half of the worker's state (by its own reading)
   reads the worker's whole state, every other engine its own ([sliced_search]),
   so the largest engine answers the worker's pressure (cursor drops, the budget
   sweep, trimming its own derived clauses). Probes
   add the continuing engine's axioms without ~releasable: they never withdraw
   an instance, because nothing would add it back to them. A probe that a
   budget stops ends its lane for good, like a capped one, and the continuing
   engine keeps the worker's time.

   The continuing engine can end on its own as well: without a proof and before
   the worker's deadline or cancellation (which end every engine of the worker
   alike), by a memory or node budget, a cap, the safety limit, or because it
   has no work left. Its search state is then released (Engine.release) and the
   lanes keep the worker's remaining time: the continuing slices are skipped,
   the probe slices run back to back, and the worker ends at a proof, at the
   deadline, or when no lane can run any more. *)
(* The queue phase of worker [worker_id]'s engines. *)
let queue_phase config ~worker_id =
  match config.worker_phase with Some phase -> phase | None -> config.phase_base + worker_id

(* A strategy with the configuration's unfolding override ([config.unfold]). *)
let with_unfold config (s : Strategy.t) =
  let s =
    match config.unfold with Some unfold when unfold <> s.unfold -> { s with unfold } | _ -> s
  in
  match (config.loop, s.heuristic) with
  | Some loop, Some h when loop <> h.loop -> { s with heuristic = Some { h with loop } }
  | _ -> s

(** The slice policy of a single heuristic worker of [workers] whose input has or has no [schemas]
    (see [config.slices]): an explicit policy; by default [Slices.share] for one [Balanced] worker
    on an input without schemas, the same composition as the two-worker balanced portfolio
    (production at the worker's phase and the first diversified member at queue phase 0) time-shared
    on one worker; otherwise none. A theory with schemas keeps production with its schema probe
    lane, and [Uniform], [Standard] and [Workers] keep one engine per worker. *)
let single_slices ~workers ~schemas (config : config) =
  if workers > 1 then Slices.off
  else
    match (config.slices, config.portfolio) with
    | Some p, _ -> p
    | None, Strategy.Balanced when not schemas -> Slices.share
    | None, _ -> Slices.off

let sliced_search ~(config : config) ~worker_id ~cancelled ~prepare ~fixed ~(stats : Slices.stats)
    ~(main : Engine.t) ~main_alive ~main_turn ~proved ~selected =
  let policy = Option.value config.slices ~default:Slices.off in
  Slices.validate policy;
  let lanes = Array.of_list policy.lanes in
  let deadline = main.started +. config.engine.limits.seconds in
  let engines = Hashtbl.create 8 in
  (* key -> [Some n]: saturated with n axioms; [None]: dead for good. *)
  let dead = Hashtbl.create 8 in
  (* Restart lanes: key -> (largest completed budget, axioms it searched). *)
  let completed = Hashtbl.create 8 in
  (* The worker's memory budget covers all of its engines whenever one of them holds at least half
     of the worker's state, which is always the case with two live engines (the default share);
     with three or more live engines (evaluation-only AXIOM_SLICES probes) none may qualify, and
     then every engine reads only its own footprint, as before. Each engine has its own reading: its
     footprint, or what [prepare] installed (a test seam). The engine whose own reading is at least
     that of all the others together reads the worker's whole state; every other engine reads its
     own. Over the budget the largest engine therefore answers for the worker with its own cursors
     and clauses, and the 2x ceiling stops it, never a smaller engine on account of a larger one's
     state; once released, an engine no longer counts. While the worker's whole state stays under
     the budget, and whenever a probe holds the larger part (the continuing engine then reads its
     own footprint and the probe the sum, as before), the search is the same as with the
     continuing engine reading only itself. The readings are taken after every step and allocate
     nothing, so they never move the work clock that cuts the slices: while one engine runs the
     others are suspended, so their part is fixed, and it is computed between slices. *)
  let seams = Hashtbl.create 8 in
  let main_reading = main.heap_reading and main_counts = ref true in
  let main_own =
    if main_reading == Engine.own_footprint then fun () -> Engine.footprint main else main_reading
  in
  let probes_total ?except () =
    Hashtbl.fold
      (fun key ((p : Engine.t), _) words ->
        if Some key = except then words
        else
          words
          + match Hashtbl.find_opt seams key with Some own -> own () | None -> Engine.footprint p)
      engines 0
  in
  (* The live probes' part of the continuing engine's reading, and the other engines' part of the
     running probe's. *)
  let probes_part = ref 0 and others_part = ref 0 in
  main.heap_reading <-
    (fun () ->
      let own = main_own () and others = !probes_part in
      if own >= others then own + others else own);
  let release key =
    Option.iter
      (fun (probe, _) ->
        Engine.seal probe;
        stats.live_probes <- stats.live_probes - 1)
      (Hashtbl.find_opt engines key);
    Hashtbl.remove engines key;
    (* Only tests install seams; an empty table is left alone, since [create] releases inside the
       new probe's measured first slice and every allocated word there counts. *)
    if Hashtbl.length seams > 0 then Hashtbl.remove seams key
  in
  let create key (lane : Slices.lane) =
    release key;
    let seconds = Float.max 0. (deadline -. Telemetry.now ()) in
    let strategy =
      with_unfold config (Option.value ~default:config.engine.strategy lane.strategy)
    in
    let probe =
      Engine.create
        ~phase:(queue_phase config ~worker_id + lane.offset)
        ~cancelled
        { config.engine with strategy; limits = { config.engine.limits with seconds } }
    in
    prepare probe;
    let installed = probe.heap_reading in
    if installed == Engine.own_footprint then
      probe.heap_reading <-
        (fun () ->
          let own = Engine.footprint probe and others = !others_part in
          if own >= others then own + others else own)
    else (
      Hashtbl.replace seams key installed;
      probe.heap_reading <-
        (fun () ->
          let own = installed () and others = !others_part in
          if own >= others then own + others else own));
    stats.probes_created <- stats.probes_created + 1;
    stats.live_probes <- stats.live_probes + 1;
    stats.peak_live_probes <- max stats.peak_live_probes stats.live_probes;
    let slot = (probe, ref 0) in
    Hashtbl.replace engines key slot;
    slot
  in
  (* Copy the continuing engine's axioms that this probe has not seen yet;
     returns how many axioms the probe has been given. The fixed axioms, the
     first ones of the continuing engine, go in together (the probe's own
     ordering and unfolding, Engine.add_initial_axioms). *)
  let feed (probe, fed) =
    if !fed = 0 then (
      Engine.add_initial_axioms probe fixed;
      fed := List.length fixed);
    List.iteri
      (fun i axiom ->
        if i >= !fed then (
          Engine.add_axiom probe axiom;
          fed := i + 1))
      main.axioms;
    !fed
  in
  (* Work of an engine since [start] in the policy's measure, and whether a
     slice with [budget] units and [taken] steps is used up. On the work clock
     only the running engine's checks count, and the domain's allocation
     between two readings is that engine's. *)
  let work (e : Engine.t) start taken =
    match policy.measure with
    | Steps -> taken
    | Generated -> e.metrics.generated - start
    | Work -> Engine.work_reading e - start
  in
  let used e start taken budget =
    work e start taken >= budget
    || (policy.measure = Generated && taken >= 16 * min budget (max_int / 16))
  in
  (* Deficit carry-over: the budgets handed to the continuing engine and to
     each lane so far, and the work they did in their slices. *)
  let main_target = ref 0 and main_done = ref 0 in
  let lane_target = Array.make (Array.length lanes) 0
  and lane_done = Array.make (Array.length lanes) 0 in
  (* A continuing slice; [None] runs the continuing engine to the end. *)
  let run_main budget =
    let before = Telemetry.now () and taken = ref 0 in
    let start =
      match policy.measure with
      | Work -> Engine.work_reading main
      | Steps | Generated -> main.metrics.generated
    in
    let open_ () = match budget with None -> true | Some b -> not (used main start !taken b) in
    while open_ () && main_alive () do
      taken := !taken + main_turn ()
    done;
    let done_ = work main start !taken in
    main_done := !main_done + done_;
    stats.main_slices <- stats.main_slices + 1;
    stats.main_steps <- stats.main_steps + !taken;
    stats.main_work <- stats.main_work + done_;
    stats.main_seconds <- stats.main_seconds +. (Telemetry.now () -. before)
  in
  let run_probe position index budget fresh =
    let before = Telemetry.now () in
    let lane = lanes.(position) in
    let key = Slices.key position lane in
    (* Between slices, outside the measured work: the suspended engines' part of this probe's
       reading. *)
    others_part := (if !main_counts then main_own () else 0) + probes_total ~except:key ();
    let resumed =
      match Hashtbl.find_opt engines key with Some slot when not fresh -> Some slot | _ -> None
    in
    (* The work clock before the admission: a new engine has made no checks yet, so creating it
       and admitting the inputs are charged to this slice. *)
    let clock_before =
      Engine.work_clock
        ~checks:(match resumed with Some ((p : Engine.t), _) -> p.metrics.checks | None -> 0)
    in
    let (((probe : Engine.t), _) as slot) =
      match resumed with Some slot -> slot | None -> create key lane
    in
    let given = probe.metrics.given and generated = probe.metrics.generated in
    let known = !(snd slot) in
    let axioms = feed slot in
    if known > 0 then stats.probe_late_axioms <- stats.probe_late_axioms + axioms - known;
    let admitted = probe.metrics.generated - generated in
    stats.probe_admitted <- stats.probe_admitted + admitted;
    stats.probe_admit_seconds <- stats.probe_admit_seconds +. (Telemetry.now () -. before);
    (* A step budget cannot charge the admission (it takes no step); a
       generated-clause budget counts the admitted input clauses, and the work
       clock the whole admission. *)
    let start =
      match policy.measure with
      | Steps -> probe.metrics.generated
      | Generated -> generated
      | Work -> clock_before
    and taken = ref 0 in
    while
      (not (used probe start !taken budget))
      && probe.root = None && probe.stopped = None && Engine.has_work probe
    do
      Engine.step probe;
      incr taken
    done;
    let finished = used probe start !taken budget in
    let done_ = work probe start !taken in
    lane_done.(position) <- lane_done.(position) + done_;
    stats.probe_slices <- stats.probe_slices + 1;
    stats.probe_steps <- stats.probe_steps + !taken;
    stats.probe_work <- stats.probe_work + done_;
    stats.probe_given <- stats.probe_given + probe.metrics.given - given;
    stats.probe_generated <- stats.probe_generated + probe.metrics.generated - generated;
    if probe.root <> None then (
      stats.winner <- Slices.lane_name lane;
      stats.winner_slice <- index;
      selected := probe)
    else if not finished then (
      Hashtbl.replace dead key (if probe.stopped = None then Some axioms else None);
      release key)
    else if lane.restart then (
      let best =
        match Hashtbl.find_opt completed key with
        | Some (b, n) when n = axioms -> max b budget
        | _ -> budget
      in
      Hashtbl.replace completed key (best, axioms);
      release key);
    (* After the measured work: the live probes' part of the continuing engine's reading. *)
    probes_part := probes_total ();
    stats.probe_seconds <- stats.probe_seconds +. (Telemetry.now () -. before)
  in
  let probe_turn position index budget fresh =
    let lane = lanes.(position) in
    let key = Slices.key position lane and axioms = List.length main.axioms in
    (match Hashtbl.find_opt dead key with
    | Some (Some n) when axioms > n ->
        Hashtbl.remove dead key;
        stats.probe_revived <- stats.probe_revived + 1
    | _ -> ());
    if not (Hashtbl.mem dead key) then
      if policy.carry then (
        (* Resumed lanes only ([Slices.validate]); a dead lane accrues no budget. *)
        lane_target.(position) <- lane_target.(position) + budget;
        let owed = lane_target.(position) - lane_done.(position) in
        if owed > 0 then run_probe position index owed fresh)
      else
        match Hashtbl.find_opt completed key with
        | Some (b, n) when lane.restart && budget <= b && n = axioms ->
            stats.probe_skipped <- stats.probe_skipped + 1
        | _ -> run_probe position index budget fresh
  in
  let main_slice budget =
    if policy.carry then (
      main_target := !main_target + budget;
      let owed = !main_target - !main_done in
      if owed > 0 then run_main (Some owed))
    else run_main (Some budget)
  in
  (* After the continuing engine ended on its own, whether lane [position] can still run: not when
     it is dead (the continuing engine's axioms no longer grow, so a saturated lane stays
     saturated), nor when it is a restart lane that already completed the largest budget the
     sequence gives on these axioms (each later slice of it would replay that search). *)
  let lane_open position =
    let lane = lanes.(position) in
    let key = Slices.key position lane in
    (not (Hashtbl.mem dead key))
    &&
    match Hashtbl.find_opt completed key with
    | Some (b, n) ->
        not (lane.restart && n = List.length main.axioms && b >= Slices.max_probe_steps policy)
    | None -> true
  in
  let lanes_open () = List.exists lane_open (List.init (Array.length lanes) Fun.id) in
  let over () = cancelled () || Deadline.expired_now main.deadline in
  let rec go n =
    if !selected == main then
      if main_alive () then (
        (match Slices.slice policy n with
        | Main steps -> main_slice steps
        | Rest -> run_main None
        | Probe { lane; index; steps; fresh } -> probe_turn lane index steps fresh);
        go (n + 1))
      else if (not (proved () || over ())) && lanes_open () then (
        Engine.release main;
        main_counts := false;
        alone n)
  (* The lanes alone, after the continuing engine ended on its own: its slices are skipped. *)
  and alone n =
    if !selected == main && (not (over ())) && lanes_open () then
      match Slices.slice policy n with
      | Main _ -> alone (n + 1)
      | Rest -> ()
      | Probe { lane; index; steps; fresh } ->
          let slices = stats.probe_slices and work = stats.probe_work in
          probe_turn lane index steps fresh;
          stats.alone_slices <- stats.alone_slices + stats.probe_slices - slices;
          stats.alone_work <- stats.alone_work + stats.probe_work - work;
          alone (n + 1)
  in
  Fun.protect
    ~finally:(fun () ->
      main.heap_reading <- main_reading;
      Hashtbl.fold (fun key (probe, _) acc -> (key, probe) :: acc) engines []
      |> List.iter (fun (key, probe) ->
          if probe == !selected then Engine.seal probe else release key))
    (fun () -> go 0)

(* Polls of the main enumeration's guard (16 raw candidates each) on this Domain, counted only
   for the probe lane's [Events] clock (the lane's own look-ahead counts its polls itself). *)
let main_polls : int ref Domain.DLS.key = Domain.DLS.new_key (fun () -> ref 0)

(* The lane-clock evaluation knob ([Probe_lane.config.main_pad]): run [steps] (one main-engine
   turn), then spin [time] times as long as it took and allocate [alloc] times as many
   short-lived words as it allocated, so that the main engine looks slower, or allocation-heavier,
   for the same search. Measurements only. *)
let padded (c : Probe_lane.config) = fst c.main_pad > 0. || snd c.main_pad > 0.

let padded_turn (c : Probe_lane.config) steps =
  let time, alloc = c.main_pad in
  let t0 = Telemetry.now () and a0 = Telemetry.allocated_words () in
  steps ();
  let elapsed = Telemetry.now () -. t0 and words = Telemetry.allocated_words () -. a0 in
  (if alloc > 0. then
     let blocks = int_of_float (alloc *. words /. 8.) in
     for _ = 1 to blocks do
       ignore (Sys.opaque_identity (Array.make 7 0))
     done);
  if time > 0. then (
    let until = Telemetry.now () +. (time *. elapsed) in
    let spins = ref 0 in
    while Telemetry.now () < until do
      incr spins
    done;
    ignore (Sys.opaque_identity !spins))

(** [on_proof] runs once, when the search has derived the empty clause and before the proof is
    extracted and checked (a process worker uses it to tell its supervisor that a report with a
    proof is on its way). [prepare] runs on every engine of the worker right after it is created:
    the continuing engine, and each probe engine of a sliced worker (a test seam, e.g. for the
    memory budget's heap reading) and each engine of the schema probe lane. [workers] is the run's
    number of heuristic workers: the lane of worker [worker_id] takes the indices
    [= worker_id (mod workers)] of a condition prior (an experiment hook that no default sets). *)
let run_search ?profile ?(history = []) ?(worker_id = 0) ?(workers = 1)
    ?(cancelled = fun () -> false) ?(on_instance = fun _ -> ()) ?(on_proof = fun () -> ())
    ?(prepare = fun _ -> ()) (config : config) theory =
  let started = Telemetry.now () in
  if
    config.max_size < 0 || config.parameters < 0 || config.max_instances < 0
    || config.max_guided_instances < 0 || config.quantum < 1 || config.phase_base < 0
    || queue_phase config ~worker_id < 0
  then invalid_arg "invalid scheduler bound";
  let arena = Theory.arena theory in
  let guided_enabled =
    config.guided && config.max_guided_instances > 0 && Theory.schemas theory <> []
  in
  let guidance, engine =
    Pipeline_profile.stage profile "engine_setup" (fun () ->
        let guidance = Guided.create ~config:config.guidance arena in
        let on_active = if guided_enabled then Guided.observe guidance else fun _ -> () in
        let engine =
          Engine.create ~phase:(queue_phase config ~worker_id) ~cancelled ~on_active
            ~on_conflict:(fun ~guard steps ->
              if guided_enabled then Guided.feedback ~guard guidance steps)
            ~on_demand:(fun ~guard clause ->
              if guided_enabled then Guided.request ~guard guidance clause)
            ~on_collect:(Guided.collect guidance) config.engine
        in
        prepare engine;
        (guidance, engine))
  in
  (* An engine of this worker's schema probe lane reads its own footprint plus the continuing
     engine's, and whichever engine runs answers the pressure with its own cursors and clauses;
     the continuing engine reads its own footprint. Both readings are engine counts. Probe slices
     read the worker's state by [sliced_search]'s rule instead. *)
  let probe_prepare (e : Engine.t) =
    e.heap_reading <- (fun () -> Engine.footprint e + Engine.footprint engine);
    prepare e
  in
  Pipeline_profile.stage profile "initial_axioms" (fun () ->
      (if guided_enabled then
         try Guided.seed ~guard:(fun () -> Engine.check_time engine) guidance history
         with Engine.Stop -> ());
      Engine.add_initial_axioms engine (Theory.fixed theory));
  let bounds : Theory.Schema.bounds option =
    if config.max_size = 0 then None
    else Some { max_size = config.max_size; parameters = config.parameters }
  in
  let streams =
    Theory.schemas theory
    |> List.map (fun schema -> (schema, ref (Theory.enumerate theory ?bounds schema), ref false))
  in
  (* (schema, parameter) -> the generator that first injected it. *)
  let seen = Hashtbl.create 64 in
  (* Instances the probe lane used before the main engine injected them. They
     are already counted in their generator's budget, so injecting one later
     is free: main engine and lane together stay within the budgets. With the
     lane off this table stays empty. *)
  let lane_charged = Hashtbl.create 64 in
  (* Injected instances by axiom id, so a withdrawn one can be added again, and
     the instances the memory budget withdrew, oldest first. *)
  let injected = Hashtbl.create 64 and withdrawn = Queue.create () in
  let next = ref (List.length (Theory.fixed theory))
  and count = ref 0
  and guided_count = ref 0
  and traces = ref [] in
  let schemas =
    List.map
      (fun schema ->
        {
          schema;
          candidates = 0;
          injected = 0;
          max_size = 0;
          max_parameters = 0;
          exhaustive_candidates = 0;
          guided_candidates = 0;
          exhaustive_injected = 0;
          guided_injected = 0;
        })
      (Theory.schemas theory)
  in
  let add generator schema phi =
    let axiom = Theory.instantiate_parameter theory ~id:!next schema phi in
    incr next;
    let trace = { axiom; predicate = Theory.parameter_text theory phi; generator } in
    traces := trace :: !traces;
    on_instance trace;
    Hashtbl.replace injected axiom.axiom_id (generator, schema, phi);
    Engine.add_axiom ~releasable:true engine axiom;
    axiom
  in
  let lane = ref None in
  let inject generator schema phi =
    let counter, limit =
      match generator with
      | Exhaustive -> (count, config.max_instances)
      | Guided -> (guided_count, config.max_guided_instances)
    in
    let stats = List.find (fun s -> s.schema = schema) schemas in
    stats.candidates <- stats.candidates + 1;
    (match generator with
    | Exhaustive -> stats.exhaustive_candidates <- stats.exhaustive_candidates + 1
    | Guided -> stats.guided_candidates <- stats.guided_candidates + 1);
    let size, parameters = Theory.parameter_info theory schema phi in
    stats.max_size <- max stats.max_size size;
    stats.max_parameters <- max stats.max_parameters parameters;
    let charged = Hashtbl.mem lane_charged (schema, phi) in
    if
      engine.root = None && engine.stopped = None
      && (charged || !counter < limit)
      && not (Hashtbl.mem seen (schema, phi))
    then (
      stats.injected <- stats.injected + 1;
      (match generator with
      | Exhaustive -> stats.exhaustive_injected <- stats.exhaustive_injected + 1
      | Guided -> stats.guided_injected <- stats.guided_injected + 1);
      Hashtbl.add seen (schema, phi) generator;
      if not charged then incr counter;
      let axiom = add generator schema phi in
      Option.iter (fun l -> Probe_lane.offer ~formula:axiom.formula l schema phi) !lane)
  in
  (* Probe-lane budget hook: an instance the lane probes before the main
     engine injects it is charged to the same per-generator budget (look-ahead
     instances to the exhaustive one, prior conditions to the guided one). *)
  let admit (source : Probe_lane.source) schema phi : Probe_lane.admission =
    if Hashtbl.mem seen (schema, phi) || Hashtbl.mem lane_charged (schema, phi) then Free
    else
      let counter, limit =
        match source with
        | Prior | Observed ->
            (guided_count, if guided_enabled then config.max_guided_instances else 0)
        | Scanned | Injected -> (count, config.max_instances)
      in
      if !counter < limit then (
        incr counter;
        Hashtbl.replace lane_charged (schema, phi) ();
        Charged)
      else Refused
  in
  (* Schema probe lane: bounded, isolated refutation attempts next to the main
     saturation, inside [config.lane.share] of the run's work and inside the
     search's instance bounds. Its engines are created from this worker's
     engine configuration (strategy and memory budgets included), at this
     worker's queue phase, and [prepare] runs on each of them. Off, or for a
     theory without schemas, the search below is exactly the main search. *)
  lane :=
    if config.lane.enabled && Theory.schemas theory <> [] then
      Some
        (Probe_lane.create ~worker:worker_id ~workers ~phase:(queue_phase config ~worker_id)
           ~cancelled ~prepare:probe_prepare ?bounds ~synthesis:guided_enabled ~admit ~started
           ?main_events:
             (match config.lane.clock with
             | Probe_lane.Allocation -> None
             | Events ->
                 (* The continuing engine's events: its generated and given clauses and the
                    polls (16 raw candidates each) of the main enumeration. *)
                 Some (fun () -> (Probe_lane.engine_events engine, !(Domain.DLS.get main_polls))))
           ~inject:(fun source schema p ->
             (* A failed lane killer: already charged, so this is free. *)
             inject
               (match source with Prior | Observed -> Guided | Scanned | Injected -> Exhaustive)
               schema p)
           config.lane config.engine theory)
    else None;
  let lane_found () = match !lane with Some l -> Probe_lane.found l | None -> false in
  let lane_has_work () = match !lane with Some l -> Probe_lane.has_work l | None -> false in
  let collect_withdrawn () =
    while not (Queue.is_empty engine.released) do
      let id = Queue.take engine.released in
      Option.iter
        (fun x ->
          Hashtbl.remove injected id;
          Queue.add x withdrawn)
        (Hashtbl.find_opt injected id)
    done
  in
  (* Withdrawn instances return once the pressure that withdrew them is
     relieved and the budget's reading is back at half the budget
     (Engine.holds_instances), or as soon as the worker has nothing else to do.
     While some wait,
     the streams wait as well: a withdrawal shows that the worker cannot hold
     more instance clauses, and enumerating on would only feed the next one.
     Until the budget withdraws an instance, enumeration keeps its pace. *)
  let held () = Engine.holds_instances engine && Engine.ordinary_has_work engine in
  let waiting () =
    collect_withdrawn ();
    (not (Queue.is_empty withdrawn)) && held ()
  in
  let has_withdrawn () =
    collect_withdrawn ();
    (not (Queue.is_empty withdrawn)) && not (held ())
  in
  let has_stream () =
    !count < config.max_instances
    && List.exists (fun (_, _, done_) -> not !done_) streams
    && not (waiting ())
    || has_withdrawn ()
  in
  let has_guidance () =
    guided_enabled && !guided_count < config.max_guided_instances && Guided.has_work guidance
  in
  (* Exhaustive enumeration is a ready operation with a reserved exploration
     turn. It shares work scheduling, never the guided instance budget. One
     step may scan many raw conditions; Enumerate polls the engine's time and
     cancellation check on every 16th of them, so neither waits for the step. *)
  let enumerate () =
    (* Withdrawn instances return ahead of the streams, as many per turn as there
       are streams, and the streams advance as usual: the budget never slows
       enumeration. *)
    List.iter
      (fun _ ->
        if has_withdrawn () && engine.root = None && engine.stopped = None then (
          let generator, schema, phi = Queue.take withdrawn in
          engine.metrics.budget_reinjected <- engine.metrics.budget_reinjected + 1;
          ignore (add generator schema phi)))
      (if streams = [] then [ () ] else List.map ignore streams);
    List.iter
      (fun (schema, seq, done_) ->
        Engine.check_time engine;
        if (not !done_) && !count < config.max_instances then
          match
            match config.lane.clock with
            | Probe_lane.Allocation ->
                Telemetry.with_stage engine.timing "enumeration" (fun () ->
                    Enumerate.with_guard (fun () -> Engine.check_time engine) !seq)
            | Events ->
                Telemetry.with_stage engine.timing "enumeration" (fun () ->
                    Enumerate.with_guard
                      (fun () ->
                        incr (Domain.DLS.get main_polls);
                        Engine.check_time engine)
                      !seq)
          with
          | Seq.Nil -> done_ := true
          | Seq.Cons (phi, rest) ->
              seq := rest;
              Option.iter (inject Exhaustive schema) phi)
      streams
  in
  let synthesize () =
    try
      Telemetry.with_stage engine.timing "guidance" (fun () ->
          let guard () = Engine.check_time engine in
          Guided.pump ~guard ~is_live:(Index.mem engine.index) guidance;
          let remaining = ref config.guidance.proposals_per_cycle in
          while
            !remaining > 0
            && !guided_count < config.max_guided_instances
            && engine.root = None && engine.stopped = None
          do
            decr remaining;
            match
              Guided.take ~guard
                ~eligible:(fun phi ->
                  List.exists
                    (fun (schema, _, _) ->
                      match Theory.guided_parameter theory schema phi with
                      | None -> false
                      | Some p -> not (Hashtbl.mem seen (schema, p)))
                    streams)
                guidance
            with
            | None -> remaining := 0
            | Some phi ->
                List.iter
                  (fun (schema, _, _) ->
                    Option.iter (inject Guided schema) (Theory.guided_parameter theory schema phi))
                  streams
          done)
    with Engine.Stop -> ()
  in
  let main_ready () = has_stream () || has_guidance () || Engine.has_work engine in
  (* The worker lives while its continuing engine or its probe lane has work
     and neither has found a proof; without a lane this is [main_ready]. *)
  let main_alive () =
    engine.root = None && engine.stopped = None
    && (not (lane_found ()))
    && (main_ready () || lane_has_work ())
  in
  (* One turn of the continuing engine: [config.quantum] engine steps unless
     the time check stops it first. Returns the steps taken. Memory pressure
     never withholds guidance. Instance clauses are releasable, so the budget
     withdraws them like derived clauses and they come back through [enumerate];
     while withdrawn ones wait, so do the streams. With a probe lane, the lane
     first takes a turn when it is due (within its share of the work), or
     whenever the continuing engine has nothing left; a lane turn alone counts
     as one step. *)
  let main_steps () =
    for _ = 1 to config.quantum do
      if waiting () then engine.metrics.budget_deferred <- engine.metrics.budget_deferred + 1;
      Engine.step
        ?synthesize:(if has_guidance () then Some synthesize else None)
        ?enumerate:(if has_stream () then Some enumerate else None)
        engine
    done
  in
  let main_turn () =
    (try Engine.check_time engine with Engine.Stop -> ());
    let lane_turned =
      match !lane with
      | Some l when engine.stopped = None && ((not (main_ready ())) || Probe_lane.due l) ->
          Probe_lane.turn l;
          true
      | _ -> false
    in
    if engine.stopped <> None then 0
    else if Option.is_some !lane && (lane_found () || not (main_ready ())) then
      if lane_turned then 1 else 0
    else (
      if Option.is_some !lane && padded config.lane then padded_turn config.lane main_steps
      else main_steps ();
      config.quantum)
  in
  let slices = single_slices ~workers ~schemas:(Theory.schemas theory <> []) config in
  let slice_stats = Slices.stats slices in
  (* The engine whose refutation is reported: the continuing engine unless a
     probe slice closed the search first. *)
  let selected = ref engine in
  (* A proof outside the probe slices: the continuing engine's or the schema probe lane's. *)
  let proved () = engine.root <> None || lane_found () in
  Pipeline_profile.stage profile "search" (fun () ->
      if not (Slices.enabled slices) then
        while main_alive () do
          ignore (main_turn ())
        done
      else
        sliced_search
          ~config:{ config with slices = Some slices }
          ~worker_id ~cancelled ~prepare ~fixed:(Theory.fixed theory) ~stats:slice_stats
          ~main:engine ~main_alive ~main_turn ~proved ~selected;
      Engine.seal engine);
  let continuing = engine and engine = !selected in
  (* A lane proof was extracted by the lane; it is checked below like any other. *)
  let lane_certificate = match !lane with Some l -> l.result | None -> None in
  if engine.root <> None || Option.is_some lane_certificate then on_proof ();
  let certificate =
    match lane_certificate with
    | Some _ as found -> found
    | None ->
        Pipeline_profile.stage profile "proof_extract" (fun () ->
            Engine.certificate engine ~theory:(Theory.name theory))
  in
  let replay_seconds =
    match certificate with
    | None -> 0.
    | Some cert -> (
        let before = Telemetry.now () in
        match Pipeline_profile.stage profile "proof_check" (fun () -> Kernel.check theory cert) with
        | Ok _ -> Telemetry.now () -. before
        | Error e -> failwith (rejected_search_proof e))
  in
  let lane_note = match !lane with Some l -> Probe_lane.summary l | None -> "" in
  (* The probe slices that ran on after the continuing engine ended on its own. *)
  let alone_note =
    if slice_stats.alone_slices = 0 || Option.is_some certificate then ""
    else
      "; "
      ^ String.concat ", " (List.sort_uniq compare (List.map Slices.lane_name slices.lanes))
      ^ " ran on alone"
  in
  let reason =
    (fun r -> r ^ alone_note ^ lane_note)
    @@
    match certificate with
    | Some _ -> "refutation verified"
    | None ->
        if engine.stopped <> None then Engine.reason engine
        else if !count >= config.max_instances && streams <> [] then
          "schema instance limit" ^ Engine.trimming_note engine ^ "; no refutation found"
        else
          "bounded formula/clauses exhausted" ^ Engine.trimming_note engine
          ^ "; consistency not established"
  in
  let used_axioms, used_instances, proof_steps =
    match certificate with
    | None -> (0, 0, 0)
    | Some c ->
        ( List.length c.axioms,
          List.length (List.filter (fun (a : Wire.axiom) -> Wire.is_instance a.origin) c.axioms),
          fst (Proof.statistics c) )
  in
  let used_ids =
    match certificate with
    | None -> []
    | Some c -> List.map (fun (a : Wire.axiom) -> a.axiom_id) c.axioms
  in
  let guided_used =
    (* A lane certificate numbers its instance in the lane's own ID space:
       count it when it came from the guided budget (a prior condition, or
       an instance the main engine's guidance injected). *)
    if Option.is_some lane_certificate then
      match Option.bind !lane (fun (l : Probe_lane.t) -> l.winning) with
      | Some { source = Prior | Observed; _ } -> 1
      | Some { source = Injected; schema; parameter; _ } ->
          if Hashtbl.find_opt seen (schema, parameter) = Some Guided then 1 else 0
      | _ -> 0
    else
      List.length
        (List.filter
           (fun trace -> trace.generator = Guided && List.mem trace.axiom.axiom_id used_ids)
           !traces)
  in
  let worker =
    {
      worker_id;
      strategy = config.engine.strategy;
      engine;
      certificate;
      schemas;
      reference_tested = 0;
      replay_seconds;
      used_axioms;
      used_instances;
      proof_steps;
      reason;
      guidance = guidance.metrics;
      guided_enabled;
      guided_compounds = config.guidance.compounds;
      guided_used;
      slices = slice_stats;
      continuing;
      lane = Option.map (fun (l : Probe_lane.t) -> l.stats) !lane;
    }
  in
  {
    certificate;
    reason;
    engine;
    traces = List.rev !traces;
    reference_tested = 0;
    replay_seconds;
    worker_id;
    workers = [ worker ];
    wall_seconds = Telemetry.now () -. started;
    proof_source =
      (if Option.is_some lane_certificate then "probe:" else "heuristic:") ^ string_of_int worker_id;
    reference_report = None;
    (* For a lane proof: the axioms its certificate actually uses. *)
    axioms = (match lane_certificate with Some c -> c.axioms | None -> engine.axioms);
    cnf_mode = config.engine.cnf_mode;
    processes = None;
  }

let validate ~workers config =
  if workers < 1 || workers > 64 then invalid_arg "workers must be between 1 and 64";
  Probe_lane.validate (config : config).lane;
  if config.reference_only && not config.reference then
    invalid_arg "reference-only conflicts with no-reference";
  if (not config.reference) && config.reference_config.checkpoint <> None then
    invalid_arg "reference-checkpoint requires the reference worker"

(** The one place where each heuristic worker's complete configuration is resolved. Both portfolios
    call it once, after [validate] and before any worker starts (in process mode, before the first
    fork), and run worker [i] with element [i], so a bad per-worker setting is an error of the
    caller and a forked child receives its final settings by value. Worker [i] runs the strategy and
    the queue phase that [Strategy.resolve config.portfolio] gives it, with [config.engine.strategy]
    as the base, plus the internal phase base (0 by default): its worker id for a production-queue
    strategy, its copy index for a ported E heuristic. Probe slices ([config.slices]) apply only to
    a single heuristic worker: with two or more workers the workers cover queue phases in parallel
    and every worker runs [Slices.off]. A single worker keeps [config.slices]; when that is the
    portfolio default ([None]), [run_search] applies [single_slices], the one per-worker choice that
    depends on the input (whether it has schemas), as the schema probe lane does. Every other
    setting is [config]'s. Per-worker settings (strategies, phases, slices, budgets) belong here and
    nowhere else. *)
let worker_configs ~workers (config : config) =
  List.map
    (fun (w : Strategy.worker) ->
      let slices = if workers = 1 then config.slices else Some Slices.off in
      {
        config with
        engine = { config.engine with strategy = with_unfold config w.strategy };
        slices;
        worker_phase = Some (config.phase_base + w.phase);
      })
    (Strategy.resolve config.portfolio ~base:config.engine.strategy ~workers)

(** The workers of the resolved portfolio that repeat an earlier worker's search, each with the
    earlier worker: the same strategy at a queue phase congruent modulo the strategy's period
    ([Strategy.queue_period] for the engine's weight ratio and clause weight). Ported E heuristics
    never appear ([Strategy.resolve] refuses their repeats); production-queue workers can (the
    production turns repeat every 22 phases), and such a worker adds no new search: at most the
    wall-clock scheduling costs tell it apart. *)
let repeated_workers ~workers (config : config) =
  let keys =
    List.mapi
      (fun i (c : config) ->
        let s = c.engine.strategy in
        let period =
          Strategy.queue_period ~policy:c.engine.clause_weight ~ratio:c.engine.weight_ratio s
        in
        (i, (s.name, queue_phase c ~worker_id:i mod period)))
      (worker_configs ~workers config)
  in
  List.filter_map
    (fun (i, k) ->
      Option.map (fun (j, _) -> (i, j)) (List.find_opt (fun (j, k') -> j < i && k' = k) keys))
    keys

(** The largest worker count up to [workers] at which every worker of [config]'s portfolio runs its
    own search (44 for the default balanced rule: the production half repeats from 23 production
    workers on; 22 for all production). *)
let distinct_workers ~workers config =
  let rec go w =
    if w < workers && repeated_workers ~workers:(w + 1) config = [] then go (w + 1) else w
  in
  if repeated_workers ~workers:1 config <> [] then 0 else go 1

(** The CLI's warning for [repeated_workers], or [None] when every worker runs its own search. *)
let repeat_warning ~workers config =
  match repeated_workers ~workers config with
  | [] -> None
  | repeats ->
      let configs = Array.of_list (worker_configs ~workers config) in
      let names =
        List.sort_uniq compare
          (List.map (fun (i, _) -> configs.(i).engine.strategy.Strategy.name) repeats)
      in
      Some
        (Printf.sprintf
           "Warning: %d of %d workers repeat another worker's search (%s at a queue phase \
            congruent modulo the strategy's period); this portfolio runs distinct searches up to \
            %d workers"
           (List.length repeats) workers (String.concat ", " names)
           (distinct_workers ~workers config))

let portfolio ?profile ?(history = []) ?(workers = 1) ?(cancelled = fun () -> false)
    ?(on_instance = fun _ -> ()) config make_theory =
  validate ~workers config;
  let configs = worker_configs ~workers config in
  let started = Telemetry.now () and stop = Atomic.make false in
  let cancelled () = cancelled () || Atomic.get stop in
  (* Construct manifests before spawning: factories need not be thread safe. *)
  let theories =
    if config.reference_only then [] else List.init workers (fun _ -> make_theory ())
  in
  let reference_theory = if config.reference then Some (make_theory ()) else None in
  let protect f () =
    try Ok (f ())
    with exn ->
      Atomic.set stop true;
      Error exn
  in
  let reference =
    Option.map
      (fun theory ->
        Domain.spawn
          (protect (fun () ->
               let r = Reference.run_certified ~cancelled config.reference_config theory in
               if r.certificate <> None then Atomic.set stop true;
               r)))
      reference_theory
  in
  let work i theory () =
    (* Only the sequential, single heuristic worker shares the CLI profiler.
       Parallel portfolios retain their existing per-worker engine counters. *)
    let profile = if workers = 1 then profile else None in
    let result =
      run_search ?profile ~history ~worker_id:i ~workers ~cancelled ~on_instance
        (List.nth configs i) theory
    in
    if result.certificate <> None then Atomic.set stop true;
    result
  in
  let outcomes =
    match theories with
    | [ theory ] -> [ protect (work 0 theory) () ]
    | theories ->
        let domains = ref [] in
        let error =
          try
            List.iteri
              (fun i theory -> domains := Domain.spawn (protect (work i theory)) :: !domains)
              theories;
            []
          with exn ->
            Atomic.set stop true;
            [ Error exn ]
        in
        List.map Domain.join (List.rev !domains) @ error
  in
  (* Join every worker before propagating any error or returning a proof. *)
  let reference_report = Option.map Domain.join reference in
  let results = List.map (function Ok r -> r | Error e -> raise e) outcomes in
  let reference_report = Option.map (function Ok r -> r | Error e -> raise e) reference_report in
  let chosen =
    match List.find_opt (fun r -> r.certificate <> None) results with
    | Some r -> r
    | None -> (
        match results with
        | r :: _ -> r
        | [] ->
            (* API compatibility: no heuristic worker ran; the carrier engine is empty
         and is never included in worker metrics. *)
            let engine = Engine.create config.engine in
            Engine.seal engine;
            {
              certificate = None;
              reason = "reference only";
              engine;
              traces = [];
              reference_tested = 0;
              replay_seconds = 0.;
              worker_id = -1;
              workers = [];
              wall_seconds = 0.;
              proof_source = "reference";
              reference_report = None;
              axioms = [];
              cnf_mode = Wire.Hybrid;
              processes = None;
            })
  in
  let chosen =
    match (chosen.certificate, reference_report) with
    | None, Some r when r.certificate <> None ->
        {
          chosen with
          certificate = r.certificate;
          reason = r.reason;
          worker_id = -1;
          proof_source = "reference";
          replay_seconds = r.replay_seconds;
          axioms = r.axioms;
          cnf_mode = (Option.get r.certificate).cnf_mode;
        }
    | None, Some r when config.reference_only ->
        { chosen with reason = r.reason; axioms = r.axioms }
    | None, Some r -> { chosen with reason = chosen.reason ^ "; " ^ r.reason }
    | _ -> chosen
  in
  {
    chosen with
    proof_source = (if chosen.certificate = None then "none" else chosen.proof_source);
    workers = List.concat_map (fun r -> r.workers) results;
    reference_report;
    reference_tested = (match reference_report with None -> 0 | Some r -> r.tested);
    wall_seconds = Telemetry.now () -. started;
  }

let run ?history ?(worker_id = 0) ?cancelled ?on_instance config theory =
  if worker_id <> 0 then invalid_arg "use portfolio for numbered workers";
  portfolio ?history ?cancelled ?on_instance config (fun () -> Theory.copy theory)
