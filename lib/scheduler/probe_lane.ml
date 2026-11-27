(* Schema probe lane: isolated, bounded refutation attempts that run next to
   the main saturation of a schema theory, inside a bounded share of its work.

   Why: in a schema theory the main engine receives hundreds of instances per
   second. When one instance (or none) together with the fixed axioms is
   already contradictory, that small refutation drowns in the main saturation.
   The lane runs fresh engines on small axiom sets instead, in sub-lanes that
   share the lane by least cumulative work:

   - fixed:     the fixed axioms alone, one persistent engine resumed in
                geometrically growing work slices (never restarted);
   - instance:  fixed axioms + one instance (instances the main engine
                injected, plus a look-ahead over the schema streams). With
                [breadth] the pending instances are grouped by schema and by
                shape (the multiset of connectives, quantifiers and symbols of
                the instance formula): every schema gets an equal share of the
                probe work, and no shape more than [shape_cap] of its schema's
                work while instances of other shapes wait; inside a shape,
                arrival order. Without [breadth], plain arrival order. With
                the optional finite-model pool, instances false in every pool
                model ("killers") are probed with a larger budget, but
                non-killer probes keep a fixed share of the sub-lane, and a
                pool that calls too many candidates killers stops ranking.
                Inside this sub-lane, at most [oe_share] of its work goes to
                the observational source ([observational], on by default):
                the theory's own formulas enumerated bottom-up, one per truth
                table over the pool (Observational), offered to every schema;
                their pool killers are probed from level 0 (see "observational
                source" below). It is a semantic order on the theory's own
                formula language, not a condition prior. As evaluation
                options, non-killer probes that stop with engine work left
                can be retried at doubling budgets inside [luby_share] of
                the sub-lane ("re-probes of non-killers" below), and the
                pool can be built by SAT (Mace, [mace]), which also
                pre-checks the observational killers for small
                counter-models ([candidate] sets both);
   - prior:     fixed axioms + one condition of a caller-supplied condition
                stream ([prior]), re-probed with escalating budgets. No preset
                sets this hook: it exists for experiments (the schema
                benchmark plugs its Lawvere-style diagonal prior in here);
                axiom-fuzz never sets it.

   Failed pool killers may enter the main engine.

   Search bounds. The lane uses only schema instances inside the search's
   instance budgets: the caller's [admit] hook charges every instance a probe
   uses that the main engine has not injected (look-ahead instances to the
   exhaustive budget, prior and observational conditions to the guided
   budget) and refuses it when that budget is spent. The look-ahead enumerates the main search's
   streams with the same [bounds], so max_size and parameters bound it exactly
   as they bound the main enumeration, and a condition prior or the
   observational source, both synthesis, run only when guided synthesis is
   enabled ([synthesis]).

   Everything is search-side. A probe certificate is an ordinary Engine
   certificate over the theory's own fixed axioms and at most one schema
   instance with normal provenance; the caller still runs Kernel.check.

   Work unit: one kiloword allocated by the worker's own Domain (OCaml
   minor + major - promoted words, which does not depend on GC timing). The
   engines' clause counters are a poor time proxy here (a large main engine
   spends about 20 times more time per generated clause than a small probe
   engine), while allocation tracks time within a factor of about 1.6 on the
   benchmark. The lane takes a turn only while its cumulative work is at most
   [share] of the work done since the lane started, the main engine's work
   counted at the exchange rate [main_weight]: the default
   ([calibrated_main_weight] below) keeps the lane's wall-time share at the
   one it was designed with, although same-search speed-ups cut the main
   engine's allocation per unit of search. Allocation is a property
   of the computation, not of machine load; the exceptions are the run's own
   time limit, inherited by every probe engine, and the deadline guard of the
   look-ahead and of the model evaluations, which never start an operation
   they predict to end after the deadline. Finite-model work is additionally
   capped in evaluation steps, and every lane engine has a stored-proof-node
   bound (its memory budget). The breadth choice uses the same work units. *)

(* A condition stream over the theory's signature (Free 0 is the principal
   variable), offered to every schema through its [guide]. Experiments only. *)
type prior = Signature.t -> Wire.source Seq.t

(* The lane's work clock. [Allocation] (the default) is described above. [Events] is an
   evaluation option: every quantity is a deterministic search event of the code that does the
   work, converted at fixed exchange rates calibrated once ([ev_*] below), so the split between
   the lane and the main engine, and every probe budget, depends only on the search, not on how
   many words the code allocates for it. Lane engines count their generated and given clauses,
   the look-ahead the raw candidates of its enumeration (Enumerate polls its guard every 16th),
   finite-model work its evaluation steps and the observational source its own steps; the main
   engine counts its generated and given clauses and the raw candidates of its enumeration. A
   same-search speed-up of either side then leaves the interleaving unchanged. *)
type clock = Allocation | Events

type config = {
  enabled : bool;  (** Off: the scheduler runs exactly the main search. *)
  share : float;
      (** The lane's bound (0 < share <= 0.5): it takes a turn while its work is at most [share] of
          the lane's work plus [main_weight] times the main engine's ([due]). That is a fraction
          [share] of the raw work only at [main_weight] 1; at [share] 0.5 the lane's raw work can
          reach [main_weight] times the main engine's, about 0.60 of all work at the default
          [calibrated_main_weight] 1.5. *)
  fixed : bool;  (** Probe the fixed axioms alone. *)
  fixed_slice : int;  (** First fixed-probe slice (work units); later slices double ... *)
  fixed_slice_cap : int;  (** ... up to this size. *)
  fixed_late_weight : float;
      (** Weight (above 0, at most 1) of the fixed sub-lane in the least-work choice once its slices
          have reached the cap: the main engine saturates the same fixed axioms, so an isolated copy
          that has not closed early gets a smaller share. *)
  instance_budget : int;  (** Work of one level-0 probe; level l gets budget * 2^l. *)
  escalations : int;  (** Re-probe levels for killers and prior conditions (0: probe once). *)
  killer_level : int;  (** Starting level of pool killers (they are few and promising). *)
  pool : bool;  (** Finite-model ranking (built lazily inside the lane). *)
  pool_budget : int;  (** Evaluation steps for building the pool. *)
  refine_budget : int;  (** Evaluation steps for one counter-model search. *)
  scan : int;  (** Look-ahead candidates per scan turn. *)
  scan_cap : int;
      (** Look-ahead candidates per worker in total (memory bound: every examined candidate's
          parameter and instance are interned in the theory's arena). *)
  breadth : bool;
      (** Spread the instance probes over schemas and shapes (equal schema shares, [shape_cap]);
          off: plain arrival order. *)
  shape_cap : float;
      (** Largest share (above 0, at most 1) of its schema's probe work that one shape may have
          while instances of other shapes of that schema wait ([breadth] only). *)
  prior : prior option;
      (** Caller-supplied condition stream (only with guided synthesis). No preset sets it: the
          library's only condition generator is the observational source (the theory's own formula
          language in a semantic order, no prior), and axiom-fuzz never sets this hook. *)
  prior_cap : int;
      (** Prior indices taken from the stream by each worker's lane; worker i keeps the indices = i
          (mod W) among them, i.e. about cap / W conditions. *)
  retry_cap : int;  (** Pending re-probes kept per sub-lane (memory bound). *)
  inject_failed : bool;  (** Pool killers failing every level enter the main engine. *)
  arrival_share : float;
      (** Minimum fraction (0..1) of the instance sub-lane's probe work that goes to non-killer
          probes while pool killers wait. *)
  weak_pool : float;
      (** Kill rate of the look-ahead above which the pool stops ranking instances: a pool that
          calls this fraction of the examined candidates killers does not discriminate. *)
  probe_retained : int;  (** Stored proof nodes of one probe engine (its memory budget). *)
  fixed_retained : int;  (** Stored proof nodes of the persistent fixed-axiom engine. *)
  turn_steps : int;  (** Model-evaluation steps of one scan or classification turn. *)
  scan_step_cap : int;
      (** A look-ahead step that allocates more than this many work units ends the look-ahead of its
          stream (the main engine still enumerates it and the lane probes what it injects). *)
  observational : bool;
      (** Observational-equivalence condition source ([Observational]): the theory's own formulas,
          one per truth table over the pool, offered to every schema; pool killers are probed (needs
          the ranking pool and guided synthesis). *)
  oe_share : float;
      (** Largest fraction (above 0, at most 1) of the instance sub-lane's work it may take. *)
  oe_bucket : int;  (** Formulas kept per (level, size) bucket of its bank. *)
  oe_words : int;
      (** Footprint cap of its banks in words for the whole run (memory bound): every worker's lane
          keeps its own bank, capped at [oe_words / workers]. *)
  oe_cap : int;
      (** Conditions it offers per worker in total (memory bound: every offered condition and its
          instances are interned in the theory's arena). *)
  clock : clock;  (** Work clock of the lane (evaluation option; default [Allocation]). *)
  main_weight : float;
      (** [Allocation]: exchange rate of the main engine's work in the share test: the lane is due
          while its work is at most [share] of (lane + [main_weight] x main). It recalibrates the
          allocation clock's split without changing its unit. [default] (and [candidate]) use
          [calibrated_main_weight]; [disabled] and the arrival-order ladder ([fifo] ...
          [with_breadth], which reproduce earlier defaults) keep 1. [Events] ignores it: [ev_main]
          is that clock's exchange rate. *)
  ev_main : float;  (** [Events]: work units per main-engine event (clause or 16 raw candidates). *)
  ev_engine : float;  (** [Events]: work units per lane-engine event (generated or given clause). *)
  ev_raw : float;  (** [Events]: work units per look-ahead poll (16 raw enumeration candidates). *)
  luby_share : float;
      (** Re-probes of non-killers (0: off, the default; [candidate]: 1/6): a non-killer probe that
          stopped with engine work left is retried at doubling budgets, inside at most this fraction
          of the instance sub-lane's work; inside that share every level gets equal cumulative work.
      *)
  luby_levels : int;  (** Highest re-probe level of non-killers (budget [instance_budget] x 2^l). *)
  main_pad : float * float;
      (** Evaluation knob (default (0, 0)): after every main-engine turn the worker spins for the
          first factor times the turn's wall time and allocates the second factor times the turn's
          allocation, simulating a main engine that is slower, or allocates more, for the same
          search. Never set outside measurements. *)
  mace : bool;
      (** SAT-based finite models (Mace, SEM-MACE; off by default, on in [candidate]; off, the pool
          samples structures with Semantic): the ranking pool holds non-isomorphic models of a
          maximal satisfiable subset of the fixed axioms, found by the CDCL at sizes 1-4, and
          counter-models are searched by SAT at sizes 1-6. *)
  mace_precheck : int;
      (** With [mace]: steps of a SAT counter-model search run on every observational killer before
          its probe (0: none); a killer with a small model is dropped unprobed and the model refines
          the killer test. *)
}

let disabled =
  {
    enabled = false;
    share = 0.5;
    fixed = false;
    fixed_slice = 2_000;
    fixed_slice_cap = 64_000;
    fixed_late_weight = 0.5;
    instance_budget = 1_000;
    escalations = 5;
    killer_level = 3;
    pool = false;
    pool_budget = 6_000_000;
    refine_budget = 400_000;
    scan = 64;
    scan_cap = 20_000;
    breadth = false;
    shape_cap = 0.25;
    prior = None;
    prior_cap = 20_000;
    retry_cap = 4_096;
    inject_failed = true;
    arrival_share = 0.5;
    weak_pool = 0.25;
    probe_retained = 100_000;
    fixed_retained = 200_000;
    turn_steps = 4_000_000;
    scan_step_cap = 8_000;
    observational = false;
    oe_share = 1. /. 3.;
    oe_bucket = 10_000;
    oe_words = 8_000_000;
    oe_cap = 20_000;
    clock = Allocation;
    main_weight = 1.;
    (* [Events] exchange rates, calibrated once (flambda -O3 release build, one worker, eight
       schema-benchmark cases at 5 s): a lane-engine event (generated or
       given clause, or 1/16 of a goal created or expanded) allocated 0.57 kilowords in total
       over 656 lane-engine runs, so 0.6 units keep a probe's search depth about where the
       allocation clock puts it; a look-ahead poll (16 raw candidates) allocated about 11
       kilowords; at load 16 a unit of the main engine (same rates) took 2.5 times (median;
       2.4-7.7) as long as a lane unit, so [ev_main] = 2.5 gives the lane about half of the
       wall time on the median case. *)
    ev_main = 2.5;
    ev_engine = 0.6;
    ev_raw = 11.;
    luby_share = 0.;
    luby_levels = 5;
    main_pad = (0., 0.);
    mace = false;
    mace_precheck = 400_000;
  }

(* The default's exchange rate of the main engine's allocation. The allocation clock buys the lane
   the wall-time share set by the ratio of the two sides' time per allocated word, so a
   same-search speed-up of the main engine (less allocation per unit of search) shrinks the lane's
   wall-time share at a fixed rate. The rate keeps the lane's share of the wall time in the CLI's
   default run (10 s, one worker) at the one it was designed with, about 0.49 on separation and
   0.65 on zf. It is calibrated with bench/schema/scripts/lane_calibrate.py: per theory a logistic
   fit of the share in ln(rate), two runs per rate, and the rate that minimises the larger of the
   two distances to 0.49 and 0.65, rounded to 0.1. On the flambda -O3 release build with the
   derive rule of equivalence rewriting (Engine.config [equivalence]), 1.5 gives 0.50 and 0.65. A
   constant of the code, so the split stays deterministic for a given build; same-search speed-ups
   of either side, and changes of the main engine's search, move the share again, and the rate
   must then be recalibrated with the same script. *)
let calibrated_main_weight = 1.5

(* The ablation ladder of the schema benchmark (arrival order), and the
   default: fixed axioms, instances spread over schemas and shapes, the
   finite-model pool, the observational-equivalence condition source over
   the theory's own formulas, no condition prior, and the calibrated
   exchange rate. The ladder keeps rate 1: its presets reproduce earlier
   defaults (the schema benchmark's pool-diag and breadth). [candidate] is an
   evaluation candidate: re-probes of non-killers inside 1/6 of the
   instance sub-lane and the pool and counter-models built by SAT (Mace),
   with the observational killers pre-checked for small models. It is not
   the default: on the schema benchmark it lost i-linear-singleton at 30 s
   (the re-probes' share) and i-cantor-injection at 4 workers. *)
let fifo = { disabled with enabled = true }
let fixed_escalate = { fifo with fixed = true }
let with_pool = { fixed_escalate with pool = true }
let with_breadth = { with_pool with breadth = true }
let default = { with_breadth with observational = true; main_weight = calibrated_main_weight }
let candidate = { default with luby_share = 1. /. 6.; mace = true }

let validate c =
  if c.enabled then (
    if not (c.share > 0. && c.share <= 0.5) then invalid_arg "probe lane share must be in (0, 0.5]";
    if
      c.fixed_slice < 1 || c.fixed_slice_cap < c.fixed_slice || c.instance_budget < 1
      || c.escalations < 0 || c.escalations > 16 || c.killer_level < 0
      || c.killer_level > c.escalations || c.pool_budget < 0 || c.refine_budget < 0 || c.scan < 0
      || c.prior_cap < 0 || c.retry_cap < 0
      || (not (c.shape_cap > 0. && c.shape_cap <= 1.))
      || (not (c.fixed_late_weight > 0. && c.fixed_late_weight <= 1.))
      || (not (c.arrival_share >= 0. && c.arrival_share <= 1.))
      || (not (c.weak_pool > 0. && c.weak_pool <= 1.))
      || c.probe_retained < 1 || c.fixed_retained < 1 || c.turn_steps < 1 || c.scan_step_cap < 1
      || c.scan_cap < 0
      || (not (c.oe_share > 0. && c.oe_share <= 1.))
      || c.oe_bucket < 1 || c.oe_words < 0 || c.oe_cap < 0
      || (not (c.main_weight > 0. && c.main_weight <= 100.))
      || (not (c.ev_main > 0. && Float.is_finite c.ev_main))
      || (not (c.ev_engine > 0. && Float.is_finite c.ev_engine))
      || (not (c.ev_raw > 0. && Float.is_finite c.ev_raw))
      || (not (c.luby_share >= 0. && c.luby_share <= 1.))
      || c.luby_levels < 1 || c.luby_levels > 16
      || (not (fst c.main_pad >= 0. && fst c.main_pad <= 10.))
      || (not (snd c.main_pad >= 0. && snd c.main_pad <= 10.))
      || c.mace_precheck < 0
    then invalid_arg "invalid probe lane bound")

(* Evaluation overrides, "key=value,..." (the CLI's AXIOM_LANE and the schema benchmark's
   --lane-set): clock=alloc|events, main_weight=F, ev_main=F, ev_engine=F, ev_raw=F, luby=F
   (share; 0 is off), luby_levels=N, pad=T:A (the main_pad knob), oe=on|off, share=F,
   mace=on|off, mace_precheck=N. The result is validated. *)
let parse_overrides config text =
  let float k v =
    match float_of_string_opt v with
    | Some f when Float.is_finite f -> f
    | _ -> invalid_arg (Printf.sprintf "lane override %s needs a number" k)
  in
  let set c item =
    match String.split_on_char '=' (String.trim item) with
    | [ "" ] -> c
    | [ "clock"; "alloc" ] -> { c with clock = Allocation }
    | [ "clock"; "events" ] -> { c with clock = Events }
    | [ ("main_weight" as k); v ] -> { c with main_weight = float k v }
    | [ ("ev_main" as k); v ] -> { c with ev_main = float k v }
    | [ ("ev_engine" as k); v ] -> { c with ev_engine = float k v }
    | [ ("ev_raw" as k); v ] -> { c with ev_raw = float k v }
    | [ ("luby" as k); v ] -> { c with luby_share = float k v }
    | [ ("luby_levels" as k); v ] -> { c with luby_levels = int_of_float (float k v) }
    | [ ("share" as k); v ] -> { c with share = float k v }
    | [ "mace"; "on" ] -> { c with mace = true }
    | [ "mace"; "off" ] -> { c with mace = false }
    | [ ("mace_precheck" as k); v ] -> { c with mace_precheck = int_of_float (float k v) }
    | [ "oe"; "on" ] -> { c with observational = true }
    | [ "oe"; "off" ] -> { c with observational = false }
    | [ "pad"; v ] -> (
        match String.split_on_char ':' v with
        | [ a; b ] -> { c with main_pad = (float "pad" a, float "pad" b) }
        | _ -> invalid_arg "lane override pad=T:A")
    | _ -> invalid_arg ("unknown lane override " ^ item)
  in
  let c = List.fold_left set config (String.split_on_char ',' text) in
  validate c;
  c

(* Where a probed instance comes from: the main engine, the look-ahead over
   the schema streams, the caller's prior, or the observational source. *)
type source = Injected | Scanned | Prior | Observed

(* The caller's answer when a probe needs an instance the main engine has not
   injected: [Free] (already counted), [Charged] (counted now) or [Refused]
   (the generator's instance budget is spent). *)
type admission = Free | Charged | Refused

type item = {
  schema : Wire.schema;
  parameter : Theory.parameter;
  source : source;
  level : int;
  killer : bool;
  shape : int;  (** Shape class of the instance formula (-1: not computed). *)
}

(* Pending items, grouped by class (schema index, shape) and numbered in
   arrival order. [take_oldest] is arrival order. [take_fair] picks the schema
   with the least probe work, and inside it the oldest item whose shape has at
   most [cap] of the schema's probe work (the least-worked shape when every
   waiting shape is over the cap); inside a class, arrival order. Ties go to
   the oldest item, so the choice is deterministic. *)
module Pending = struct
  type 'a t = {
    classes : (int * int, (int * 'a) Queue.t) Hashtbl.t;
    mutable size : int;
    mutable seq : int;
  }

  let create () = { classes = Hashtbl.create 16; size = 0; seq = 0 }
  let is_empty q = q.size = 0
  let length q = q.size

  let add q cls x =
    (match Hashtbl.find_opt q.classes cls with
    | Some c -> Queue.add (q.seq, x) c
    | None ->
        let c = Queue.create () in
        Queue.add (q.seq, x) c;
        Hashtbl.replace q.classes cls c);
    q.seq <- q.seq + 1;
    q.size <- q.size + 1

  let remove_head q cls =
    let c = Hashtbl.find q.classes cls in
    let _, x = Queue.take c in
    if Queue.is_empty c then Hashtbl.remove q.classes cls;
    q.size <- q.size - 1;
    x

  let head_seq c = fst (Queue.peek c)

  let take_oldest q =
    Hashtbl.fold
      (fun cls c best ->
        let seq = head_seq c in
        match best with Some (s, _) when s <= seq -> best | _ -> Some (seq, cls))
      q.classes None
    |> Option.map (fun (_, cls) -> remove_head q cls)

  let take_fair q ~schema_work ~class_work ~cap =
    let better (w, seq) (w', seq') = w < w' || (w = w' && seq < seq') in
    let schema =
      Hashtbl.fold
        (fun (s, _) c best ->
          let key = (schema_work s, head_seq c) in
          match best with Some (k, _) when not (better key k) -> best | _ -> Some (key, s))
        q.classes None
    in
    match schema with
    | None -> None
    | Some (_, s) ->
        let limit = cap *. schema_work s in
        let within, least =
          Hashtbl.fold
            (fun ((s', _) as cls) c (within, least) ->
              if s' <> s then (within, least)
              else
                let seq = head_seq c and w = class_work cls in
                let within =
                  if w <= limit then
                    match within with Some (o, _) when o <= seq -> within | _ -> Some (seq, cls)
                  else within
                in
                let least =
                  match least with
                  | Some (k, _) when not (better (w, seq) k) -> least
                  | _ -> Some ((w, seq), cls)
                in
                (within, least))
            q.classes (None, None)
        in
        let cls =
          match (within, least) with
          | Some (_, cls), _ | None, Some (_, cls) -> cls
          | None, None -> assert false
        in
        Some (remove_head q cls)

  (* In arrival order. *)
  let iter f q =
    Hashtbl.fold (fun _ c acc -> Queue.fold (fun acc e -> e :: acc) acc c) q.classes []
    |> List.sort (fun (a, _) (b, _) -> compare a b)
    |> List.iter (fun (_, x) -> f x)

  let clear q =
    Hashtbl.reset q.classes;
    q.size <- 0
end

type stats = {
  mutable turns : int;
  mutable probes : int;
  mutable fixed_slices : int;
  mutable fixed_work : float;
  mutable instance_work : float;
  mutable prior_work : float;
  mutable offered : int;
  mutable scanned : int;
  mutable killers : int;
  mutable prior : int;  (** Conditions taken from the prior. *)
  mutable reprobes : int;
  mutable injected : int;
  mutable pool_models : int;
  mutable refined : int;
  mutable charged_exhaustive : int;  (** Look-ahead instances charged to the exhaustive budget. *)
  mutable charged_guided : int;  (** Prior conditions charged to the guided budget. *)
  mutable refused : int;  (** Probes refused because their instance budget was spent. *)
  mutable weak : bool;  (** The pool stopped ranking (too many killers). *)
  mutable expensive_streams : int;  (** Streams whose look-ahead stopped on the step cap. *)
  mutable peak_stored : int;  (** Largest stored proof-node count of a lane engine. *)
  mutable schemas : int;  (** Schemas of the theory. *)
  mutable schemas_probed : int;  (** Distinct schemas with at least one probe. *)
  mutable shapes_probed : int;  (** Distinct (schema, shape) classes with at least one probe. *)
  mutable probe_work : float;  (** Work of all instance probes (any source). *)
  mutable top_schema_work : float;  (** Largest probe work of one schema. *)
  mutable top_shape_work : float;  (** Largest probe work of one (schema, shape) class. *)
  mutable winner : string;
  mutable seconds : float;  (** Wall time inside the lane; reported only, never a budget. *)
  mutable promoted : int;  (** Injected instances the look-ahead moved to the killers. *)
  mutable oe_work : float;  (** Work of the observational source (part of [instance_work]). *)
  mutable oe_offered : int;  (** Conditions it offered to the schemas. *)
  mutable oe_killers : int;  (** Pool killers among their instances. *)
  mutable oe_probes : int;  (** Probes of those killers (re-probes included). *)
  mutable oe_rebuilds : int;  (** Banks rebuilt after a counter-model refined the pool. *)
  mutable oe_kept : int;  (** Formula classes kept, over all its banks. *)
  mutable oe_words : int;  (** Largest bank footprint (words). *)
  mutable oe_steps : int;
      (** Enumeration and evaluation steps of the source (Observational unit). *)
  mutable oe_evaluations : int;  (** Model-evaluation steps of its killer tests and refinements. *)
  mutable oe_seconds : float;  (** Wall time of its turns; reported only, never a budget. *)
  mutable luby_probes : int;  (** Re-probes of non-killers ([luby_share]). *)
  mutable mace_rejected : int;  (** Observational killers dropped by the SAT pre-check. *)
  mutable luby_work : float;  (** Their work (part of [instance_work]). *)
  mutable ev_engine_events : int;  (** [Events]: generated + given clauses of the lane engines. *)
  mutable ev_engine_alloc : float;  (** [Events]: allocation units of the lane engines' runs. *)
  mutable ev_polls : int;  (** [Events]: polls (16 raw candidates each) of the look-ahead. *)
  mutable ev_poll_alloc : float;
      (** [Events]: allocation units of the look-ahead's stream steps. *)
  mutable ev_capped : int;  (** [Events]: lane-engine runs stopped by the allocation safety net. *)
}

(* A look-ahead stream: the main search's schema stream (same bounds), read
   by the lane's own cursor. *)
type stream = {
  s_schema : Wire.schema;
  mutable s_seq : Theory.parameter option Seq.t;
  mutable s_done : bool;
  mutable s_seconds : float;  (** Wall time of its last step: the deadline predictor. *)
}

type t = {
  config : config;
  theory : Theory.t;
  engine_config : Engine.config;
  started : float;
  deadline : float;
  work_start : float;
  phase : int;
  worker : int;
  workers : int;
  cancelled : unit -> bool;
  prepare : Engine.t -> unit;
  synthesis : bool;
  admit : source -> Wire.schema -> Theory.parameter -> admission;
  inject : source -> Wire.schema -> Theory.parameter -> unit;
  finite : Signature.t option;
  fixed_axioms : Wire.axiom list;
  probe_id : int;
  queued : (Wire.schema * Theory.parameter, unit) Hashtbl.t;
  fresh : item Pending.t;
  waiting : (Wire.schema * Theory.parameter, unit) Hashtbl.t;
      (** Instances the main engine injected that wait unprobed in [fresh]. *)
  killers : item Pending.t;
  prior_retry : item Pending.t;
  prior_killers : item Pending.t;
  prior_backlog : item Pending.t;
  schema_index : (Wire.schema, int) Hashtbl.t;
  schema_work : float array;  (** Probe work per schema index. *)
  class_work : (int * int, float) Hashtbl.t;  (** Probe work per (schema index, shape). *)
  shape_ids : (string, int) Hashtbl.t;  (** Interned shape keys. *)
  mutable fixed_engine : Engine.t option;
  mutable fixed_done : bool;
  mutable next_slice : int;
  mutable builder : Semantic.builder option;
  mutable mace_builder : Mace.builder option;  (** The SAT pool builder ([mace]). *)
  prechecked : (Wire.schema * Theory.parameter, unit) Hashtbl.t;
      (** Observational killers the SAT pre-check found no small model for. *)
  mutable pool : Semantic.pool option;
  mutable scan_streams : stream list;
  mutable scan_cursor : int;
  mutable scan_turn : bool;
  mutable examined : int;
  mutable scan_killers : int;
  mutable killer_work : float;
  mutable arrival_work : float;
  mutable prior_stream : Wire.source Seq.t;
  mutable prior_index : int;
  mutable prior_pending : item list;
  mutable prior_fresh_work : float;
  mutable prior_retry_work : float;
  mutable oe : Observational.t option;  (** The bank and its cursor, built on the current pool. *)
  mutable oe_levels : int option;  (** K of the first bank, kept by rebuilds. *)
  mutable oe_extra : Semantic.model list;
      (** Counter-models that refined the pool after the bank was built, oldest first. *)
  mutable oe_found : Semantic.model list;  (** Counter-models of its own killers, not yet used. *)
  mutable oe_pool_seen : int;  (** Models of the shared pool already in the bank or [oe_extra]. *)
  mutable oe_extra_memo : int array array array;
      (** Per schema index and model of [oe_extra] (same order): the memo of [oe_memo]. *)
  mutable oe_off : bool;  (** Its guided budget is spent. *)
  mutable oe_memo : int array array array;
      (** Per schema index, model of the bank and extension of a condition in that model: the truth
          of the instance there (0 unknown, 1 false, 2 true or unknown). *)
  oe_offered : (Wire.source, unit) Hashtbl.t;  (** Conditions offered (kept across rebuilds). *)
  oe_queued : (Wire.schema * Theory.parameter, unit) Hashtbl.t;
      (** Instances it queued (never entered in [queued], see [oe_probe]). *)
  oe_killers : item Pending.t;
  oe_retry : item Pending.t;
  mutable oe_fresh_work : float;
  mutable oe_retry_work : float;
  mutable counted : float;
      (** Work units charged beyond allocation in total (see [oe_turn]); [main_work] excludes them.
      *)
  mutable turn_counted : float;  (** The part of [counted] added by the running turn. *)
  main_events : unit -> int * int;
      (** [Events]: the main engine's events and enumeration polls so far (the scheduler's hook). *)
  mutable main_events_start : float;
  mutable ev : float;
      (** [Events]: the lane's work units so far, apart from its evaluation steps (read live). *)
  luby : item Pending.t array;  (** Non-killer re-probes per level (index 0 unused). *)
  luby_level_work : float array;  (** Their cumulative work per level. *)
  meter : Semantic.meter;
  mutable result : Wire.certificate option;
  mutable winning : item option;
  stats : stats;
}

(* Work units done by the calling Domain so far. *)
let alloc_clock () = Telemetry.allocated_words () /. 1024.

(* Evaluation steps are worth [oe_eval_weight] / [oe_steps_per_unit] units (see the
   observational source below). *)
let ev_eval_rate = 8. /. 1_500.

(* The pool builder's evaluation steps so far ([Events] counts them as lane work). *)
let builder_steps t =
  (match t.builder with Some b -> Semantic.builder_steps b | None -> 0)
  + match t.mace_builder with Some b -> Mace.steps b | None -> 0

(* The lane's clock: allocation (default), or its own deterministic events. *)
let clock t =
  match t.config.clock with
  | Allocation -> alloc_clock ()
  | Events -> t.ev +. (ev_eval_rate *. float_of_int (t.meter.steps + builder_steps t))

let work t = t.stats.fixed_work +. t.stats.instance_work +. t.stats.prior_work
let found t = t.result <> None

(* [Events]: the main engine's events and polls in lane units, before its exchange rate. *)
let main_units t =
  let events, polls = t.main_events () in
  (t.config.ev_engine *. float_of_int events) +. (t.config.ev_raw *. float_of_int polls)

(* Main-search work since the lane started: everything else (work the lane
   counts beyond its allocation is not part of the allocation clock). With
   [Events], the main engine's own events at their exchange rate. *)
let main_work t =
  match t.config.clock with
  | Allocation -> alloc_clock () -. t.work_start -. (work t -. t.counted)
  | Events -> t.config.ev_main *. (main_units t -. t.main_events_start)

let past_deadline t = t.cancelled () || Telemetry.now () >= t.deadline

(* The events of an engine: its generated and given clauses, and the goals its Goal producer
   created and expanded, weighted [ev_goal_weight] (a goal expansion tries many inferences; in a
   goal-directed probe it is the only work). All are search events: a same-search speed-up keeps
   them. *)
let ev_goal_weight = 16

let engine_events (e : Engine.t) =
  e.metrics.generated + e.metrics.given
  + (ev_goal_weight * (e.goals.metrics.created + e.goals.metrics.expanded))

let create ?(worker = 0) ?(workers = 1) ?phase ?(cancelled = fun () -> false)
    ?(prepare = fun _ -> ()) ?bounds ?(synthesis = true) ?(admit = fun _ _ _ -> Free)
    ?(main_events = fun () -> (0, 0)) ~started ~inject config (engine_config : Engine.config) theory
    =
  validate config;
  let signature = Source.signature (Theory.arena theory) in
  let finite = if Signature.is_unrestricted signature then None else Some signature in
  let fixed_axioms = Theory.fixed theory in
  let formulas = List.map (fun (a : Wire.axiom) -> a.formula) fixed_axioms in
  let builder =
    match finite with
    | Some sg when config.pool && not config.mace ->
        Some (Semantic.builder ~budget:config.pool_budget sg formulas)
    | _ -> None
  in
  let mace_builder =
    match finite with
    | Some sg when config.pool && config.mace ->
        Some (Mace.builder ~budget:config.pool_budget sg formulas)
    | _ -> None
  in
  (* The main search's streams with its bounds, read by the lane's own cursor. *)
  let schemas = Theory.schemas theory in
  let streams = List.map (fun s -> (s, Theory.enumerate ?bounds theory s)) schemas in
  let schema_index = Hashtbl.create 8 in
  List.iteri
    (fun i s -> if not (Hashtbl.mem schema_index s) then Hashtbl.add schema_index s i)
    schemas;
  let t =
    {
      config;
      theory;
      engine_config;
      started;
      deadline = started +. engine_config.limits.seconds;
      work_start = alloc_clock ();
      phase = Option.value phase ~default:worker;
      worker;
      workers = max 1 workers;
      cancelled;
      prepare;
      synthesis;
      admit;
      inject;
      finite;
      fixed_axioms;
      probe_id = List.length fixed_axioms;
      queued = Hashtbl.create 256;
      fresh = Pending.create ();
      waiting = Hashtbl.create 256;
      killers = Pending.create ();
      prior_retry = Pending.create ();
      prior_killers = Pending.create ();
      prior_backlog = Pending.create ();
      schema_index;
      schema_work = Array.make (max 1 (List.length schemas)) 0.;
      class_work = Hashtbl.create 64;
      shape_ids = Hashtbl.create 64;
      fixed_engine = None;
      fixed_done = (not config.fixed) || fixed_axioms = [];
      next_slice = config.fixed_slice;
      builder;
      mace_builder;
      prechecked = Hashtbl.create (if config.mace then 64 else 1);
      pool = None;
      scan_streams =
        List.map
          (fun (s, seq) -> { s_schema = s; s_seq = seq; s_done = false; s_seconds = 0. })
          streams;
      scan_cursor = 0;
      scan_turn = false;
      examined = 0;
      scan_killers = 0;
      killer_work = 0.;
      arrival_work = 0.;
      prior_stream =
        (match (finite, config.prior) with
        | Some sg, Some prior when synthesis -> prior sg
        | _ -> Seq.empty);
      prior_index = 0;
      prior_pending = [];
      prior_fresh_work = 0.;
      prior_retry_work = 0.;
      oe = None;
      oe_levels = None;
      oe_extra = [];
      oe_found = [];
      oe_pool_seen = 0;
      oe_extra_memo = [||];
      oe_off = false;
      oe_memo = [||];
      oe_offered = Hashtbl.create 256;
      oe_queued = Hashtbl.create 64;
      oe_killers = Pending.create ();
      oe_retry = Pending.create ();
      oe_fresh_work = 0.;
      oe_retry_work = 0.;
      counted = 0.;
      turn_counted = 0.;
      main_events;
      main_events_start = 0.;
      ev = 0.;
      luby =
        (if config.luby_share > 0. then
           Array.init (config.luby_levels + 1) (fun _ -> Pending.create ())
         else [||]);
      luby_level_work =
        (if config.luby_share > 0. then Array.make (config.luby_levels + 1) 0. else [||]);
      meter = Semantic.meter ();
      result = None;
      winning = None;
      stats =
        {
          turns = 0;
          probes = 0;
          fixed_slices = 0;
          fixed_work = 0.;
          instance_work = 0.;
          prior_work = 0.;
          offered = 0;
          scanned = 0;
          killers = 0;
          prior = 0;
          reprobes = 0;
          injected = 0;
          pool_models = 0;
          refined = 0;
          charged_exhaustive = 0;
          charged_guided = 0;
          refused = 0;
          weak = false;
          expensive_streams = 0;
          peak_stored = 0;
          schemas = List.length schemas;
          schemas_probed = 0;
          shapes_probed = 0;
          probe_work = 0.;
          top_schema_work = 0.;
          top_shape_work = 0.;
          winner = "";
          seconds = 0.;
          promoted = 0;
          oe_work = 0.;
          oe_offered = 0;
          oe_killers = 0;
          oe_probes = 0;
          oe_rebuilds = 0;
          oe_kept = 0;
          oe_words = 0;
          oe_steps = 0;
          oe_evaluations = 0;
          oe_seconds = 0.;
          luby_probes = 0;
          mace_rejected = 0;
          luby_work = 0.;
          ev_engine_events = 0;
          ev_engine_alloc = 0.;
          ev_polls = 0;
          ev_poll_alloc = 0.;
          ev_capped = 0;
        };
    }
  in
  (match config.clock with Events -> t.main_events_start <- main_units t | Allocation -> ());
  t

(* ---------- shapes and breadth ---------- *)

(* The shape of an instance: the multiset of connectives, quantifiers,
   equalities and non-logical symbols of its formula (variables are ignored).
   Instances of one schema differ only in their condition, so within a schema
   two instances have the same shape exactly when their conditions use the
   same constructors and symbols the same number of times (for example, all
   renamings of one condition). Interned as a small integer per lane. *)
let shape_of t (f : Wire.source) =
  let counts = Hashtbl.create 16 in
  let bump k = Hashtbl.replace counts k (1 + Option.value ~default:0 (Hashtbl.find_opt counts k)) in
  let rec term = function
    | Wire.B _ | Wire.F _ -> ()
    | Wire.App (s, ts) ->
        bump ("f:" ^ s);
        List.iter term ts
  in
  let rec go = function
    | Wire.Top -> bump "T"
    | Wire.Bot -> bump "F"
    | Wire.Pred (p, ts) ->
        bump ("p:" ^ p);
        List.iter term ts
    | Wire.Eq (a, b) ->
        bump "=";
        term a;
        term b
    | Wire.Neg g ->
        bump "~";
        go g
    | Wire.Conj gs ->
        bump ("&" ^ string_of_int (List.length gs));
        List.iter go gs
    | Wire.Disj gs ->
        bump ("|" ^ string_of_int (List.length gs));
        List.iter go gs
    | Wire.All g ->
        bump "!";
        go g
    | Wire.Ex g ->
        bump "?";
        go g
  in
  go f;
  let key =
    Hashtbl.fold (fun k n acc -> (k, n) :: acc) counts []
    |> List.sort compare
    |> List.map (fun (k, n) -> k ^ "=" ^ string_of_int n)
    |> String.concat " "
  in
  match Hashtbl.find_opt t.shape_ids key with
  | Some id -> id
  | None ->
      let id = Hashtbl.length t.shape_ids in
      Hashtbl.add t.shape_ids key id;
      id

let index_of t schema = Option.value ~default:0 (Hashtbl.find_opt t.schema_index schema)
let class_of t item = (index_of t item.schema, item.shape)

(* The instance formula of [parameter] in the lane's ID space, if it has one. *)
let instance_formula t schema parameter =
  match Theory.instantiate_parameter t.theory ~id:t.probe_id schema parameter with
  | exception Invalid_argument _ -> None
  | axiom -> Some axiom.formula

let shape_of_parameter t schema parameter =
  match instance_formula t schema parameter with Some f -> shape_of t f | None -> -1

(* A probe of [cls] spent [spent] work units: the breadth statistics (distinct
   schemas and shapes probed, the largest schema and shape shares) and the
   fair choice's work tables. *)
let charge t ((s, _) as cls) spent =
  (* A probe always allocates; the floor keeps every probed class positive. *)
  let spent = Float.max spent (1. /. 1024.) in
  let st = t.stats in
  let before = Option.value ~default:(-1.) (Hashtbl.find_opt t.class_work cls) in
  if before < 0. then st.shapes_probed <- st.shapes_probed + 1;
  let w = Float.max 0. before +. spent in
  Hashtbl.replace t.class_work cls w;
  if s >= 0 && s < Array.length t.schema_work then (
    if t.schema_work.(s) = 0. then st.schemas_probed <- st.schemas_probed + 1;
    t.schema_work.(s) <- t.schema_work.(s) +. spent;
    st.top_schema_work <- Float.max st.top_schema_work t.schema_work.(s));
  st.top_shape_work <- Float.max st.top_shape_work w;
  st.probe_work <- st.probe_work +. spent

(* The next pending item of an instance queue: fair over schemas and shapes
   with [breadth], else in arrival order. *)
let take t q =
  if t.config.breadth then
    Pending.take_fair q
      ~schema_work:(fun s ->
        if s >= 0 && s < Array.length t.schema_work then t.schema_work.(s) else 0.)
      ~class_work:(fun cls ->
        Float.max 0. (Option.value ~default:0. (Hashtbl.find_opt t.class_work cls)))
      ~cap:t.config.shape_cap
  else Pending.take_oldest q

let enqueue t q item = Pending.add q (class_of t item) item
let ready_pool t = match t.pool with Some p when p.models <> [] -> Some p | _ -> None

(* The pool ranks instances only while it discriminates. *)
let ranking t = (not t.stats.weak) && ready_pool t <> None

(* Is [formula] false in every model of the ready pool? Evaluations stop at
   the deadline (the answer is then "no"). *)
let killer_formula t formula =
  match ready_pool t with
  | None -> false
  | Some p ->
      List.for_all
        (fun m ->
          (not (past_deadline t))
          && Semantic.eval ~budget:200_000 ~meter:t.meter m formula = Some false)
        p.models

(* Is the instance of [parameter] false in every model of the ready pool? *)
let is_killer t schema parameter =
  ready_pool t <> None
  && match instance_formula t schema parameter with Some f -> killer_formula t f | None -> false

(* A fresh engine with the worker's engine configuration (calculus, strategy
   and memory budgets) at the worker's queue phase, and the run's deadline.
   Clause counts are not limited (the lane's work budget is); the stored proof
   nodes are, by the lane engine's memory budget. Like the worker's other
   engines, it answers the worker's budget itself: its reading is its own
   footprint plus the main engine's (the scheduler's [prepare]), and it never withdraws an
   instance (its axioms are added without ~releasable). A strategy precedence
   (E workers) is computed from the fixed axioms, as for the main engine. *)
let engine t ~retained =
  let limits = t.engine_config.limits in
  let remaining = limits.seconds -. (Telemetry.now () -. t.started) in
  let limits =
    {
      Engine.max_given = max_int;
      max_generated = max_int;
      max_retained = min limits.max_retained retained;
      seconds = Float.max 0. remaining;
    }
  in
  let e = Engine.create ~phase:t.phase ~cancelled:t.cancelled { t.engine_config with limits } in
  t.prepare e;
  e

let note_stored t (e : Engine.t) =
  t.stats.peak_stored <- max t.stats.peak_stored (Proof.stored e.proof)

(* [Events]: a new lane engine's setup (its input clauses, plus a fixed cost per engine, so that
   no probe is free) is lane work outside its run budget, as its allocation is with the
   allocation clock. *)
let ev_setup_events = 16

(* [Events]: the allocation safety net of a lane-engine run, in multiples of its budget (the
   calibration puts about one allocation unit on each unit of budget). *)
let ev_alloc_cap = 8.

let charge_setup t (e : Engine.t) =
  match t.config.clock with
  | Allocation -> ()
  | Events ->
      let n = ev_setup_events + engine_events e in
      t.ev <- t.ev +. (t.config.ev_engine *. float_of_int n);
      t.stats.ev_engine_events <- t.stats.ev_engine_events + n

(* Run [e] for about [budget] more work units; the overshoot is at most one
   engine step. [`Exhausted] means the budget ran out while the engine still
   had work: only then can a larger budget change the outcome. *)
let run t (e : Engine.t) ~budget =
  (match t.config.clock with
  | Allocation -> (
      let stop = alloc_clock () +. float_of_int budget in
      try
        while e.root = None && e.stopped = None && Engine.has_work e && alloc_clock () < stop do
          Engine.step e
        done
      with Engine.Stop -> ())
  | Events ->
      (* The engine's own events at the lane-engine rate; the units are added to the lane's
         clock as they are spent. Safety net: a run also stops after [ev_alloc_cap] times its
         budget in allocation units (an engine can spend seconds and gigabytes on a few
         events, e.g. on huge terms); only such runs depend on allocation. *)
      let rate = t.config.ev_engine and a0 = alloc_clock () in
      let start = engine_events e and cap = ev_alloc_cap *. float_of_int budget in
      let spent () = rate *. float_of_int (engine_events e - start) in
      (try
         while
           e.root = None && e.stopped = None && Engine.has_work e
           && spent () < float_of_int budget
           && alloc_clock () -. a0 < cap
         do
           Engine.step e
         done
       with Engine.Stop -> ());
      if alloc_clock () -. a0 >= cap then t.stats.ev_capped <- t.stats.ev_capped + 1;
      let n = engine_events e - start in
      t.ev <- t.ev +. (rate *. float_of_int n);
      t.stats.ev_engine_events <- t.stats.ev_engine_events + n;
      t.stats.ev_engine_alloc <- t.stats.ev_engine_alloc +. (alloc_clock () -. a0));
  note_stored t e;
  if e.root = None && e.stopped = None && Engine.has_work e then `Exhausted else `Settled

let certificate t (e : Engine.t) =
  Engine.seal e;
  Engine.certificate e ~theory:(Theory.name t.theory)

(* The instance budget of [source] is spent: stop generating its items. *)
let exhausted t = function
  | Injected -> ()
  | Scanned ->
      List.iter
        (fun s ->
          s.s_done <- true;
          s.s_seq <- Seq.empty)
        t.scan_streams
  | Prior ->
      t.prior_index <- t.config.prior_cap;
      t.prior_pending <- []
  | Observed ->
      t.oe_off <- true;
      t.oe <- None;
      Pending.clear t.oe_killers;
      Pending.clear t.oe_retry

(* An instance the main engine has not injected is charged to the search's
   instance budget of its generator before a probe may use it. *)
let admitted t item =
  item.source = Injected
  ||
  match t.admit item.source item.schema item.parameter with
  | Free -> true
  | Charged ->
      (match item.source with
      | Prior | Observed -> t.stats.charged_guided <- t.stats.charged_guided + 1
      | Injected | Scanned -> t.stats.charged_exhaustive <- t.stats.charged_exhaustive + 1);
      true
  | Refused ->
      t.stats.refused <- t.stats.refused + 1;
      exhausted t item.source;
      false

(* One probe: fixed axioms + [item]'s instance, numbered in the lane's own
   ID space (the first ID after the fixed axioms, the same in every probe), so
   probes never consume the main engine's instance or Skolem IDs and a probe's
   outcome does not depend on how many probes ran before it. [`Refused]: the
   instance is outside the search's budget and was not used. The probe's work
   is charged to its (schema, shape) class. *)
let probe ?(breadth = true) t item =
  match Theory.instantiate_parameter t.theory ~id:t.probe_id item.schema item.parameter with
  | exception Invalid_argument _ -> `Settled
  | _ when not (admitted t item) -> `Refused
  | axiom ->
      let w0 = clock t in
      let cls = (index_of t item.schema, shape_of t axiom.formula) in
      Fun.protect
        ~finally:(fun () ->
          (* Observational probes are accounted in the source's own share and
             leave the breadth tables of the other probes untouched, and so do
             the re-probes of non-killers ([breadth] false). *)
          if item.source <> Observed && breadth then charge t cls (clock t -. w0))
        (fun () ->
          t.stats.probes <- t.stats.probes + 1;
          if item.level > 0 then t.stats.reprobes <- t.stats.reprobes + 1;
          let e = engine t ~retained:t.config.probe_retained in
          Engine.add_initial_axioms e t.fixed_axioms;
          Engine.add_axiom e axiom;
          charge_setup t e;
          let outcome = run t e ~budget:(t.config.instance_budget lsl item.level) in
          match certificate t e with
          | Some cert ->
              t.result <- Some cert;
              t.winning <- Some item;
              t.stats.winner <-
                (match item.source with
                | Prior -> "prior"
                | Observed -> "observed"
                | Injected | Scanned -> "instance");
              `Settled
          | None ->
              (* Counterexample refinement: a small model of a failed killer
                 demotes similar false killers. *)
              (match (t.pool, t.finite) with
              | Some p, Some sg
                when item.killer && item.level = 0 && t.config.refine_budget > 0
                     && not (past_deadline t) -> (
                  match
                    if t.config.mace then
                      if Hashtbl.mem t.prechecked (item.schema, item.parameter) then None
                      else
                        Mace.find_model ~budget:t.config.refine_budget ~meter:t.meter sg p.active
                          axiom.formula
                    else
                      Semantic.find_model ~budget:t.config.refine_budget ~meter:t.meter sg p.active
                        axiom.formula
                  with
                  | Some m ->
                      t.stats.refined <- t.stats.refined + 1;
                      (* The observational source keeps its counter-models to
                         itself, so the look-ahead's ranking is not changed. *)
                      if item.source = Observed then t.oe_found <- m :: t.oe_found
                      else t.pool <- Some { p with models = m :: p.models }
                  | None -> ())
              | _ -> ());
              outcome)

(* Re-probe with a doubled budget, up to [escalations] times; a pool killer
   that failed every level and that the main engine has not seen goes to the
   main engine, which can combine it with other instances. *)
let escalate t queue item outcome =
  if t.result = None && outcome <> `Refused then
    if outcome = `Exhausted && item.level < t.config.escalations then (
      if Pending.length queue < t.config.retry_cap then
        enqueue t queue { item with level = item.level + 1 })
    else if item.killer && item.source <> Injected && t.config.inject_failed then (
      t.stats.injected <- t.stats.injected + 1;
      t.inject item.source item.schema item.parameter)

(* ---------- sub-lanes ---------- *)

let fixed_turn t =
  let e =
    match t.fixed_engine with
    | Some e -> e
    | None ->
        let e = engine t ~retained:t.config.fixed_retained in
        Engine.add_initial_axioms e t.fixed_axioms;
        charge_setup t e;
        t.fixed_engine <- Some e;
        e
  in
  t.stats.fixed_slices <- t.stats.fixed_slices + 1;
  ignore (run t e ~budget:t.next_slice);
  t.next_slice <- min t.config.fixed_slice_cap (2 * t.next_slice);
  if e.root <> None then (
    t.result <- certificate t e;
    t.stats.winner <- "fixed")
  else if e.stopped <> None || not (Engine.has_work e) then (
    (* Saturated, out of time or over its memory budget: release it. *)
    t.fixed_done <- true;
    t.fixed_engine <- None)

(* The pool stopped discriminating: its killers lose their priority and are
   probed at level 0 like every other instance. *)
let weaken t =
  t.stats.weak <- true;
  (* Unprobed look-ahead killers keep their arrival order, and injected
     instances the look-ahead promoted wait among the arrivals again;
     escalated ones already failed at a larger budget. *)
  Pending.iter
    (fun item ->
      if item.level = t.config.killer_level && (item.source = Scanned || item.source = Injected)
      then (
        if item.source = Injected then Hashtbl.replace t.waiting (item.schema, item.parameter) ();
        enqueue t t.fresh { item with killer = false; level = 0 }))
    t.killers;
  Pending.clear t.killers

let live_streams t = List.filter (fun s -> not s.s_done) t.scan_streams

(* Raised by the look-ahead's enumeration guard at the deadline or on a stop request. *)
exception Past_deadline

(* A finished or abandoned stream releases its cursor. *)
let finish s =
  s.s_done <- true;
  s.s_seq <- Seq.empty

(* Look-ahead over the schema streams, round-robin from a rotating start, so
   that every schema gets look-ahead. With a ranking pool only killers are
   queued (as killers); everything else stays unmarked, so the same instance
   is still probed when the main engine injects it later. Without one the
   next unqueued candidate is queued: this keeps the lane busy when it is
   faster than the main engine's injection. A turn ends after [scan]
   candidates, [turn_steps] evaluation steps or about one level-0 probe of
   work, and the look-ahead ends for good after [scan_cap] candidates. A
   stream step is opaque (a registered schema may filter for a long time
   inside one step), so a step is never started when the stream's previous
   step predicts it to end after the deadline, and a step that allocates more
   than [scan_step_cap] ends that stream's look-ahead. A step built on
   Enumerate (bounded/exhaustive) is also forced under the lane's own guard
   ([Enumerate.with_guard]), which every 16th raw candidate checks the
   deadline and stop requests: such a step is abandoned at the deadline, and
   the stream's look-ahead ends there (no lane turn starts after the deadline,
   so it is never forced again). *)
let scan t =
  let rank = ranking t in
  let budget = ref (max 1 t.config.scan) and queued = ref false in
  let steps = t.meter.steps and w0 = clock t in
  let quota () =
    t.meter.steps - steps < t.config.turn_steps
    && clock t -. w0 < float_of_int t.config.instance_budget
  in
  let rotation =
    let live = Array.of_list (live_streams t) in
    let n = Array.length live in
    let start = if n = 0 then 0 else t.scan_cursor mod n in
    t.scan_cursor <- t.scan_cursor + 1;
    List.init n (fun i -> live.((start + i) mod n))
  in
  let consider s p =
    t.stats.scanned <- t.stats.scanned + 1;
    if not (Hashtbl.mem t.queued (s.s_schema, p)) then
      if not rank then (
        Hashtbl.replace t.queued (s.s_schema, p) ();
        queued := true;
        enqueue t t.fresh
          {
            schema = s.s_schema;
            parameter = p;
            source = Scanned;
            level = 0;
            killer = false;
            shape = shape_of_parameter t s.s_schema p;
          })
      else (
        t.examined <- t.examined + 1;
        match instance_formula t s.s_schema p with
        | Some f when killer_formula t f ->
            t.scan_killers <- t.scan_killers + 1;
            Hashtbl.replace t.queued (s.s_schema, p) ();
            t.stats.killers <- t.stats.killers + 1;
            enqueue t t.killers
              {
                schema = s.s_schema;
                parameter = p;
                source = Scanned;
                level = t.config.killer_level;
                killer = true;
                shape = shape_of t f;
              }
        | _ -> ())
    else if rank && Hashtbl.mem t.waiting (s.s_schema, p) then
      (* The main engine injected this candidate before the look-ahead read
         it, and it still waits among the arrivals: a pool killer moves to the
         killers, as if the look-ahead had read it first (the lane's killer
         queue then does not depend on that race). The weak-pool counts are
         unchanged. *)
      match instance_formula t s.s_schema p with
      | Some f when killer_formula t f ->
          Hashtbl.remove t.waiting (s.s_schema, p);
          t.stats.killers <- t.stats.killers + 1;
          t.stats.promoted <- t.stats.promoted + 1;
          enqueue t t.killers
            {
              schema = s.s_schema;
              parameter = p;
              source = Injected;
              level = t.config.killer_level;
              killer = true;
              shape = shape_of t f;
            }
      | _ -> ()
  in
  let force s =
    match t.config.clock with
    | Allocation ->
        Enumerate.with_guard (fun () -> if past_deadline t then raise Past_deadline) s.s_seq
    | Events ->
        (* Every poll stands for 16 raw candidates of the enumeration. *)
        let b0 = alloc_clock () in
        Fun.protect
          ~finally:(fun () ->
            t.stats.ev_poll_alloc <- t.stats.ev_poll_alloc +. (alloc_clock () -. b0))
          (fun () ->
            Enumerate.with_guard
              (fun () ->
                t.ev <- t.ev +. t.config.ev_raw;
                t.stats.ev_polls <- t.stats.ev_polls + 1;
                if past_deadline t then raise Past_deadline)
              s.s_seq)
  in
  let step s =
    let t0 = Telemetry.now () and a0 = clock t in
    (match force s with
    | Seq.Nil -> finish s
    | Seq.Cons (p, rest) ->
        s.s_seq <- rest;
        Option.iter (consider s) p
    | exception Past_deadline -> finish s);
    s.s_seconds <- Telemetry.now () -. t0;
    if (not s.s_done) && clock t -. a0 > float_of_int t.config.scan_step_cap then (
      finish s;
      t.stats.expensive_streams <- t.stats.expensive_streams + 1)
  in
  let rec loop = function
    | [] -> ()
    | rotation ->
        let next =
          List.filter
            (fun s ->
              if
                !budget > 0 && (rank || not !queued) && quota () && (not s.s_done)
                && t.stats.scanned < t.config.scan_cap
                && Telemetry.now () +. (2. *. s.s_seconds) < t.deadline
                && not (t.cancelled ())
              then (
                decr budget;
                step s;
                not s.s_done)
              else false)
            rotation
        in
        if !budget > 0 && (rank || not !queued) && quota () then loop next
  in
  loop rotation;
  (* The look-ahead's memory bound: release every cursor at the cap. *)
  if t.stats.scanned >= t.config.scan_cap then List.iter finish t.scan_streams;
  (* A pool that calls a large fraction of the candidates killers does not
     discriminate between them. *)
  if
    rank && t.examined >= 64
    && float_of_int t.scan_killers > t.config.weak_pool *. float_of_int t.examined
  then weaken t

let scan_ready t = t.config.scan > 0 && live_streams t <> []

(* Pool slices per turn: about one level-0 probe of evaluation. *)
let pool_quota = 50_000

(* ---------- re-probes of non-killers (SEM-LUBY) ---------- *)

(* A non-killer probe that stopped with engine work left ([`Exhausted]) is
   retried at doubling budgets, levels 1 .. [luby_levels], inside at most
   [luby_share] of the instance sub-lane's work. Inside that share the levels
   get equal cumulative work, the aggregate of Luby et al.'s universal restart
   sequence: the next re-probe is at the level whose cumulative work would be
   least after it (its work plus the probe's budget, instance_budget x 2^l;
   ties go to the lower level; oldest first inside a level). A level-l probe
   costs twice a level-(l-1) probe, so the lower levels get more probes for
   the same work, and a level opened by the first escalation does not take
   probes ahead of the levels below it (counting only the work done so far,
   one instance would climb every level before a second one is retried).
   Without it, non-killers are tried once at level 0 (a uniformly larger
   level-0 budget would trade breadth for depth). The re-probes leave the
   breadth tables alone. *)
let luby_on t = t.config.luby_share > 0. && Array.length t.luby > 1

let luby_retry t item outcome =
  if luby_on t && t.result = None && outcome = `Exhausted && item.level < t.config.luby_levels then
    let pending = Array.fold_left (fun n q -> n + Pending.length q) 0 t.luby in
    if pending < t.config.retry_cap then
      let level = item.level + 1 in
      enqueue t t.luby.(level) { item with level; killer = false }

let luby_ready t = luby_on t && Array.exists (fun q -> not (Pending.is_empty q)) t.luby

let luby_turn t =
  let after l = t.luby_level_work.(l) +. float_of_int (t.config.instance_budget lsl l) in
  let best = ref (-1) in
  Array.iteri
    (fun l q ->
      if l > 0 && not (Pending.is_empty q) then if !best < 0 || after l < after !best then best := l)
    t.luby;
  if !best > 0 then (
    let l = !best in
    let w0 = clock t in
    (match Pending.take_oldest t.luby.(l) with
    | Some item ->
        t.stats.luby_probes <- t.stats.luby_probes + 1;
        luby_retry t item (probe ~breadth:false t item)
    | None -> ());
    let spent = clock t -. w0 in
    t.luby_level_work.(l) <- t.luby_level_work.(l) +. spent;
    t.stats.luby_work <- t.stats.luby_work +. spent)

(* The next non-killer probe: classified when it is taken while the pool
   ranks (a killer starts at [killer_level] and escalates). *)
let probe_fresh t =
  match take t t.fresh with
  | None -> ()
  | Some item
    when item.source = Injected && not (Hashtbl.mem t.waiting (item.schema, item.parameter)) ->
      (* The look-ahead already moved it to the killers. *)
      ()
  | Some item ->
      Hashtbl.remove t.waiting (item.schema, item.parameter);
      let killer = ranking t && is_killer t item.schema item.parameter in
      let item = { item with killer; level = (if killer then t.config.killer_level else 0) } in
      if killer then t.stats.killers <- t.stats.killers + 1;
      let outcome = probe t item in
      if killer then escalate t t.killers item outcome else luby_retry t item outcome

(* Pool killers and the other probes share the instance sub-lane by work:
   the others keep at least [arrival_share] of it while both wait. *)
let probe_ranked t =
  let killers = not (Pending.is_empty t.killers) and arrivals = not (Pending.is_empty t.fresh) in
  let a = t.config.arrival_share in
  let killer_turn =
    killers && ((not arrivals) || t.killer_work *. a <= t.arrival_work *. (1. -. a))
  in
  if killers || arrivals then (
    let w0 = clock t in
    if killer_turn then
      match take t t.killers with
      | Some item -> escalate t t.killers item (probe t item)
      | None -> ()
    else probe_fresh t;
    let spent = clock t -. w0 in
    if killer_turn then t.killer_work <- t.killer_work +. spent
    else t.arrival_work <- t.arrival_work +. spent)
  else if scan_ready t then scan t

(* ---------- observational source ---------- *)

(* The observational source (Observational) enumerates the theory's own
   formulas bottom-up, one per truth table over the ranking pool, and offers
   every new condition class to every schema through its [guide]. Instances
   that are pool killers are probed from level 0 and escalate like the other
   killers; a killer whose level-0 probe fails starts the usual counter-model
   search, and a model found there refines the pool: the failed killer and
   the pending killers that the model satisfies are dropped, and every later
   killer test also evaluates in that model (any killer's counter-model). The
   bank keeps growing on its own pool; once it is finished it is rebuilt on
   the refined pool (formulas the old pool could not tell apart become
   separate classes). Rebuilding at every counter-model would repeat the
   same early enumeration again and again (six times in 10 s on
   cantor-injection). Non-killers are not probed: the look-ahead and the main
   engine's enumeration still reach them. The source takes at most
   [oe_share] of the instance sub-lane's work; its enumeration advances by
   quotas of [oe_quota] steps (Observational) and of one level-0 probe of
   work, and its killers are charged to the guided budget. It runs only while the pool ranks (a pool that does not
   discriminate gives it nothing to go on) and only with guided synthesis. *)

(* The bank can grow, or a finished bank can be rebuilt on a refined pool. *)
let oe_enumerable t =
  t.stats.oe_offered < t.config.oe_cap
  && match t.oe with Some e -> (not (Observational.finished e)) || t.oe_extra <> [] | None -> true

let oe_ready t =
  t.config.observational && t.synthesis && t.finite <> None && (not t.oe_off) && ranking t
  && ((not (Pending.is_empty t.oe_killers))
     || (not (Pending.is_empty t.oe_retry))
     || oe_enumerable t)

(* Killer test of a condition class. A condition has only the principal
   variable free, so in each pool model its instance's truth depends only on
   the condition's extension there (the set of elements satisfying it): the
   instance is the schema's template applied to the condition. The lane
   therefore evaluates an instance in a model at most once per (schema,
   model, extension), at most 2^n times for a model of n elements, and every
   later class reads the memo. (For a registered schema whose expansion is
   not such a template the memo can only misrank, never misprove: every
   probe is an ordinary refutation attempt.) *)
let memo_size = 16

let oe_memo_entry t si e i table =
  let row = t.oe_memo.(si).(i) in
  if Array.length row = 0 then None
  else
    let x = Observational.extension e table i in
    Some (row, x)

(* The truth of an instance in model [m] (1 false, 2 true or unknown); stops
   at the deadline (the answer is then "true"). *)
let oe_value t (m : Semantic.model) formula =
  if past_deadline t then 2
  else match Semantic.eval ~budget:200_000 ~meter:t.meter m formula with Some false -> 1 | _ -> 2

(* The extensions of a condition in the counter-models outside the bank. *)
let oe_extra_extensions t form =
  List.map
    (fun m ->
      let x, steps = Observational.extension_in form m in
      t.stats.oe_steps <- t.stats.oe_steps + steps;
      x)
    t.oe_extra

(* Is the instance false in every model of the bank and in every counter-model
   found since? *)
let oe_killer t e si formula table extra =
  let models = Observational.models e in
  let n = Array.length models in
  n > 0
  &&
  let rec go i =
    i >= n
    ||
    let v =
      match oe_memo_entry t si e i table with
      | Some (row, x) ->
          if row.(x) = 0 then row.(x) <- oe_value t models.(i) formula;
          row.(x)
      | None -> oe_value t models.(i) formula
    in
    v = 1 && go (i + 1)
  in
  go 0
  && List.for_all2
       (fun (m, row) x ->
         if Array.length row = 0 then oe_value t m formula = 1
         else (
           if row.(x) = 0 then row.(x) <- oe_value t m formula;
           row.(x) = 1))
       (List.combine t.oe_extra (Array.to_list t.oe_extra_memo.(si)))
       extra

(* Some model is already known to make the instance true. *)
let oe_known_true t e si table extra =
  let n = Array.length (Observational.models e) in
  let rec go i =
    i < n
    && ((match oe_memo_entry t si e i table with Some (row, x) -> row.(x) = 2 | None -> false)
       || go (i + 1))
  in
  go 0
  || List.exists2
       (fun row x -> Array.length row > 0 && row.(x) = 2)
       (Array.to_list t.oe_extra_memo.(si))
       extra

(* [mace]: a killer with a small model (fixed axioms of the pool + the instance,
   SAT at sizes 1-6 within [mace_precheck] steps) is no killer: it is dropped
   before its probe, and the model joins the source's counter-models (used by
   the next killer tests, see [oe_sync]). *)
let oe_precheck t f =
  t.config.mace && t.config.mace_precheck > 0
  &&
  match (t.pool, t.finite) with
  | Some p, Some sg when not (past_deadline t) -> (
      match Mace.find_model ~budget:t.config.mace_precheck ~meter:t.meter sg p.active f with
      | Some m ->
          t.stats.mace_rejected <- t.stats.mace_rejected + 1;
          t.oe_found <- m :: t.oe_found;
          true
      | None -> false)
  | _ -> false

(* A new condition class: queue the instances that are pool killers. *)
let oe_offer t e form table =
  let condition = Observational.condition form in
  if not (Hashtbl.mem t.oe_offered condition) then (
    Hashtbl.replace t.oe_offered condition ();
    t.stats.oe_offered <- t.stats.oe_offered + 1;
    let schemas = List.mapi (fun si s -> (si, s)) (Theory.schemas t.theory) in
    let extra = oe_extra_extensions t form in
    let open_schemas =
      List.filter (fun (si, _) -> not (oe_known_true t e si table extra)) schemas
    in
    if open_schemas <> [] then
      match Wire.import (Theory.arena t.theory) condition with
      | exception Invalid_argument _ -> ()
      | phi ->
          List.iter
            (fun (si, schema) ->
              match Theory.guided_parameter t.theory schema phi with
              | Some parameter
                when not
                       (Hashtbl.mem t.queued (schema, parameter)
                       || Hashtbl.mem t.oe_queued (schema, parameter)) -> (
                  match instance_formula t schema parameter with
                  | Some f when oe_killer t e si f table extra && not (oe_precheck t f) ->
                      if t.config.mace && t.config.mace_precheck > 0 then
                        Hashtbl.replace t.prechecked (schema, parameter) ();
                      Hashtbl.replace t.oe_queued (schema, parameter) ();
                      t.stats.killers <- t.stats.killers + 1;
                      t.stats.oe_killers <- t.stats.oe_killers + 1;
                      enqueue t t.oe_killers
                        {
                          schema;
                          parameter;
                          source = Observed;
                          level = 0;
                          killer = true;
                          shape = shape_of t f;
                        }
                  | _ -> ())
              | _ -> ())
            open_schemas)

(* Enumeration steps of one turn (Observational's unit: a candidate plus one
   step per eight table bytes): a few milliseconds of tables. *)
let oe_quota = 250_000
let oe_note t e = t.stats.oe_words <- max t.stats.oe_words (Observational.words e)

(* Advance the enumeration by one quota, stopping at the first new killer. *)
let oe_enumerate t =
  match ready_pool t with
  | None -> ()
  | Some p ->
      (match t.oe with
      | Some e when not (Observational.finished e && t.oe_extra <> []) -> ()
      | _ ->
          if t.oe <> None then t.stats.oe_rebuilds <- t.stats.oe_rebuilds + 1;
          (* The shared pool plus the source's own counter-models. *)
          t.oe_pool_seen <- List.length p.models;
          let p = { p with models = List.rev_append t.oe_extra p.models } in
          t.oe_extra <- [];
          t.oe_extra_memo <- [||];
          let e =
            Observational.create ~bucket_cap:t.config.oe_bucket
              ~word_cap:(t.config.oe_words / t.workers) ?levels:t.oe_levels
              (Source.signature (Theory.arena t.theory))
              p
          in

          t.oe_levels <- Some (Observational.levels e);
          t.oe_memo <-
            Array.init
              (max 1 (List.length (Theory.schemas t.theory)))
              (fun _ ->
                Array.map
                  (fun (m : Semantic.model) ->
                    if m.size <= memo_size then Array.make (1 lsl m.size) 0 else [||])
                  (Observational.models e));
          t.oe_extra_memo <- Array.make (max 1 (List.length (Theory.schemas t.theory))) [||];
          t.oe <- Some e);
      Option.iter
        (fun e ->
          let w0 = clock t and kept = Observational.kept e and steps = Observational.steps e in
          Observational.advance e ~quota:oe_quota ~emit:(fun form table ->
              oe_offer t e form table;
              (not (Pending.is_empty t.oe_killers))
              || t.oe_found <> []
              || t.stats.oe_offered >= t.config.oe_cap
              || clock t -. w0 >= float_of_int t.config.instance_budget
              || past_deadline t);
          t.stats.oe_kept <- t.stats.oe_kept + (Observational.kept e - kept);
          t.stats.oe_steps <- t.stats.oe_steps + (Observational.steps e - steps);
          oe_note t e)
        t.oe

(* A counter-model refined the pool: the pending killers it satisfies are
   dropped, and later killer tests also evaluate in it (memoised by the
   condition's extension there, computed directly). The bank keeps growing on
   its pool; once it is finished, it is rebuilt on the refined pool, whose
   finer classes separate formulas the old pool merged. *)
let oe_refine t m =
  t.oe_extra <- t.oe_extra @ [ m ];
  t.oe_extra_memo <-
    Array.map
      (fun rows ->
        Array.append rows [| (if m.size <= memo_size then Array.make (1 lsl m.size) 0 else [||]) |])
      t.oe_extra_memo;
  let keep q =
    let items = ref [] in
    Pending.iter (fun item -> items := item :: !items) q;
    Pending.clear q;
    List.iter
      (fun item ->
        match instance_formula t item.schema item.parameter with
        | Some f when Semantic.eval ~budget:200_000 ~meter:t.meter m f = Some false ->
            enqueue t q item
        | _ -> ())
      (List.rev !items)
  in
  keep t.oe_killers;
  keep t.oe_retry

(* New counter-models for the killer test: the source's own (kept out of the
   shared pool), and those the other killers' probes added to the front of
   the shared pool since the bank was built, oldest first. *)
let oe_sync t =
  match (t.oe, t.pool) with
  | Some _, Some p ->
      let fresh = List.length p.models - t.oe_pool_seen in
      if fresh > 0 then (
        t.oe_pool_seen <- List.length p.models;
        List.iter (oe_refine t) (List.rev (List.filteri (fun i _ -> i < fresh) p.models)));
      let own = List.rev t.oe_found in
      t.oe_found <- [];
      List.iter (oe_refine t) own
  | _ -> ()

(* The source never takes an instance away from the other sources: it does
   not mark its instances in [queued], so the look-ahead (which starts its
   killers at [killer_level]) and the main engine's arrivals still probe them
   on their own paths, and a fresh killer that another source queued first is
   left to it. An instance both probe is charged once (the caller's [admit]). *)
let oe_probe t item =
  if item.level = 0 && Hashtbl.mem t.queued (item.schema, item.parameter) then ()
  else
    let refined = t.stats.refined in
    t.stats.oe_probes <- t.stats.oe_probes + 1;
    let outcome = probe t item in
    (* A counter-model of this killer makes it true there: it is dropped. *)
    if t.stats.refined > refined then oe_sync t else escalate t t.oe_retry item outcome

(* The source's steps per work unit, and the weight of one model-evaluation
   step in those steps. A table operation allocates little for the time it
   takes (one result table per candidate), so allocation alone would
   undercount the source's time several times over; a turn is charged the
   larger of its allocation and its counted steps. Calibration (flambda
   build, loaded machine): about 2.3 ns per enumeration step, 18 ns per
   evaluation step, and 2-4 microseconds per work unit of the engines.
   Both counts are deterministic. *)
let oe_steps_per_unit = 1_500.
let oe_eval_weight = 8

(* The re-probe at the lowest level, oldest first: every killer gets a level
   before any killer gets the next one (iterative deepening), so a killer
   that needs a larger budget is not starved behind earlier false killers
   escalating to the top level. *)
let oe_next_retry t =
  let best = ref None in
  Pending.iter
    (fun item ->
      match !best with Some b when b.level <= item.level -> () | _ -> best := Some item)
    t.oe_retry;
  match !best with
  | None -> None
  | Some b ->
      let rest = ref [] in
      Pending.iter (fun item -> if item != b then rest := item :: !rest) t.oe_retry;
      Pending.clear t.oe_retry;
      List.iter (enqueue t t.oe_retry) (List.rev !rest);
      Some b

(* Fresh killers (and the enumeration that finds them) and re-probes share
   the source by work. *)
let oe_turn t =
  let w0 = clock t and t0 = Telemetry.now () in
  let steps0 = t.stats.oe_steps and meter0 = t.meter.steps in
  oe_sync t;
  let retry = (not (Pending.is_empty t.oe_retry)) && t.oe_retry_work <= t.oe_fresh_work in
  (if retry then Option.iter (oe_probe t) (oe_next_retry t)
   else
     match Pending.take_oldest t.oe_killers with
     | Some item -> oe_probe t item
     | None ->
         if oe_enumerable t then oe_enumerate t else Option.iter (oe_probe t) (oe_next_retry t));
  t.stats.oe_evaluations <- t.stats.oe_evaluations + (t.meter.steps - meter0);
  t.stats.oe_steps <- t.stats.oe_steps + (oe_eval_weight * (t.meter.steps - meter0));
  let spent =
    match t.config.clock with
    | Allocation ->
        let allocated = clock t -. w0 in
        let counted = float_of_int (t.stats.oe_steps - steps0) /. oe_steps_per_unit in
        let extra = Float.max 0. (counted -. allocated) in
        t.counted <- t.counted +. extra;
        t.turn_counted <- extra;
        allocated +. extra
    | Events ->
        (* The clock already holds the evaluation steps and the probes' events; the
           enumeration's own steps are added here. *)
        let own = t.stats.oe_steps - steps0 - (oe_eval_weight * (t.meter.steps - meter0)) in
        t.ev <- t.ev +. (float_of_int own /. oe_steps_per_unit);
        clock t -. w0
  in
  t.stats.oe_seconds <- t.stats.oe_seconds +. (Telemetry.now () -. t0);
  t.stats.oe_work <- t.stats.oe_work +. spent;
  if retry then t.oe_retry_work <- t.oe_retry_work +. spent
  else t.oe_fresh_work <- t.oe_fresh_work +. spent

(* The instance sub-lane's other work: probes and the look-ahead. *)
let others_ready t =
  (not (Pending.is_empty t.fresh)) || (not (Pending.is_empty t.killers)) || scan_ready t

let instance_turn t =
  match t.mace_builder with
  | Some b -> (
      match Mace.advance b ~quota:pool_quota with
      | Some p ->
          t.pool <- Some p;
          (match t.config.clock with
          | Allocation -> ()
          | Events -> t.ev <- t.ev +. (ev_eval_rate *. float_of_int (Mace.steps b)));
          t.mace_builder <- None;
          t.stats.pool_models <- List.length p.models
      | None -> ())
  | None -> (
      match t.builder with
      | Some b -> (
          match Semantic.advance b ~quota:pool_quota with
          | Some p ->
              t.pool <- Some p;
              (* [Events]: the finished builder's steps stay on the lane's clock. *)
              (match t.config.clock with
              | Allocation -> ()
              | Events -> t.ev <- t.ev +. (ev_eval_rate *. float_of_int (Semantic.builder_steps b)));
              t.builder <- None;
              t.stats.pool_models <- List.length p.models
          | None -> ())
      | None ->
          if
            oe_ready t
            && ((not (others_ready t))
               || t.stats.oe_work <= t.config.oe_share *. t.stats.instance_work)
          then oe_turn t
          else if
            luby_ready t
            && ((not (others_ready t))
               || t.stats.luby_work <= t.config.luby_share *. t.stats.instance_work)
          then luby_turn t
          else if ranking t then (
            (* Pool mode: scan turns alternate with probe turns. *)
            t.scan_turn <- not t.scan_turn;
            if t.scan_turn && scan_ready t then scan t else probe_ranked t)
          else (
            if Pending.is_empty t.fresh && scan_ready t then scan t;
            probe_ranked t))

(* The next prior item of this worker's share (index mod workers). *)
let rec next_prior t =
  match t.prior_pending with
  | item :: rest ->
      t.prior_pending <- rest;
      Some item
  | [] -> (
      if t.prior_index >= t.config.prior_cap then None
      else
        match t.prior_stream () with
        | Seq.Nil ->
            t.prior_index <- t.config.prior_cap;
            None
        | Seq.Cons (d, rest) ->
            t.prior_stream <- rest;
            let index = t.prior_index in
            t.prior_index <- index + 1;
            if index mod t.workers <> t.worker then next_prior t
            else
              let items =
                match Wire.import (Theory.arena t.theory) d with
                | exception Invalid_argument _ -> []
                | phi ->
                    List.filter_map
                      (fun schema ->
                        match Theory.guided_parameter t.theory schema phi with
                        | Some p when not (Hashtbl.mem t.queued (schema, p)) ->
                            Hashtbl.replace t.queued (schema, p) ();
                            Some
                              {
                                schema;
                                parameter = p;
                                source = Prior;
                                level = 0;
                                killer = false;
                                shape = -1;
                              }
                        | _ -> None)
                      (Theory.schemas t.theory)
              in
              t.prior_pending <- items;
              next_prior t)

let prior_ready t =
  Option.is_some t.config.prior && t.synthesis && t.finite <> None
  && ((not (Pending.is_empty t.prior_retry))
     || (not (Pending.is_empty t.prior_killers))
     || (not (Pending.is_empty t.prior_backlog))
     || t.prior_pending <> []
     || t.prior_index < t.config.prior_cap)

(* With a ready pool, rank instead of filter: classify the next prior
   conditions (killers first, at [killer_level]; the others keep their order
   in a backlog), because pool models come from the subset of fixed axioms
   that has small models and may miss a needle. Bounded per turn by [scan]
   candidates, [turn_steps] evaluation steps and the deadline. *)
let classify_prior t =
  let budget = ref (max 1 t.config.scan) and steps = t.meter.steps in
  while
    !budget > 0 && Pending.is_empty t.prior_killers
    && t.meter.steps - steps < t.config.turn_steps
    && not (past_deadline t)
  do
    decr budget;
    match next_prior t with
    | None -> budget := 0
    | Some item ->
        t.stats.prior <- t.stats.prior + 1;
        if is_killer t item.schema item.parameter then (
          t.stats.killers <- t.stats.killers + 1;
          enqueue t t.prior_killers { item with killer = true; level = t.config.killer_level })
        else if Pending.length t.prior_backlog < t.config.prior_cap then
          enqueue t t.prior_backlog item
  done

let next_fresh_prior t =
  if ready_pool t = None then (
    let item = next_prior t in
    if item <> None then t.stats.prior <- t.stats.prior + 1;
    item)
  else (
    classify_prior t;
    match Pending.take_oldest t.prior_killers with
    | Some _ as killer -> killer
    | None -> Pending.take_oldest t.prior_backlog)

(* Fresh prior conditions and re-probes share the sub-lane by work. *)
let prior_turn t =
  let w0 = clock t in
  let retry = (not (Pending.is_empty t.prior_retry)) && t.prior_retry_work <= t.prior_fresh_work in
  let item =
    if retry then Pending.take_oldest t.prior_retry
    else match next_fresh_prior t with None -> Pending.take_oldest t.prior_retry | some -> some
  in
  Option.iter (fun item -> escalate t t.prior_retry item (probe t item)) item;
  let spent = clock t -. w0 in
  if retry then t.prior_retry_work <- t.prior_retry_work +. spent
  else t.prior_fresh_work <- t.prior_fresh_work +. spent

let instance_ready t =
  t.builder <> None || t.mace_builder <> None || others_ready t || oe_ready t || luby_ready t

let fixed_ready t = not t.fixed_done
let has_work t = t.result = None && (fixed_ready t || instance_ready t || prior_ready t)

(* The main engine injected [parameter] (instance formula [formula], when the
   caller has it): queue it for its probe. *)
let offer ?formula t schema parameter =
  if not (Hashtbl.mem t.queued (schema, parameter)) then (
    Hashtbl.replace t.queued (schema, parameter) ();
    t.stats.offered <- t.stats.offered + 1;
    let shape =
      match formula with Some f -> shape_of t f | None -> shape_of_parameter t schema parameter
    in
    Hashtbl.replace t.waiting (schema, parameter) ();
    enqueue t t.fresh { schema; parameter; source = Injected; level = 0; killer = false; shape })

(* May the lane take a turn now (its work is within [share] of all work
   since the lane started, the main engine's work at its exchange rate:
   [main_weight] on the allocation clock, [calibrated_main_weight] in the
   default; the events clock's [main_work] already carries [ev_main])? *)
let due t =
  t.result = None
  &&
  let lane = work t in
  let weight = match t.config.clock with Allocation -> t.config.main_weight | Events -> 1. in
  lane <= t.config.share *. (lane +. (weight *. main_work t))

(* One lane activity: the ready sub-lane with the least cumulative (weighted)
   work. Its work is the allocation of this turn. No turn starts after the
   deadline. *)
let turn t =
  if has_work t && not (past_deadline t) then (
    let t0 = Telemetry.now () and w0 = clock t in
    t.stats.turns <- t.stats.turns + 1;
    let fixed_weight =
      if t.next_slice >= t.config.fixed_slice_cap then t.config.fixed_late_weight else 1.
    in
    let candidates =
      (if fixed_ready t then [ (t.stats.fixed_work /. fixed_weight, `Fixed) ] else [])
      @ (if instance_ready t then [ (t.stats.instance_work, `Instance) ] else [])
      @ if prior_ready t then [ (t.stats.prior_work, `Prior) ] else []
    in
    let lane =
      match List.sort (fun (a, _) (b, _) -> compare a b) candidates with
      | (_, l) :: _ -> l
      | [] -> `Instance
    in
    Fun.protect
      ~finally:(fun () ->
        (* At least a word per turn, so that an empty turn is not free; work
           counted beyond allocation (observational turns) is added. *)
        let spent = Float.max (1. /. 1024.) (clock t -. w0) +. t.turn_counted in
        t.turn_counted <- 0.;
        (match lane with
        | `Fixed -> t.stats.fixed_work <- t.stats.fixed_work +. spent
        | `Instance -> t.stats.instance_work <- t.stats.instance_work +. spent
        | `Prior -> t.stats.prior_work <- t.stats.prior_work +. spent);
        t.stats.seconds <- t.stats.seconds +. (Telemetry.now () -. t0))
      (fun () ->
        match lane with
        | `Fixed -> fixed_turn t
        | `Instance -> instance_turn t
        | `Prior -> prior_turn t))

(* Breadth: the largest share of the probe work taken by one schema and by
   one (schema, shape) class, and distinct classes per 1,000 work units of
   probe work. *)
let top_schema_share (s : stats) =
  if s.probe_work > 0. then s.top_schema_work /. s.probe_work else 0.

let top_shape_share (s : stats) = if s.probe_work > 0. then s.top_shape_work /. s.probe_work else 0.

let shape_rate (s : stats) =
  if s.probe_work > 0. then 1000. *. float_of_int s.shapes_probed /. s.probe_work else 0.

(* Fields of the evaluation options, only when one differs from the default (the default
   line is unchanged): the clock and exchange rate (an allocation clock at another
   [main_weight], e.g. the uncalibrated rate 1); with [Events], the main engine's events, the
   lane engines' events and allocation, the look-ahead's polls and allocation (calibration
   data); the re-probes of non-killers. *)
let extra_summary t =
  let s = t.stats and c = t.config in
  (match c.clock with
    | Allocation when c.main_weight = calibrated_main_weight -> ""
    | Allocation -> Printf.sprintf " clock=alloc main_weight=%.3g" c.main_weight
    | Events ->
        Printf.sprintf
          " clock=events main_events=%.0f lane_ev=%d/%.0f polls=%d/%.0f evals=%d capped=%d"
          (main_units t -. t.main_events_start)
          s.ev_engine_events s.ev_engine_alloc s.ev_polls s.ev_poll_alloc
          (t.meter.steps + builder_steps t)
          s.ev_capped)
  ^ (if luby_on t then Printf.sprintf " luby=%d/%.0f" s.luby_probes s.luby_work else "")
  ^ if c.mace then Printf.sprintf " mace=%d" s.mace_rejected else ""

let summary t =
  let s = t.stats in
  Printf.sprintf
    " [lane: turns=%d probes=%d reprobes=%d fixed_slices=%d work=%.0f/%.0f/%.0f main=%.0f \
     offered=%d scanned=%d killers=%d prior=%d injected=%d pool=%d%s refined=%d charged=%d/%d \
     refused=%d expensive=%d stored=%d schemas=%d/%d shapes=%d shape_rate=%.2f top_schema=%.2f \
     top_shape=%.2f seconds=%.3f promoted=%d%s%s]"
    s.turns s.probes s.reprobes s.fixed_slices s.fixed_work s.instance_work s.prior_work
    (main_work t) s.offered s.scanned s.killers s.prior s.injected s.pool_models
    (if s.weak then "(weak)" else "")
    s.refined s.charged_exhaustive s.charged_guided s.refused s.expensive_streams s.peak_stored
    s.schemas_probed s.schemas s.shapes_probed (shape_rate s) (top_schema_share s)
    (top_shape_share s) s.seconds s.promoted
    (* Observational source: work/offered/killers/probes/rebuilds/kept/words. *)
    (if t.config.observational then
       Printf.sprintf " oe=%.0f/%d/%d/%d/%d/%d/%d steps=%d/%d oe_seconds=%.3f" s.oe_work
         s.oe_offered s.oe_killers s.oe_probes s.oe_rebuilds s.oe_kept s.oe_words s.oe_steps
         s.oe_evaluations s.oe_seconds
     else "")
    (extra_summary t ^ if s.winner = "" then "" else " FOUND:" ^ s.winner)
