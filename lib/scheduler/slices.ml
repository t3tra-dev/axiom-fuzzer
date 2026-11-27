(** Single-worker slice schedule over probe lanes (pure; no engine state).

    A sliced worker runs one continuing engine (the worker's own phase and strategy) and probe
    engines on the same axioms. The continuing engine is suspended while a probe slice runs and
    resumed afterwards; it is never restarted. Slices are measured in engine steps (one
    [Engine.step] call each), generated clauses or the deterministic work clock
    ([Engine.work_reading]), never in wall time, so the slice sequence is a function of the input.

    Slice [2i] is a continuing slice and slice [2i + 1] a probe slice, for [i = 0, 1, ...]. The
    probe slices cycle through [lanes]: probe slice [i] runs lane [i mod n] in round [r = i / n]
    ([n] lanes) for [unit_steps * factor r] steps, and the continuing slice before it runs
    [main_ratio] times as many. Every lane therefore sees the same budget sequence, and at every
    slice boundary the continuing engine has received at least [main_ratio / (main_ratio + 1)] of
    the steps handed out. With [rounds > 0], every lane gets [rounds] probe slices and the
    continuing engine then runs alone ([Rest]). A restart lane starts a fresh engine for each of its
    slices; a resumed lane keeps one suspended engine, shared by every equal resumed lane of the
    cycle.

    The share counts slice work only. Admitting the inputs into a new probe engine is extra work
    that a step budget does not count (a generated-clause or work-clock budget does);
    [probe_admitted] and [probe_admit_seconds] report it.

    With [carry] (deficit carry-over), the budgets accumulate instead: every engine's cumulative
    work tracks the cumulative budget its slices were handed. A slice runs the budget handed out so
    far minus the work already done (a step can overshoot its slice; the next slice of that engine
    is shorter by as much), and is skipped when an earlier slice already covered it. The work share
    then holds over the whole run, not only at slice boundaries.

    [share] is the default of one [Balanced] worker whose input has no schemas
    ([Scheduler.single_slices]): production as the continuing engine and one resumed lane of the
    first diversified member ([Strategy.diversified], e208) at the worker's queue phase, 1:1 in
    work-clock slices of about 50 ms with carry-over. It is the two-worker balanced composition on
    one worker. *)

type sequence =
  | Luby  (** [factor r] is the Luby sequence 1 1 2 1 1 2 4 ... per lane *)
  | Geometric of int  (** [factor r = g ^ r] *)

type lane = {
  offset : int;  (** Passive phase relative to the worker's own phase. *)
  strategy : Strategy.t option;  (** [None]: the worker's strategy. *)
  restart : bool;  (** A fresh engine per slice, or the lane's resumed engine. *)
}

(** The work unit of slice budgets. [Steps] counts [Engine.step] calls. [Generated] counts generated
    clauses (the engine's [generated] metric); such a slice also ends after [16] steps per unit of
    budget, so an engine that stops generating cannot hold the worker. [Work] reads the work clock
    ([Engine.work_reading]: words the worker's domain allocated plus [Engine.check_words] per
    cooperative check of the running engine), which tracks time but repeats exactly for the same
    input and binary; every step adds at least one check, so no engine holds the worker. *)
type measure = Steps | Generated | Work

type policy = {
  lanes : lane list;  (** The probe cycle; [[]] disables slicing. *)
  unit_work : int;  (** Work units in a factor-1 probe slice. *)
  measure : measure;
  sequence : sequence;
  main_ratio : int;  (** Continuing work per probe work (at least 1). *)
  rounds : int;
      (** Probe slices per lane; afterwards the continuing engine runs alone. [0]: no limit. *)
  carry : bool;  (** Deficit carry-over (resumed lanes only). *)
}

(* A compact description from which policies are built; also the grammar of
   the AXIOM_SLICES experiment hook. [phases] restart-or-resume lanes run the
   worker's strategy at offsets 1..phases; [e] occurrences of one resumed
   proto:e lane at offset 0 are spread over the cycle, starting with it; then
   one lane per [members] strategy at offset 0 (restart or resume as the phase
   lanes). *)
type spec = {
  phases : int;
  restart : bool;
  e : int;
  members : Strategy.t list;
  unit : int;
  measure_spec : measure;
  sequence_spec : sequence;
  ratio : int;
  round_limit : int;  (** [rounds] of the policy *)
  carry_spec : bool;
}

let e_lane = { offset = 0; strategy = Some Strategy.proto_e; restart = false }

let lanes_of spec =
  let phase k = { offset = k; strategy = None; restart = spec.restart } in
  let members =
    List.map (fun s -> { offset = 0; strategy = Some s; restart = spec.restart }) spec.members
  in
  if spec.phases = 0 then (if spec.e > 0 then [ e_lane ] else []) @ members
  else
    (* ceil((i + 1) e / phases) - ceil(i e / phases) copies of the e lane
       before phase lane i + 1. *)
    let ceil_div a b = (a + b - 1) / b in
    List.concat
      (List.init spec.phases (fun i ->
           let copies =
             ceil_div ((i + 1) * spec.e) spec.phases - ceil_div (i * spec.e) spec.phases
           in
           List.init copies (fun _ -> e_lane) @ [ phase (i + 1) ]))
    @ members

let build spec =
  {
    lanes = lanes_of spec;
    unit_work = spec.unit;
    measure = spec.measure_spec;
    sequence = spec.sequence_spec;
    main_ratio = spec.ratio;
    rounds = spec.round_limit;
    carry = spec.carry_spec;
  }

let off_spec =
  {
    phases = 0;
    restart = true;
    e = 0;
    members = [];
    unit = 1;
    measure_spec = Steps;
    sequence_spec = Luby;
    ratio = 1;
    round_limit = 0;
    carry_spec = false;
  }

(** No slices: the continuing engine runs alone. *)
let off = build off_spec

(** The opt-in candidate ([AXIOM_SLICES=on]), chosen from the per-phase grid: one visit of 512 steps
    to each of the seven queue phases a portfolio of eight workers would add (every observed probe
    win took 158-376 steps of its phase's first visit), interleaved 1:1 with continuing slices; then
    the continuing engine runs alone. Probes therefore cost at most seven 512-step slices and seven
    input admissions, and no lane repeats a search. *)
let candidate_spec =
  {
    phases = 7;
    restart = true;
    e = 0;
    members = [];
    unit = 512;
    measure_spec = Steps;
    sequence_spec = Luby;
    ratio = 1;
    round_limit = 1;
    carry_spec = false;
  }

let candidate = build candidate_spec

(** The single-worker share ([share], the CLI default of one [Balanced] worker on an input without
    schemas): the first diversified member, resumed at offset 0, alternating 1:1 with the continuing
    engine in constant work-clock slices of [Engine.work_units_per_second / 20] units (about 50 ms
    on a quiet performance core; the e208 lane's first slice also pays for admitting the input),
    with deficit carry-over and no round limit. *)
let share_spec =
  {
    phases = 0;
    restart = false;
    e = 0;
    members = [ List.hd Strategy.diversified ];
    unit = int_of_float (Engine.work_units_per_second /. 20.);
    measure_spec = Work;
    sequence_spec = Geometric 1;
    ratio = 1;
    round_limit = 0;
    carry_spec = true;
  }

let share = build share_spec
let enabled p = p.lanes <> []
let min_work_unit = 10_000

let validate p =
  if List.length p.lanes > 64 then invalid_arg "at most 64 slice lanes";
  if List.exists (fun l -> l.offset < 0 || l.offset > 1_000_000) p.lanes then
    invalid_arg "slice lane offsets must be between 0 and 1000000";
  if p.unit_work < 1 || p.unit_work > 1_000_000_000 then
    invalid_arg "slice unit must be between 1 and 1000000000";
  if p.main_ratio < 1 || p.main_ratio > 1_000_000 then
    invalid_arg "continuing share ratio must be between 1 and 1000000";
  if p.rounds < 0 || p.rounds > 1_000_000 then
    invalid_arg "slice rounds must be between 0 and 1000000";
  if p.carry && List.exists (fun (l : lane) -> l.restart) p.lanes then
    invalid_arg "slice carry-over needs resumed lanes";
  (* Reading the work clock and switching engines allocate a few dozen words. A slice whose
     budget they already cover passes its turn without a step, and that bookkeeping is charged
     to it; a unit far above it keeps every engine moving (the next slice owes almost a whole
     unit). *)
  if p.measure = Work && p.unit_work < min_work_unit then
    invalid_arg (Printf.sprintf "work-clock slices need a unit of at least %d" min_work_unit);
  match p.sequence with
  | Geometric g when g < 1 || g > 64 ->
      invalid_arg "geometric slice factor must be between 1 and 64"
  | _ -> ()

(* Luby et al. 1993: t_i = 2^(k-1) when i = 2^k - 1, else t_(i - 2^(k-1) + 1),
   for 1-based i. *)
let luby index =
  if index < 0 then invalid_arg "Slices.luby: negative index";
  let rec go i =
    let rec size k = if (1 lsl k) - 1 >= i then k else size (k + 1) in
    let k = size 1 in
    if (1 lsl k) - 1 = i then 1 lsl (k - 1) else go (i - (1 lsl (k - 1)) + 1)
  in
  go (index + 1)

let cap = 1 lsl 40

let factor p index =
  let round = index / max 1 (List.length p.lanes) in
  match p.sequence with
  | Luby -> luby round
  | Geometric 1 -> 1 (* constant slices: O(1) at any index, as the share needs *)
  | Geometric g ->
      let rec power acc n = if n = 0 || acc >= cap then min acc cap else power (acc * g) (n - 1) in
      power 1 round

(* The continuing slice is exactly [main_ratio] probe slices long, so the
   probe budget saturates at [cap / main_ratio] without overflowing. *)
let probe_steps p index =
  let limit = cap / p.main_ratio and f = factor p index in
  if f > limit / p.unit_work then limit else min limit (p.unit_work * f)

(** The largest budget [probe_steps] ever gives a probe slice of [p]: the factor-1 budget of
    constant slices ([Geometric 1]); otherwise the limit [cap / main_ratio], which Luby and growing
    sequences reach. *)
let max_probe_steps p =
  match p.sequence with Geometric 1 -> probe_steps p 0 | Luby | Geometric _ -> cap / p.main_ratio

(** Engine identity of a lane: restart lanes never share an engine; equal resumed lanes do. *)
let key position (lane : lane) =
  if lane.restart then `Restart position
  else `Resumed (lane.offset, Option.map (fun (s : Strategy.t) -> s.name) lane.strategy)

type slice =
  | Main of int
  | Probe of { lane : int; index : int; steps : int; fresh : bool }
  | Rest  (** The continuing engine runs alone until the search ends. *)

(** The [n]th slice (0-based) of an enabled policy. [fresh] says that the slice starts a new engine:
    always for a restart lane, and for the first slice of a resumed engine. *)
let slice p n =
  if not (enabled p) then invalid_arg "Slices.slice: slicing is disabled";
  if n < 0 then invalid_arg "Slices.slice: negative slice";
  let index = n / 2 in
  let steps = probe_steps p index in
  if p.rounds > 0 && index >= p.rounds * List.length p.lanes then Rest
  else if n mod 2 = 0 then Main (p.main_ratio * steps)
  else
    let count = List.length p.lanes in
    let position = index mod count in
    let (lane : lane) = List.nth p.lanes position in
    let first_use () =
      index < count
      && not
           (List.exists
              (fun (j, other) -> j < position && key j other = key position lane)
              (List.mapi (fun j l -> (j, l)) p.lanes))
    in
    Probe { lane = position; index; steps; fresh = lane.restart || first_use () }

let lane_name (lane : lane) =
  Printf.sprintf "%s+%d%s"
    (match lane.strategy with None -> "worker" | Some s -> s.name)
    lane.offset
    (if lane.restart then "" else "~")

let name p =
  if not (enabled p) then "off"
  else
    Printf.sprintf "[%s] unit=%d%s %s ratio=%d%s%s"
      (String.concat " " (List.map lane_name p.lanes))
      p.unit_work
      (match p.measure with Steps -> "" | Generated -> " generated" | Work -> " work")
      (match p.sequence with Luby -> "luby" | Geometric g -> "geometric:" ^ string_of_int g)
      p.main_ratio
      (if p.rounds = 0 then "" else Printf.sprintf " rounds=%d" p.rounds)
      (if p.carry then " carry" else "")

type stats = {
  policy : string;
  mutable main_slices : int;
  mutable probe_slices : int;
  mutable main_steps : int;
  mutable probe_steps : int;
  mutable main_work : int;  (** in the policy's measure *)
  mutable probe_work : int;
  mutable main_seconds : float;
  mutable probe_seconds : float;
  mutable probes_created : int;
  mutable probe_given : int;
  mutable probe_generated : int;
  mutable probe_admitted : int;
      (** Input clauses admitted into probe engines (counted in [probe_generated]). *)
  mutable probe_admit_seconds : float;  (** Creating probe engines and admitting their inputs. *)
  mutable probe_skipped : int;
      (** Restart-lane slices skipped because a fresh engine of the lane already searched at least
          that budget on the same axioms. *)
  mutable probe_revived : int;  (** Saturated lanes resumed after the axioms grew. *)
  mutable probe_late_axioms : int;
      (** Axioms copied into a resumed probe after its first slice (instances injected by the
          continuing engine in between). *)
  mutable live_probes : int;
  mutable peak_live_probes : int;
  mutable winner : string;  (** [lane_name] of a probe proof; "" otherwise *)
  mutable winner_slice : int;  (** probe slice index of a probe proof, else -1 *)
  mutable alone_slices : int;
      (** Probe slices that ran after the continuing engine ended on its own (without a proof, and
          not at the deadline or a cancellation), when the lanes keep the worker's remaining time;
          included in [probe_slices]. *)
  mutable alone_work : int;  (** their work, included in [probe_work] *)
}
(** Per-worker slice accounting. Seconds are telemetry only; the schedule never reads them.
    [probe_slices] counts the probe slices that ran; skipped ones are not included. *)

let stats p =
  {
    policy = name p;
    main_slices = 0;
    probe_slices = 0;
    main_steps = 0;
    probe_steps = 0;
    main_work = 0;
    probe_work = 0;
    main_seconds = 0.;
    probe_seconds = 0.;
    probes_created = 0;
    probe_given = 0;
    probe_generated = 0;
    probe_admitted = 0;
    probe_admit_seconds = 0.;
    probe_skipped = 0;
    probe_revived = 0;
    probe_late_axioms = 0;
    live_probes = 0;
    peak_live_probes = 0;
    winner = "";
    winner_slice = -1;
    alone_slices = 0;
    alone_work = 0;
  }

(** Continuing share of the work done in slices, in the policy's measure (1 when nothing was
    sliced). *)
let main_share s =
  let total = s.main_work + s.probe_work in
  if total = 0 then 1. else float s.main_work /. float total

(** ["off"], ["on"] ([base]), ["share"] ([share]), or comma-separated overrides of [base] (of
    [share_spec] when the first item is [share]): [phases=N] [e=N] [members=NAME+NAME...] (strategy
    names; [members=] alone: none) [unit=N] [ratio=N] [rounds=N] ([0]: unbounded) [luby]
    [geometric=G] [restart] [resume] [steps] [generated] [work] [carry] [nocarry]. *)
let parse ?(base = candidate_spec) text =
  match String.trim text with
  | "off" -> off
  | "on" -> build base
  | "share" -> share
  | spec ->
      let field s item =
        match String.split_on_char '=' (String.trim item) with
        | [ "luby" ] -> { s with sequence_spec = Luby }
        | [ "steps" ] -> { s with measure_spec = Steps }
        | [ "generated" ] -> { s with measure_spec = Generated }
        | [ "work" ] -> { s with measure_spec = Work }
        | [ "carry" ] -> { s with carry_spec = true }
        | [ "nocarry" ] -> { s with carry_spec = false }
        | [ "restart" ] -> { s with restart = true }
        | [ "resume" ] -> { s with restart = false }
        | [ "members"; "" ] -> { s with members = [] }
        | [ "members"; names ] ->
            { s with members = List.map Strategy.of_name (String.split_on_char '+' names) }
        | [ key; value ] -> (
            let n =
              match int_of_string_opt value with
              | Some n -> n
              | None -> invalid_arg ("slice option " ^ key ^ " needs an integer")
            in
            if n < 0 then invalid_arg ("slice option " ^ key ^ " must be nonnegative");
            match key with
            | "phases" -> { s with phases = n }
            | "e" -> { s with e = n }
            | "unit" -> { s with unit = n }
            | "geometric" -> { s with sequence_spec = Geometric n }
            | "ratio" -> { s with ratio = n }
            | "rounds" -> { s with round_limit = n }
            | _ -> invalid_arg ("unknown slice option " ^ key))
        | _ -> invalid_arg ("malformed slice option " ^ item)
      in
      let base, items =
        match List.map String.trim (String.split_on_char ',' spec) with
        | "share" :: rest -> (share_spec, rest)
        | items -> (base, items)
      in
      let s = List.fold_left field base items in
      if s.phases > 64 || s.e > 64 || List.length s.members > 64 then
        invalid_arg "at most 64 phase, 64 e and 64 member lanes";
      let p = build s in
      validate p;
      p
