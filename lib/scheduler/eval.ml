(* Evaluation-only switches: every AXIOM_* environment variable that changes or instruments a
   search of axiom-fuzz. They exist for measurements, A/B runs against earlier rules and
   diagnostics, and none of them is a user option: with all of them unset the default search runs
   exactly, and when one is set the CLI says so on standard error ([note]). [switches] is the one
   list of them (docs/evaluation-switches.md shows it, `axiom-fuzz --eval-help` prints it), and
   [of_env] is the one parser. Parsing sets the same configuration fields and process-global hooks
   that the search reads; it adds nothing to the search itself. *)

type kind =
  | Search  (** changes the search *)
  | Certificate  (** changes the certificate of a found proof, not the search *)
  | Measurement  (** changes how a run is clocked, isolated or traced *)
  | Diagnostic  (** prints internal counters on standard error *)

let kind_name = function
  | Search -> "search"
  | Certificate -> "certificate"
  | Measurement -> "measurement"
  | Diagnostic -> "diagnostic"

type switch = {
  name : string;
  values : string;  (** the accepted values *)
  default : string;  (** what an unset variable means *)
  unset : string list;  (** values that mean the same as an unset variable *)
  kind : kind;
  doc : string;
}

let switch ?(unset = []) name kind ~values ~default doc =
  { name; values; default; unset; kind; doc }

let diagnostic name doc =
  switch name Diagnostic ~values:"any value but 0" ~default:"off" ~unset:[ ""; "0" ] doc

let switches =
  [
    switch "AXIOM_PHASE_BASE" Search ~values:"integer 0..1000000" ~default:"0"
      "Adds K to every worker's queue phase (worker 0 starts at phase K).";
    switch "AXIOM_EQ_UNFOLD" Search ~values:"off, on, or an integer limit -1000000..1000000"
      ~default:"each strategy's own setting"
      "Replaces the equational-definition unfolding of every worker strategy: off, on with E's \
       eq-unfold-limit, or on with the given limit.";
    switch "AXIOM_LEAN_NF" Search ~values:"rewrite, both, given or off" ~default:"rewrite"
      "Sets the lean workers' normal-form rewriting and immediate processing of a simplified given \
       clause: the rewriting only, both, the immediate processing only, or neither (production's \
       one-step admission and re-queued given).";
    switch "AXIOM_LEAN_EQ" Search ~values:"on, off, or a comma-separated subset of inst, gj, cc"
      ~default:"off"
      "Sets the unit-equality redundancy tests (EQ-UNIT) of the lean workers with ordered \
       rewriting: instances, ground joinability and connectedness.";
    switch "AXIOM_EQUIVALENCE" Search ~values:"redundant, legacy or derive" ~default:"derive"
      "Chooses when Contraction's literal rewriting with an equivalence may retire the rewritten \
       clause: only as a redundancy deletion (redundant); on any strict decrease, units included \
       (legacy, a refutationally incomplete rule kept for A/B runs); or as redundant, with the \
       other rewrites added as consequences without retiring anything (derive).";
    switch "AXIOM_LEAN_LOOP" Search
      ~values:"ported, e, presat, or a comma-separated list of loop details"
      ~default:"each heuristic's own loop"
      "Replaces the E loop details of every ported E heuristic worker.";
    switch "AXIOM_LANE" Search ~values:"comma-separated key=value overrides"
      ~default:"the default probe lane"
      "Overrides the schema probe lane's evaluation options: clock=alloc|events, main_weight, \
       ev_main, ev_engine, ev_raw, luby, luby_levels, share, mace, mace_precheck, oe, pad=T:A.";
    switch "AXIOM_SLICES" Search ~values:"off, on, share, or overrides of the slice candidate"
      ~default:"share for one worker on an input without schemas"
      "Replaces the probe slices of a single worker whatever its portfolio and input; members= can \
       name any strategy.";
    switch "AXIOM_GROUND_EXPLANATION" Certificate ~values:"forest or short" ~default:"short"
      "Chooses how the ground congruence closure explains a conflict: along the union-find forest \
       (forest) or, for a long final conflict, along the cheapest paths with shared lemmas \
       (short). The certificate changes, the search does not.";
    switch "AXIOM_AVATAR_REFUTATION" Certificate ~values:"incremental or smaller" ~default:"smaller"
      "Chooses the Boolean refutation of an AVATAR certificate outside the Vampire members: the \
       incremental solver's (incremental), or the one with fewer steps of the incremental and a \
       fresh re-solve of the same inputs after pruning (smaller).";
    switch "AXIOM_MEASURE_COST_CLOCK" Measurement ~values:"wall or stopped" ~default:"wall"
      ~unset:[ ""; "wall" ]
      "stopped charges the scheduling costs to a stopped clock, so that a bounded search depends \
       on its input alone (the time limit still reads the wall clock).";
    switch "AXIOM_MEASURE_REFERENCE" Measurement ~values:"on or off" ~default:"on"
      ~unset:[ ""; "on" ]
      "off runs no reference worker, so that a search that caps end stops with its heuristic \
       workers (the reference worker runs to the wall limit). For tests and identity checks; \
       --checkpoint needs the reference worker.";
    switch "AXIOM_MEASURE_PORTFOLIO" Measurement ~values:"processes or domains" ~default:"processes"
      ~unset:[ ""; "processes" ]
      "Runs the portfolio as forked processes or as Domains of one process.";
    switch "AXIOM_MEASURE_GIVEN_TRACE" Measurement ~values:"a file prefix" ~default:"off"
      ~unset:[ "" ]
      "Every lean (ported E heuristic) worker writes one line per given clause to the file \
       PREFIX.PID of its process, to compare its given clauses with E's.";
    switch "AXIOM_MEASURE_EVAL_TRACE" Measurement ~values:"a file prefix" ~default:"off"
      ~unset:[ "" ] "The same for every clause that enters Passive, with its evaluations.";
    switch "AXIOM_MEASURE_NEW_TRACE" Measurement ~values:"any value but 0" ~default:"off"
      ~unset:[ ""; "0" ]
      "With AXIOM_MEASURE_GIVEN_TRACE, also writes every clause that enters Passive.";
    diagnostic "AXIOM_EQ_UNFOLD_REPORT"
      "Every engine that unfolds equational definitions prints what it removed and rewrote.";
    diagnostic "AXIOM_LEAN_EQ_REPORT"
      "Every lean worker that ran an EQ-UNIT redundancy test prints its counters when it stops.";
    diagnostic "AXIOM_EQUIVALENCE_REPORT"
      "Every engine prints its counters of literal rewriting with equivalences when it stops.";
    diagnostic "AXIOM_VAMPIRE_ORDERING"
      "Every Vampire slice member prints its precedence, KBO weights and predicate levels.";
  ]

(* The search switches, applied in this order to the CLI's configuration. An empty value is
   invalid for each of them. *)
let configure getenv (config : Scheduler.config) =
  let config =
    match getenv "AXIOM_PHASE_BASE" with
    | None -> config
    | Some text -> (
        match int_of_string_opt (String.trim text) with
        | Some k when k >= 0 && k <= 1_000_000 -> { config with phase_base = k }
        | _ -> invalid_arg "AXIOM_PHASE_BASE must be an integer between 0 and 1000000")
  in
  let config =
    match getenv "AXIOM_EQ_UNFOLD" with
    | None -> config
    | Some text -> (
        match String.trim text with
        | "off" -> { config with unfold = Some None }
        | "on" -> { config with unfold = Some (Some Unfold.default_limit) }
        | text -> (
            match int_of_string_opt text with
            | Some k when abs k <= 1_000_000 -> { config with unfold = Some (Some k) }
            | _ ->
                invalid_arg
                  "AXIOM_EQ_UNFOLD must be off, on or an integer limit between -1000000 and 1000000"
            ))
  in
  let config =
    match getenv "AXIOM_LEAN_NF" with
    | None -> config
    | Some text ->
        let normal_form, given_at_once =
          match String.trim text with
          | "rewrite" -> (true, false)
          | "both" -> (true, true)
          | "given" -> (false, true)
          | "off" -> (false, false)
          | _ -> invalid_arg "AXIOM_LEAN_NF must be rewrite, both, given or off"
        in
        { config with engine = { config.engine with normal_form; given_at_once } }
  in
  let config =
    match getenv "AXIOM_LEAN_EQ" with
    | None -> config
    | Some text ->
        let parts =
          match String.trim text with
          | "on" -> [ "inst"; "gj"; "cc" ]
          | "off" -> []
          | text -> List.map String.trim (String.split_on_char ',' text)
        in
        List.iter
          (fun p ->
            if not (List.mem p [ "inst"; "gj"; "cc" ]) then
              invalid_arg
                "AXIOM_LEAN_EQ must be on, off or a comma-separated subset of inst, gj, cc")
          parts;
        {
          config with
          engine =
            {
              config.engine with
              eq_instances = List.mem "inst" parts;
              eq_ground_joinable = List.mem "gj" parts;
              eq_connected = List.mem "cc" parts;
            };
        }
  in
  let config =
    match getenv "AXIOM_EQUIVALENCE" with
    | None -> config
    | Some text -> (
        match String.trim text with
        | "redundant" ->
            { config with engine = { config.engine with equivalence = Contraction.Redundant } }
        | "legacy" ->
            { config with engine = { config.engine with equivalence = Contraction.Legacy } }
        | "derive" ->
            { config with engine = { config.engine with equivalence = Contraction.Derive } }
        | _ -> invalid_arg "AXIOM_EQUIVALENCE must be redundant, legacy or derive")
  in
  let config =
    match getenv "AXIOM_GROUND_EXPLANATION" with
    | None -> config
    | Some text -> (
        match Ground.explanation_of_string (String.trim text) with
        | explanation ->
            { config with engine = { config.engine with ground_explanation = explanation } }
        | exception Invalid_argument _ ->
            invalid_arg "AXIOM_GROUND_EXPLANATION must be forest or short")
  in
  let config =
    match getenv "AXIOM_AVATAR_REFUTATION" with
    | None -> config
    | Some text -> (
        match String.trim text with
        | "incremental" -> { config with engine = { config.engine with fresh_refutation = false } }
        | "smaller" -> { config with engine = { config.engine with fresh_refutation = true } }
        | _ -> invalid_arg "AXIOM_AVATAR_REFUTATION must be incremental or smaller")
  in
  let config =
    match getenv "AXIOM_LEAN_LOOP" with
    | None -> config
    | Some text -> (
        try { config with loop = Some (Heuristic.loop_of_string text) }
        with Invalid_argument e -> invalid_arg ("AXIOM_LEAN_LOOP: " ^ e))
  in
  let config =
    match getenv "AXIOM_LANE" with
    | None -> config
    | Some text -> (
        try { config with lane = Probe_lane.parse_overrides config.lane text }
        with Invalid_argument e -> invalid_arg ("AXIOM_LANE: " ^ e))
  in
  let config =
    match getenv "AXIOM_SLICES" with
    | None -> config
    | Some text -> (
        try { config with slices = Some (Slices.parse text) }
        with Invalid_argument e -> invalid_arg ("AXIOM_SLICES: " ^ e))
  in
  (* A measurement switch, applied here because it is a configuration field; empty means unset. *)
  match getenv "AXIOM_MEASURE_REFERENCE" with
  | None | Some "" | Some "on" -> config
  | Some "off" -> { config with reference = false }
  | Some other -> invalid_arg ("AXIOM_MEASURE_REFERENCE: unsupported value " ^ other)

(** The scheduling-cost clock that AXIOM_MEASURE_COST_CLOCK selects, if it replaces the wall clock.
    Shared with the schema benchmark, which reads only this switch. *)
let cost_clock getenv =
  match getenv "AXIOM_MEASURE_COST_CLOCK" with
  | None | Some "" | Some "wall" -> None
  | Some "stopped" -> Some (fun () -> 0.)
  | Some other -> invalid_arg ("AXIOM_MEASURE_COST_CLOCK: unsupported value " ^ other)

type t = {
  active : (string * string) list;
      (** The switches whose value changes something, with their values, in [switches] order. *)
  config : Scheduler.config -> Scheduler.config;  (** applies the search switches *)
  isolation : Portfolio.isolation;  (** AXIOM_MEASURE_PORTFOLIO *)
  install : unit -> unit;
      (** Sets the clock, trace and report hooks (process-global; before any worker starts). *)
}

let of_env getenv =
  (* The search switches are checked first, then the others, each in [switches] order. *)
  ignore (configure getenv Scheduler.default_config : Scheduler.config);
  let clock = cost_clock getenv in
  let isolation =
    match getenv "AXIOM_MEASURE_PORTFOLIO" with
    | None | Some "" | Some "processes" -> Portfolio.Processes
    | Some "domains" -> Portfolio.Domains
    | Some other -> invalid_arg ("AXIOM_MEASURE_PORTFOLIO: unsupported value " ^ other)
  in
  let on name = match getenv name with None | Some "" | Some "0" -> false | Some _ -> true in
  let prefix name = match getenv name with None | Some "" -> None | Some p -> Some p in
  let given_trace = Option.map Given_trace.writer (prefix "AXIOM_MEASURE_GIVEN_TRACE") in
  let eval_trace = Option.map Given_trace.writer (prefix "AXIOM_MEASURE_EVAL_TRACE") in
  let install () =
    Option.iter (fun c -> Engine.cost_clock := c) clock;
    if on "AXIOM_EQ_UNFOLD_REPORT" then Engine.unfold_report := prerr_endline;
    if on "AXIOM_LEAN_EQ_REPORT" then Engine.eq_report := prerr_endline;
    if on "AXIOM_EQUIVALENCE_REPORT" then Engine.equivalence_report := prerr_endline;
    if on "AXIOM_VAMPIRE_ORDERING" then Vampire.report := prerr_endline;
    Engine.given_trace := given_trace;
    Option.iter (fun w -> Engine.eval_trace := Some w) eval_trace;
    if on "AXIOM_MEASURE_NEW_TRACE" then Engine.new_trace := true
  in
  let active =
    List.filter_map
      (fun s ->
        match getenv s.name with
        | Some v when not (List.mem v s.unset) -> Some (s.name, v)
        | _ -> None)
      switches
  in
  { active; config = configure getenv; isolation; install }

(** The one line that says a run is not the default search, or [None]. [extra] adds evaluation
    settings that are not environment variables (the CLI's --eval-strategies). *)
let note ?(extra = []) t =
  match t.active @ extra with
  | [] -> None
  | active ->
      Some
        ("Note: evaluation overrides active: "
        ^ String.concat ", " (List.map (fun (k, v) -> k ^ "=" ^ v) active))

(** [switches] as a Markdown table (docs/evaluation-switches.md shows the same table). *)
let help () =
  let escape s = String.concat "\\|" (String.split_on_char '|' s) in
  let row s =
    Printf.sprintf "| `%s` | %s | %s | %s | %s |\n" s.name (kind_name s.kind) (escape s.values)
      (escape s.default) (escape s.doc)
  in
  "| Variable | Kind | Values | Unset | Effect |\n| --- | --- | --- | --- | --- |\n"
  ^ String.concat "" (List.map row switches)
