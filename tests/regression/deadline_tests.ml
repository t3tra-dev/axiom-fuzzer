open Axiom_fuzzer
open Test_support

(* Deadline regressions for schema enumeration. One step of a registered schema's stream can scan
   very many raw conditions of Enumerate.exhaustive before it reaches the next admissible one. The
   heuristic scheduler and the script reference must abandon such a step at the time limit or on
   cancellation (Enumerate.with_guard) instead of finishing it first. Every search runs in its own
   Domain under a watchdog, so a regression fails within seconds instead of hanging the suite. *)

let within ~seconds name f =
  let finished = Atomic.make false in
  let worker =
    Domain.spawn (fun () -> Fun.protect ~finally:(fun () -> Atomic.set finished true) f)
  in
  let started = Telemetry.now () in
  while (not (Atomic.get finished)) && Telemetry.now () -. started < seconds do
    Unix.sleepf 0.005
  done;
  if not (Atomic.get finished) then (
    (* The stuck Domain cannot be joined; end the process with a failure. *)
    Printf.eprintf "FAIL %s: still running %.1f s after the start\n%!" name seconds;
    exit 1);
  Domain.join worker

let timed f =
  let started = Telemetry.now () in
  let r = f () in
  (r, Telemetry.now () -. started)

(* Slack over the budget for an interrupted step: polling happens on every 16th raw condition (a
   few tens of microseconds); the rest is scheduling noise on a loaded machine. *)
let slack = 1.0
let lambda_signature = Signature.make ~functions:[ ("ap", 2); ("n", 1) ] ~predicates:[]

let rec occurs_term i = function
  | Wire.F j -> i = j
  | Wire.B _ -> false
  | Wire.App (_, ts) -> List.exists (occurs_term i) ts

(* Term comprehension (the independent schema benchmark's i-ctl-lambda-moving control): the
   condition must be y = t with y not in t; the instance is ?f. !x. ap(f, x) = t. Few raw
   conditions are admissible, so the gaps between admissible ones grow quickly. *)
let admissible p =
  Wire.source_scoped p
  &&
  match p with
  | Wire.Eq (Wire.F 1, t) | Wire.Eq (t, Wire.F 1) -> not (occurs_term 1 t)
  | _ -> false

let lambda_instance a phi =
  let params = List.filter (fun i -> i >= 2) (Source.free_vars a phi) in
  let f = List.fold_left max 1 params + 1 in
  Source.all a params
    (Source.ex a [ f ]
       (Source.all a [ 0 ]
          (Source.subst_free a 1 (Source.apply a "ap" [ Source.free a f; Source.free a 0 ]) phi)))

let schema ~name ~keep =
  Theory.Schema.create ~name ~revision:"1"
    ~encode:(fun p -> Sexp.to_string (Certificate_io.source p))
    ~decode:(fun s -> try Some (Certificate_io.decode_source (Sexp.parse s)) with _ -> None)
    ~enumerate:(fun signature _ ->
      let a = Source.create signature in
      Enumerate.exhaustive a ~arity:2
      |> Seq.filter_map (fun phi ->
          let p = Wire.export a phi in
          if keep p then Some p else None))
    ~expand:(fun a p -> lambda_instance a (Wire.import a p))
    ~check:(fun signature p f ->
      keep p
      &&
        try
          let a = Source.create signature in
          Wire.import a f = lambda_instance a (Wire.import a p)
        with _ -> false)
    ()

(* ?p. n(p) != p: satisfiable together with every lambda instance (closed lambda terms modulo beta,
   n(p) = K p), so the search can only end by the budget. *)
let moving keep =
  let moves = Wire.Ex (Wire.Neg (Wire.Eq (Wire.App ("n", [ Wire.B 0 ]), Wire.B 0))) in
  Theory.register_schema
    (Theory.custom ~name:"lambda-moving" lambda_signature [ ("moves", moves) ])
    (schema ~name:"lambda" ~keep)

let budget ?(reference = false) seconds =
  {
    Scheduler.default_config with
    reference;
    reference_config = { Reference.default_config with seconds; max_trials = max_int };
    engine =
      {
        Engine.default_config with
        limits = { max_given = max_int; max_generated = max_int; max_retained = max_int; seconds };
      };
  }

let unknown_within name seconds (r : Scheduler.result) elapsed =
  check (r.certificate = None) (name ^ ": consistent theory refuted");
  if elapsed > seconds +. slack then
    failwith (Printf.sprintf "%s: %.2f s for a %.2f s budget (%s)" name elapsed seconds r.reason)

let tests =
  [
    ( "a guard abandons an enumeration step; forcing the node again yields the same element",
      fun () ->
        let keep a phi = admissible (Wire.export a phi) in
        let stream a = Enumerate.exhaustive a ~arity:2 |> Seq.filter (keep a) in
        let expected =
          let a = Source.create lambda_signature in
          stream a |> Seq.take 60 |> Seq.map (Wire.export a) |> List.of_seq
        in
        let a = Source.create lambda_signature in
        let polls = ref 0 and armed = ref true and interrupts = ref 0 in
        let guard () =
          incr polls;
          if !armed && !polls = 1 then (
            armed := false;
            incr interrupts;
            raise Exit)
        in
        let rec force n s acc =
          if n = 0 then List.rev acc
          else
            match Enumerate.with_guard guard s with
            | exception Exit ->
                polls := 0;
                force n s acc
            | Seq.Nil -> List.rev acc
            | Seq.Cons (x, rest) ->
                polls := 0;
                armed := true;
                force (n - 1) rest (Wire.export a x :: acc)
        in
        let got = force 60 (stream a) [] in
        check (!interrupts > 10) "the guard was not polled inside long steps";
        check (got = expected) "an interrupted step changed the enumeration";
        polls := 0;
        Enumerate.exhaustive a ~arity:2 |> Seq.take 200 |> Seq.iter ignore;
        check (!polls = 0) "the guard stayed installed after with_guard" );
    ( "the scheduler stops a schema step that never reaches an admissible condition",
      fun () ->
        let theory = moving (fun _ -> false) in
        let r, elapsed =
          within ~seconds:(0.3 +. 3.) "silent schema, deadline" (fun () ->
              timed (fun () -> Scheduler.run (budget 0.3) theory))
        in
        unknown_within "silent schema" 0.3 r elapsed;
        (* With the default schema probe lane the reason ends with its statistics. *)
        check
          (String.starts_with ~prefix:"time limit" r.reason)
          ("silent schema: unexpected reason " ^ r.reason);
        let cancel_at = 0.3 in
        let r, elapsed =
          within ~seconds:(cancel_at +. 3.) "silent schema, cancellation" (fun () ->
              timed (fun () ->
                  let started = Telemetry.now () in
                  Scheduler.run
                    ~cancelled:(fun () -> Telemetry.now () -. started >= cancel_at)
                    (budget 60.) theory))
        in
        unknown_within "silent schema, cancellation" cancel_at r elapsed;
        check
          (String.starts_with ~prefix:"cancelled" r.reason)
          ("cancellation: unexpected reason " ^ r.reason) );
    ( "the probe lane's look-ahead abandons a schema step at the deadline",
      fun () ->
        (* The lane forces its own cursor of the schema streams, outside the main
           engine's guard; a step of the silent schema never returns, so only the
           lane's own guard can end it. 0.2 s are left before the deadline. *)
        let theory = moving (fun _ -> false) in
        let seconds = 0.2 in
        let config = budget 60. in
        let started = Telemetry.now () -. (config.engine.limits.seconds -. seconds) in
        let lane =
          Probe_lane.create ~started ~inject:(fun _ _ _ -> ()) Probe_lane.fifo config.engine theory
        in
        let (), elapsed =
          within ~seconds:(seconds +. 3.) "lane look-ahead" (fun () ->
              timed (fun () ->
                  while Probe_lane.has_work lane && not (Probe_lane.past_deadline lane) do
                    Probe_lane.turn lane
                  done))
        in
        check (not (Probe_lane.scan_ready lane)) "the interrupted look-ahead kept its stream";
        check (lane.stats.scanned = 0) "the silent schema produced a candidate";
        if elapsed > seconds +. slack then
          failwith (Printf.sprintf "lane look-ahead: %.2f s for a %.2f s budget" elapsed seconds) );
    ( "the portfolio keeps its budget on the lambda-moving control (heuristic and reference)",
      fun () ->
        (* A regression test: an earlier build took 4.9 s for a 1 s budget on this control, and
           64-72 s and 3 GB for a 10 s budget in the benchmark. *)
        let seconds = 1.5 in
        let theory = moving admissible in
        let r, elapsed =
          within ~seconds:(seconds +. 2.) "lambda-moving" (fun () ->
              timed (fun () ->
                  Scheduler.portfolio ~workers:1 (budget ~reference:true seconds) (fun () ->
                      Theory.copy theory)))
        in
        unknown_within "lambda-moving" seconds r elapsed );
    ( "the script reference stops a schema step that never reaches an admissible condition",
      fun () ->
        let theory = moving (fun _ -> false) in
        let r, elapsed =
          within ~seconds:(0.3 +. 3.) "script reference" (fun () ->
              timed (fun () ->
                  Reference.run
                    { Reference.default_config with seconds = 0.3; max_trials = max_int }
                    theory))
        in
        check (r.certificate = None) "script reference refuted a consistent theory";
        check (r.reason = "reference time limit") ("script reference: unexpected reason " ^ r.reason);
        if elapsed > 0.3 +. slack then
          failwith (Printf.sprintf "script reference: %.2f s for a 0.30 s budget" elapsed) );
  ]

(* An optional argument selects the tests whose name contains it (a stuck test ends the process). *)
let () =
  match Array.to_list Sys.argv with
  | [ _ ] -> run tests
  | [ _; part ] ->
      let contains name =
        let n = String.length part in
        let rec at i = i + n <= String.length name && (String.sub name i n = part || at (i + 1)) in
        at 0
      in
      run (List.filter (fun (name, _) -> contains name) tests)
  | _ -> invalid_arg "deadline_tests [NAME-PART]"
