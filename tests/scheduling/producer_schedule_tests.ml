open Axiom_fuzzer
open Test_support
open Producer_schedule

let kinds = [ Ordinary; Goal; Consumer ]
let snapshots t = List.map (snapshot t) kinds
let zero _ = 0
let clock () = 0.

let run_one t ready costs =
  let effort = Array.make 3 0 in
  dispatch t ready
    ~effort:(fun kind -> effort.(index kind))
    ~now:clock
    (fun kind ->
      effort.(index kind) <- costs kind;
      kind)

let lane_snapshot (t : Directions.Schedule.t) =
  ( t.turns,
    Array.to_list
      (Array.map
         (fun (lane : Directions.Schedule.lane) -> (lane.service, lane.work, lane.runs, lane.last))
         t.lanes) )

let control_snapshot (t : Control.t) =
  ( t.turns,
    Array.to_list (Array.map (fun (arm : Control.arm) -> (arm.runs, arm.reward, arm.last)) t.arms)
  )

(* This models only the accounting boundary, not proof search or admission.
   Ordinary inputs and costs depend on its own count; internal readiness and
   costs vary independently. Real Engine boundaries have separate fixtures. *)
let ordinary_projection ?trace ~internal () =
  let services = create () in
  let work = Directions.Schedule.create () and control = Control.create () in
  let effort = Array.make 3 0 and steps = ref 0 and batches = ref 0 and continues = ref 0 in
  let choices = ref [] and polls = ref 0 in
  let ordinary () =
    let open Directions.Schedule in
    let ready = if !steps mod 5 = 2 then [ Control.Ground; Infer ] else [ Control.Infer; Ground ] in
    let operation = Option.get (Control.choose control ready) in
    Option.iter
      (fun trace ->
        Trace.control_select trace ~turn:control.turns ~ready ~selected:operation ~given:!steps
          ~pending:0
          ~generated:effort.(Producer_schedule.index Ordinary))
      trace;
    (match operation with
    | Infer ->
        incr batches;
        let ready = if !batches mod 7 = 0 then [ Continue ] else [ Demand; Continue ] in
        let selected = Option.get (choose work ready) in
        Option.iter
          (fun trace ->
            Trace.lane_select trace ~turn:work.turns ~ready ~selected ~batch:!batches
              ~demand_runs:work.lanes.(1).runs ~continue_runs:work.lanes.(2).runs)
          trace;
        let action =
          match selected with
          | First -> failwith "isolated ordinary service dispatched a Goal first trial"
          | Demand -> if work.lanes.(1).runs mod 4 = 0 then "request" else "focus"
          | Continue ->
              incr continues;
              if !continues mod 16 = 15 then "revisit"
              else if work.lanes.(2).runs mod 2 = 0 then "pending"
              else "given"
        in
        let cost = 1 + (!batches * 17 mod 23) in
        charge work selected cost;
        Option.iter
          (fun trace ->
            Trace.lane_charge trace ~turn:(work.turns - 1) ~selected ~work:cost ~batch:!batches
              ~generated:effort.(Producer_schedule.index Ordinary)
              ~attempts:0)
          trace;
        choices := (operation, Some (selected, action)) :: !choices
    | _ -> choices := (operation, None) :: !choices);
    Control.observe control operation ~gain:(!steps mod 3) ~cost:(1 + (!steps mod 19));
    Option.iter
      (fun trace ->
        Trace.control_observe trace ~turn:(control.turns - 1) ~selected:operation
          ~gain:(!steps mod 3)
          ~cost:(1 + (!steps mod 19))
          ~generated:effort.(Producer_schedule.index Ordinary)
          ~stored:!steps)
      trace;
    incr steps;
    effort.(Producer_schedule.index Ordinary) <-
      effort.(Producer_schedule.index Ordinary) + 1 + (!steps mod 11)
  in
  let states = ref [] in
  while !steps < 160 do
    incr polls;
    check (!polls < 10000) "an always-ready ordinary service stopped making progress";
    let ready =
      [ Ordinary ]
      @ (if internal && !polls mod 9 <> 0 then [ Goal ] else [])
      @ if internal && !polls mod 13 > 2 then [ Consumer ] else []
    in
    ignore
      (dispatch services ready
         ~effort:(fun kind -> effort.(index kind))
         ~now:clock
         (fun kind ->
           match kind with
           | Ordinary ->
               ordinary ();
               states :=
                 (lane_snapshot work, control_snapshot control, !batches, !continues) :: !states
           | Goal | Consumer ->
               let before = (lane_snapshot work, control_snapshot control, !batches, !continues) in
               effort.(index kind) <- effort.(index kind) + 1 + (!polls * 29 mod 37);
               equal before
                 (lane_snapshot work, control_snapshot control, !batches, !continues)
                 "internal work changed ordinary clocks"))
  done;
  (List.rev !choices, List.rev !states, services)

exception Cancelled

let tests =
  [
    ( "empty readiness performs no selection, measurement, credit, or charge",
      fun () ->
        let t = create () in
        ignore (run_one t [ Ordinary ] (fun _ -> 9));
        let before = (snapshots t, turns t) in
        let forbidden _ = failwith "empty scheduler evaluated a callback" in
        equal
          (dispatch t [] ~effort:forbidden ~now:forbidden forbidden)
          None "empty readiness returned work";
        equal before (snapshots t, turns t) "empty readiness changed the scheduler" );
    ( "readiness, selection, effort, and elapsed charge have distinct boundaries",
      fun () ->
        let t = create () and effort = Array.make 3 0 and now = ref 10. in
        equal
          (dispatch t [ Goal; Consumer; Goal ]
             ~effort:(fun kind -> effort.(index kind))
             ~now:(fun () -> !now)
             (fun kind ->
               equal kind Goal "caller tie order changed";
               effort.(index Goal) <- 7;
               effort.(index Consumer) <- 900;
               now := 10.125;
               42))
          (Some 42) "dispatch lost its result";
        let goal = snapshot t Goal and consumer = snapshot t Consumer in
        equal
          (goal.ready, goal.selected, goal.runs, goal.effort, goal.milliseconds, goal.work)
          (1, 1, 1, 7, 125, 133) "selected service charge is not local";
        equal
          (consumer.ready, consumer.selected, consumer.runs, consumer.effort, consumer.work)
          (1, 0, 0, 0, 0) "ready but unselected service was charged";
        equal (snapshot t Ordinary).ready 0 "inactive service was marked ready";
        equal (turns t) 1 "one dispatch advanced multiple turns" );
    ( "a cancelled slice is charged exactly once and the next service can resume",
      fun () ->
        let t = create () and effort = Array.make 3 0 and now = ref 0. in
        let cancelled =
          try
            ignore
              (dispatch t [ Goal; Consumer ]
                 ~effort:(fun kind -> effort.(index kind))
                 ~now:(fun () -> !now)
                 (fun _ ->
                   effort.(index Goal) <- 11;
                   now := 0.25;
                   raise Cancelled));
            false
          with Cancelled -> true
        in
        check cancelled "dispatch swallowed cancellation";
        let goal = snapshot t Goal in
        equal
          (goal.selected, goal.runs, goal.effort, goal.milliseconds, goal.work)
          (1, 1, 11, 250, 262) "cancelled work was lost or charged twice";
        equal (snapshot t Ordinary).runs 0 "cancellation leaked into ordinary accounting";
        equal
          (run_one t [ Goal; Consumer ] zero)
          (Some Consumer) "cancellation prevented another ready service from running";
        equal (turns t) 2 "resumed scheduling lost its charged clock" );
    ( "an inactive service cannot bank credit across empty queues and revival",
      fun () ->
        let t = create () in
        for _ = 1 to 99 do
          ignore (run_one t [ Ordinary ] zero)
        done;
        equal (snapshot t Goal).ready 0 "inactive queue acquired readiness observations";
        equal (snapshot t Goal).work 0 "inactive queue acquired charged work";
        equal (snapshot t Goal).service 98. "inactive queue banked service credit";
        for _ = 1 to 20 do
          ignore (dispatch t [] ~effort:zero ~now:clock (fun _ -> ()))
        done;
        equal
          (run_one t [ Ordinary; Goal ] zero)
          (Some Goal) "revived queue did not receive its current opportunity";
        equal
          (run_one t [ Ordinary; Goal ] zero)
          (Some Ordinary) "revived queue spent accumulated inactive credit";
        equal (snapshot t Consumer).runs 0 "an absent service was dispatched" );
    ( "all continuously ready services receive turns despite one very costly slice",
      fun () ->
        let t = create () and last = Array.make 3 0 in
        for turn = 1 to 240 do
          let selected =
            Option.get
              (run_one t kinds (function Ordinary -> 0 | Goal -> 1000000 | Consumer -> 6))
          in
          last.(index selected) <- turn;
          Array.iter
            (fun previous -> check (turn - previous < 24) "a ready service lost its age turn")
            last
        done;
        List.iter
          (fun kind ->
            let s = snapshot t kind in
            equal s.ready 240 "continuous readiness was undercounted";
            equal s.selected s.runs "a selected slice was not charged")
          kinds;
        check
          ((snapshot t Ordinary).runs > (snapshot t Goal).runs)
          "costly work was scheduled as though every call cost the same";
        equal (turns t)
          (List.fold_left (fun n kind -> n + (snapshot t kind).runs) 0 kinds)
          "charged turns do not partition into services" );
    ( "a dormant costly service revives through age without resetting spent work",
      fun () ->
        let t = create () in
        ignore (run_one t [ Consumer ] (fun _ -> 1000000));
        for _ = 1 to 40 do
          ignore (run_one t [ Ordinary; Goal ] zero)
        done;
        let before = snapshot t Consumer and received = ref false in
        for _ = 1 to 24 do
          if run_one t kinds zero = Some Consumer then received := true
        done;
        check !received "a revived expensive service had no reserved turn";
        check
          ((snapshot t Consumer).work >= before.work)
          "revival discarded previously charged work" );
    ( "internal producers preserve the complete ordinary selection and accounting projection",
      fun () ->
        let plain_trace, plain_states, plain = ordinary_projection ~internal:false () in
        let busy_trace, busy_states, busy = ordinary_projection ~internal:true () in
        equal plain_trace busy_trace "producer work changed ordinary operation/lane/modulo choices";
        equal plain_states busy_states "producer work changed ordinary work or Control clocks";
        check
          ((snapshot busy Goal).runs > 0 && (snapshot busy Consumer).runs > 0)
          "invariance fixture did not dispatch both internal producers";
        equal (snapshot plain Ordinary).work (snapshot busy Ordinary).work
          "unrelated producer effort was charged to ordinary work";
        check (turns busy > turns plain) "invariance fixture had no interposed work" );
    ( "trace joins selection, charge, owner zero and GC without rewriting raw cost",
      fun () ->
        let t = Trace.create () in
        Trace.control_select t ~turn:0 ~ready:[ Control.Infer; Ground; Infer ] ~selected:Infer
          ~given:2 ~pending:1 ~generated:3;
        Trace.lane_select t ~turn:0
          ~ready:[ Directions.Schedule.Demand; Continue ]
          ~selected:Continue ~batch:1 ~demand_runs:7 ~continue_runs:2;
        Trace.action t Trace.Process ~id:0 ~generation:4 ~control_turn:0 ~lane_turn:0
          ~producer_turn:3 ~pending:1;
        Trace.gc t Trace.Begin ~origin:Trace.Ordinary ~control_turn:0 ~producer_turn:3 ~stored:7
          ~retained:5 ~pending:1;
        Trace.gc t Trace.End ~origin:Trace.Ordinary ~control_turn:0 ~producer_turn:3 ~stored:4
          ~retained:3 ~pending:1;
        Trace.lane_charge t ~turn:0 ~selected:Directions.Schedule.Continue ~work:11 ~batch:1
          ~generated:4 ~attempts:8;
        Trace.control_observe t ~turn:0 ~selected:Control.Infer ~gain:(-3) ~cost:(-4) ~generated:4
          ~stored:4;
        equal t.total 7 "global event clock omitted a stream";
        let control = Trace.snapshot t.control and lane = Trace.snapshot t.lane in
        let action = Trace.snapshot t.action and gc = Trace.snapshot t.gc in
        equal control.events
          [| [| 0; 0; 0; 5; 0; 2; 1; 3 |]; [| 6; 1; 0; 0; -3; -4; 4; 4 |] |]
          "Control readiness or unclamped observation was changed";
        equal lane.events
          [| [| 1; 0; 0; 6; 2; 1; 7; 2 |]; [| 5; 1; 0; 2; 11; 1; 4; 8 |] |]
          "lane observations lost their time or payload";
        equal action.events
          [| [| 2; 1; 0; 4; 0; 0; 3; 1 |] |]
          "ordinary ID zero or its retained generation was lost";
        equal gc.events
          [| [| 3; 2; 1; 0; 3; 7; 5; 1 |]; [| 4; 3; 1; 0; 3; 4; 3; 1 |] |]
          "GC origin/boundary was conflated with a producer charge";
        equal control.counts [| 1; 1 |] "Control tag count changed";
        equal gc.counts [| 0; 0; 1; 1; 0; 0 |] "GC origin count changed" );
    ( "trace keeps first bounded prefixes and counts unretained events independently",
      fun () ->
        let t = Trace.create () in
        let iterations = (2 * Trace.capacity) + 4 in
        for n = 0 to iterations - 1 do
          Trace.control_select t ~turn:n ~ready:[ Control.Infer ] ~selected:Infer ~given:n
            ~pending:0 ~generated:n;
          if n mod 2 = 0 then
            Trace.control_observe t ~turn:n ~selected:Control.Infer ~gain:0 ~cost:1 ~generated:n
              ~stored:n;
          Trace.action t Trace.Given ~id:n ~generation:0 ~control_turn:n ~lane_turn:0
            ~producer_turn:0 ~pending:0
        done;
        Trace.gc t Trace.Begin ~origin:Trace.Producer ~control_turn:iterations ~producer_turn:9
          ~stored:1 ~retained:1 ~pending:0;
        Trace.gc t Trace.End ~origin:Trace.Producer ~control_turn:iterations ~producer_turn:9
          ~stored:0 ~retained:0 ~pending:0;
        let control = Trace.snapshot t.control and action = Trace.snapshot t.action in
        let gc = Trace.snapshot t.gc and lane = Trace.snapshot t.lane in
        equal control.total (iterations + (iterations / 2)) "Control total stopped at capacity";
        equal control.counts [| iterations; iterations / 2 |] "dropped event tags were lost";
        equal (Array.length control.events) Trace.capacity "Control history grew without bound";
        equal control.dropped (control.total - Trace.capacity) "Control dropped count is wrong";
        equal control.events.(0) [| 0; 0; 0; 1; 0; 0; 0; 0 |]
          "the retained prefix was silently replaced with a recent ring";
        equal action.total iterations "one stream changed another stream's capacity";
        equal (Array.length action.events) Trace.capacity "action history grew without bound";
        equal action.dropped (iterations - Trace.capacity) "action dropped count is wrong";
        equal lane.total 0 "absent lane events were synthesized";
        equal (Array.length lane.events) 0 "an empty stream has a fabricated prefix";
        equal gc.dropped 0 "late GC events inherited another stream's truncation";
        equal
          gc.events.(0).(0)
          (control.total + action.total) "late stream sequence discarded unretained earlier events";
        equal t.total (control.total + action.total + gc.total) "global count lost truncated data";
        control.events.(0).(0) <- -1;
        control.counts.(0) <- -1;
        equal (Trace.snapshot t.control).events.(0).(0) 0 "snapshot mutated the stored prefix";
        equal (Trace.snapshot t.control).counts.(0) iterations "snapshot mutated event totals" );
    ( "trace leaves cancelled Control and GC unfinished while lane finally is charged",
      fun () ->
        let t = Trace.create () in
        Trace.control_select t ~turn:0 ~ready:[ Control.Infer ] ~selected:Infer ~given:0 ~pending:1
          ~generated:0;
        Trace.lane_select t ~turn:0 ~ready:[ Directions.Schedule.Continue ] ~selected:Continue
          ~batch:1 ~demand_runs:0 ~continue_runs:0;
        let cancelled =
          try
            Fun.protect
              ~finally:(fun () ->
                Trace.lane_charge t ~turn:0 ~selected:Directions.Schedule.Continue ~work:7 ~batch:1
                  ~generated:1 ~attempts:5)
              (fun () ->
                Trace.gc t Trace.Begin ~origin:Trace.Manual ~control_turn:0 ~producer_turn:0
                  ~stored:4 ~retained:3 ~pending:1;
                if t.total > 0 then raise Cancelled;
                false)
          with Cancelled -> true
        in
        check cancelled "fixture swallowed cancellation";
        equal (Trace.snapshot t.control).counts [| 1; 0 |] "cancelled Control observe invented";
        equal (Trace.snapshot t.lane).counts [| 1; 1 |] "finally charge disappeared";
        equal (Trace.snapshot t.gc).counts [| 1; 0; 0; 0; 0; 0 |] "interrupted GC end invented" );
    ( "trace observation preserves the ordinary projection for fixed cost inputs",
      fun () ->
        let trace = Trace.create () in
        let plain_choices, plain_states, plain = ordinary_projection ~internal:true () in
        let traced_choices, traced_states, traced = ordinary_projection ~trace ~internal:true () in
        equal plain_choices traced_choices "observation changed the selected operations or lanes";
        equal plain_states traced_states "observation changed ordinary accounting";
        equal (snapshots plain) (snapshots traced) "observation changed producer charges";
        let control = Trace.snapshot trace.control in
        equal control.total 320 "projection did not record selection and observation";
        equal control.counts [| 160; 160 |] "Control turns did not produce paired observations";
        equal control.dropped 64 "projection did not exercise bounded observation";
        check ((Trace.snapshot trace.lane).total > 0) "projection had no inference lane activity" );
  ]

let () = run tests
