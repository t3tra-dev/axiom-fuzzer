open Axiom_fuzzer
open Test_support
open Wire

let settings =
  {
    Engine.default_config with
    avatar = false;
    subsumption = false;
    ordered = false;
    lookahead = 0;
    variants = false;
    demodulation = false;
    backward_demodulation = false;
    collect_every = 0;
    limits =
      { Engine.seconds = 10.; max_given = max_int; max_generated = max_int; max_retained = max_int };
  }

let prepare ?(config = settings) text =
  let theory = Tptp.parse text in
  let e = Engine.create config in
  List.iter (Engine.add_axiom e) (Theory.fixed theory);
  (theory, e)

let goal_slices n e =
  for _ = 1 to n do
    if e.Engine.root = None && e.stopped = None && Goal.has_work e.goals then
      Engine.protect (fun () -> Engine.goal_only_step e)
  done

let consumer_slices n e =
  for _ = 1 to n do
    if e.Engine.root = None && e.stopped = None && Engine.consumer_ready e then
      Engine.protect (fun () -> Engine.consumer_step e)
  done

let checked theory e =
  let cert = Option.get (Engine.certificate e ~theory:(Theory.name theory)) in
  (match Kernel.check theory cert with Ok _ -> () | Error error -> failwith error);
  cert

let promotion_text =
  "cnf(a,axiom,(p(a)|q(a))). cnf(b,axiom,~q(a)). cnf(link,axiom,(~p(a)|r)). cnf(close,axiom,~r)."

let promotion () =
  let theory = Tptp.parse promotion_text in
  let e = Engine.create settings in
  List.iteri (fun i a -> if i < 3 then Engine.add_axiom e a) (Theory.fixed theory);
  goal_slices 100 e;
  (theory, e)

let resolvent e left right =
  let result = ref None in
  Calculus.resolve_cursor e.Engine.calculus (Proof.get e.proof left) (Proof.get e.proof right)
  |> Seq.iter (fun f -> f (fun raw rule -> result := Some (raw, rule)));
  Option.get !result

let simple () = prepare "cnf(a,axiom,(p|q)). cnf(b,axiom,~p)."
let ticket e id = (id, Tbl.Int.find e.Engine.retained_index.live id)

let slow_work e id : Engine.pending_inference =
  let owner = ticket e id in
  {
    owner;
    current = None;
    groups =
      Seq.return
        {
          Directions.parents = [ owner ];
          start = (fun () -> List.to_seq (List.init 600 (fun _ _emit -> ())));
        };
  }

let sets e =
  let o = e.Engine.transfer_observations in
  [
    o.publication_ancestors;
    o.publication_results;
    o.publication_accepted;
    o.empty_ancestors;
    o.empty_results;
    o.empty_accepted;
  ]

let tests =
  [
    ( "Goal retains recipes and internal progress without publishing before a work request",
      fun () ->
        let _, e = promotion () in
        check (e.goals.metrics.expanded > 0) "Goal stopped";
        check
          (e.transfer.metrics.offered > 0 && Tbl.Int.length e.transfer.offers > 0)
          "eligible recipe never offered";
        equal e.transfer_observations.publication_commits 0 "private recipe was published";
        equal e.transfer.metrics.ancestor_recorded 0 "unrequested recipe was materialized";
        equal e.transfer.metrics.slices 0 "unrequested recipe was consumed";
        equal (Goal_transfer.consumer_count e.transfer) 0 "retention opened consumers";
        equal e.transfer_observations.use_applied 0 "old use escaped";
        equal e.transfer_observations.demand_applied 0 "old demand escaped";
        check
          (e.transfer_observations.use_calls > 0 && e.transfer_observations.demand_calls > 0)
          "suppression bypassed old observation boundaries" );
    ( "single-slice ordinary selection drains prior recipes after completion",
      fun () ->
        let theory, e = promotion () in
        equal (Goal_transfer.consumer_count e.transfer) 0 "retention opened consumers";
        equal e.transfer.request_metrics.opened 0 "retention opened a work request";
        consumer_slices 8 e;
        equal e.transfer.metrics.accepted 0 "unrequested clause consumed a recipe";
        (* Goal produced q(a) | r; the chosen ordinary ~q(a) consumes it. *)
        let q = P ("q", [ constant "a" ]) in
        equal (Proof.get e.proof 1).clause [ negative q ] "fixture owner changed";
        check
          (Tbl.Int.fold
             (fun _ (o : Goal_transfer.offer) found ->
               found || List.mem (positive q) o.proof.step.clause)
             e.transfer.offers false)
          "fixture has no complementary preexisting recipe";
        select_given e 1;
        equal e.transfer.request_metrics.opened 1 "chosen work did not open one request";
        equal e.transfer.request_metrics.sealed 1 "short ordinary work did not seal";
        equal (Engine.Work_table.length e.transfer_work) 0 "completed ordinary binding leaked";
        let opened, draining = Goal_transfer.request_counts e.transfer in
        equal opened 0 "completed work remained unsealed";
        equal draining 1 "completed work disappeared before consumer service";
        consumer_slices 100 e;
        check (e.transfer.metrics.accepted > 0) "selected work's recipe never reached admission";
        equal (Goal_transfer.request_counts e.transfer) (0, 0) "finite debt did not drain";
        equal e.transfer.request_metrics.drained 1 "drained request was not closed";
        equal e.transfer.metrics.feedback 0 "consumer acceptance fed back into priority";
        Engine.collect e;
        Engine.add_axiom e (List.nth (Theory.fixed theory) 3);
        let cert = checked theory e in
        check
          (List.exists (fun (s : step) -> Tbl.Int.mem e.transfer.direct_ids s.id) cert.steps)
          "requested consumer result absent from final proof" );
    ( "distinct continuations of one owner keep separate stable request identities",
      fun () ->
        let _, e = prepare "cnf(a,axiom,p(a))." in
        let a = slow_work e 0 and b = slow_work e 0 in
        Engine.process_inference e a;
        Engine.process_inference e b;
        equal (Engine.Work_table.length e.transfer_work) 2 "same owner collapsed distinct work";
        let qa = Engine.Work_table.find e.transfer_work a in
        let qb = Engine.Work_table.find e.transfer_work b in
        check (qa.serial <> qb.serial) "request token was an owner ID";
        equal e.transfer.request_metrics.opened 2 "wrong number of owner requests";
        let resumed = Engine.take_pending e in
        check (resumed == a) "unexpected pending order";
        Engine.process_inference e resumed;
        equal e.transfer.request_metrics.opened 2 "mutable cursor lost physical request identity";
        equal e.transfer.request_metrics.sealed 1 "resumed work did not finish";
        equal (Engine.Work_table.length e.transfer_work) 1 "completed binding survived";
        Engine.process_inference e (Engine.take_pending e);
        equal (Engine.Work_table.length e.transfer_work) 0 "second completed binding survived";
        consumer_slices 20 e;
        equal (Goal_transfer.request_counts e.transfer) (0, 0) "empty finite debts did not close" );
    ( "deactivation removes pending-work bindings and invalidates every owner request",
      fun () ->
        let _, e = prepare "cnf(a,axiom,p(a))." in
        Engine.process_inference e (slow_work e 0);
        Engine.process_inference e (slow_work e 0);
        equal (Engine.Work_table.length e.transfer_work) 2 "fixture lacked live work";
        Engine.retire e 0;
        equal (Engine.Work_table.length e.transfer_work) 0 "retired owner kept physical bindings";
        equal e.transfer.request_metrics.invalidated 2 "retired owner left a request alive";
        Engine.collect e;
        equal (Queue.length e.pending) 0 "collection retained stale ordinary jobs";
        equal (Goal_transfer.request_counts e.transfer) (0, 0) "retired request survived collection"
    );
    ( "ordinary selection refresh clears old request snapshots and work bindings",
      fun () ->
        let config = { settings with ordered = true; lookahead = 64 } in
        let _, e = prepare ~config "cnf(a,axiom,(~p(a)|q(a)))." in
        Tbl.Int.replace e.calculus.selected 0 (Some [ 1 ]);
        Engine.process_inference e (slow_work e 0);
        equal (Engine.Work_table.length e.transfer_work) 1 "fixture lacked selected work";
        Engine.select_literal e (Proof.get e.proof 0) (Engine.emit e);
        check
          (Calculus.selected e.calculus (Proof.get e.proof 0) <> Some [ 1 ])
          "fixture did not change ordinary selection";
        equal
          (Engine.Work_table.length e.transfer_work)
          0 "selection refresh kept stale work binding";
        equal e.transfer.request_metrics.invalidated 1
          "selection refresh did not invalidate request" );
    ( "filtered duplicate never reports a direct recording or acceptance",
      fun () ->
        let _, e = simple () in
        let raw, rule = resolvent e 0 1 in
        let recorded = ref [] and accepted = ref [] in
        let emit () =
          Engine.emit_consumed e
            ~recorded:(fun s -> recorded := s.id :: !recorded)
            ~accepted:(fun _ s -> accepted := s.id :: !accepted)
            raw rule
        in
        emit ();
        equal (List.length !recorded) 1 "first result was not recorded";
        equal (List.length !accepted) 1 "first result was not retained";
        recorded := [];
        accepted := [];
        emit ();
        equal !recorded [] "duplicate acquired an ID";
        equal !accepted [] "duplicate acquired acceptance" );
    ( "accepted observer follows a synchronous empty descendant",
      fun () ->
        let text = "cnf(a,axiom,(p|q)). cnf(b,axiom,~p). cnf(c,axiom,~q)." in
        let theory, e = prepare text in
        let raw, rule = resolvent e 0 1 in
        let recorded = ref [] and accepted = ref [] in
        Engine.protect (fun () ->
            Engine.emit_consumed e
              ~recorded:(fun s -> recorded := s.id :: !recorded)
              ~accepted:(fun kind s -> accepted := (kind, s.id) :: !accepted)
              raw rule);
        equal (List.length !recorded) 1 "nested emit counted as a second direct result";
        check
          (List.exists
             (fun (kind, id) -> kind = Goal_transfer.Unconditional_empty && Some id = e.root)
             !accepted)
          "empty descendant was not accepted";
        check
          (List.exists
             (fun (kind, id) -> kind = Goal_transfer.Retained && List.mem id !recorded)
             !accepted)
          "direct retained event absent";
        check (e.emission_observer = None) "Stop leaked observer scope";
        ignore (checked theory e) );
    ( "observer exceptions restore the dynamic emission scope",
      fun () ->
        let _, e = simple () in
        let raw, rule = resolvent e 0 1 in
        let calls = ref 0 in
        (try
           Engine.emit_consumed e
             ~recorded:(fun _ ->
               incr calls;
               raise Exit)
             ~accepted:(fun _ _ -> assert false)
             raw rule
         with Exit -> ());
        equal !calls 1 "recorded callback never ran";
        check (e.emission_observer = None) "exception leaked observer";
        let ids = List.map Tbl.Int.length (sets e) in
        Engine.emit e raw rule;
        equal ids
          (List.map Tbl.Int.length (sets e))
          "unrelated ordinary emit gained Goal provenance" );
    ( "isolated producer-only work leaves ordinary lane and Control clocks unchanged",
      fun () ->
        let _, e = prepare "cnf(a,axiom,p(a))." in
        Passive.invalidate e.passive 0;
        Focus.remove e.focus 0;
        e.ground_epoch <- e.knowledge_epoch;
        Ground_boolean.collect e.ground_boolean ~keep:(fun _ -> false) ~get:(Proof.get e.proof);
        e.avatar.dirty <- false;
        check (not (Engine.ordinary_has_work e)) "fixture left ordinary work ready";
        let work =
          Array.map
            (fun (l : Directions.Schedule.lane) -> (l.runs, l.work, l.last, l.service))
            e.work.lanes
        in
        let control =
          Array.map (fun (a : Control.arm) -> (a.runs, a.last, a.reward)) e.control.arms
        in
        let batches = e.metrics.inference_batches in
        check (Goal.has_work e.goals) "no producer work";
        Engine.step e;
        equal work
          (Array.map
             (fun (l : Directions.Schedule.lane) -> (l.runs, l.work, l.last, l.service))
             e.work.lanes)
          "producer perturbed ordinary lanes";
        equal control
          (Array.map (fun (a : Control.arm) -> (a.runs, a.last, a.reward)) e.control.arms)
          "producer perturbed Control";
        equal e.metrics.inference_batches batches "producer counted an ordinary inference batch";
        check
          ((Producer_schedule.snapshot e.producers Goal).runs > 0)
          "Goal service was not selected" );
    ( "isolated ordinary Demand cannot dispatch a ready consumer while Focus is waiting",
      fun () ->
        let _, e = promotion () in
        Engine.process_inference e (slow_work e 1);
        let ticket = (0, Tbl.Int.find e.retained_index.live 0) in
        Queue.clear e.focus.pending;
        Tbl.Pair.clear e.focus.queued;
        Focus.enqueue e.focus ticket;
        check (Focus.has_work e.focus && Engine.consumer_ready e) "boundary fixture is not ready";
        e.work.lanes.(1).runs <- 2;
        e.work.lanes.(1).service <- 0.;
        e.work.lanes.(2).service <- 1000000.;
        let slices = e.transfer.metrics.slices in
        Engine.infer_step e;
        equal e.work.lanes.(1).runs 3 "ordinary Demand was not selected";
        equal e.transfer.metrics.slices slices "ordinary Demand ran the isolated consumer" );
    ( "real engine events agree with ordinary counters under the production policy",
      fun () ->
        let config = { settings with collect_every = 1; collect_adaptive = false } in
        let _, e = prepare ~config "cnf(a,axiom,(p(a)|q(a))). cnf(b,axiom,~p(a))." in
        for _ = 1 to 32 do
          if e.root = None && e.stopped = None && Engine.has_work e then Engine.step e
        done;
        Engine.collect e;
        let trace = e.schedule_trace in
        check (trace.control.total > 0 && trace.lane.total > 0) "ordinary trace stayed empty";
        equal trace.lane.counts.(1)
          (Array.fold_left
             (fun n (lane : Directions.Schedule.lane) -> n + lane.runs)
             0 e.work.lanes)
          "lane charges disagree with actual accounting";
        equal trace.action.counts.(0) e.metrics.given "given action was lost";
        equal trace.action.counts.(5) e.metrics.inference_yields "yield action was lost";
        let gc = trace.gc.counts in
        equal
          (gc.(1) + gc.(3) + gc.(5))
          e.metrics.collections "returned collections lack end events";
        equal
          (gc.(0) + gc.(2) + gc.(4))
          e.metrics.collections "returned collections lack begin events";
        equal gc.(0) 1 "manual collection origin was lost" );
    ( "four-worker default rows preserve exact observation columns",
      fun () ->
        let theory = Tptp.parse "cnf(a,axiom,p)." in
        let config =
          {
            Scheduler.default_config with
            reference = false;
            guided = false;
            max_instances = 0;
            max_guided_instances = 0;
            engine = { settings with limits = { settings.limits with seconds = 0.02 } };
          }
        in
        let r = Scheduler.portfolio ~workers:4 config (fun () -> Theory.copy theory) in
        equal (List.length r.workers) 4 "portfolio dropped worker rows";
        equal (List.length Metrics_csv.r13_header) 56 "schema column count changed";
        equal (List.length Metrics_csv.r14_header) 13 "request schema column count changed";
        (* 309 observation columns, then the worker groups: the strategy group (the worker strategy
           and the E heuristic diagnostics), the slice group and the caps and memory-budget group. *)
        equal (List.length Metrics_csv.strategy_header) 3 "strategy column count changed";
        equal (List.length Metrics_csv.slice_header) 23 "slice column count changed";
        equal (List.length Metrics_csv.budget_header) 18 "budget column count changed";
        equal Metrics_csv.worker_group_header
          (Metrics_csv.strategy_header @ Metrics_csv.slice_header @ Metrics_csv.budget_header)
          "worker group order changed";
        equal Metrics_csv.header
          (Metrics_csv.base_header @ Metrics_csv.worker_group_header)
          "worker columns changed";
        equal (List.length Metrics_csv.header) (309 + 3 + 23 + 18) "base header prefix changed";
        equal (List.nth Metrics_csv.header 309) "strategy" "strategy column moved";
        equal
          [ List.nth Metrics_csv.header 310; List.nth Metrics_csv.header 311 ]
          [ "order_violations"; "mix_selections" ]
          "E heuristic diagnostics moved";
        (* metrics_version 6, one column order for both CSVs: the observation columns, the
           summary's portfolio and reference columns, the worker groups, and last the process
           supervisor's columns. *)
        equal Metrics_csv.version "6" "metrics_version not bumped";
        equal
          (List.length Metrics_csv.summary_header, List.length Metrics_csv.isolation_header)
          (19, 4) "summary-only column count changed";
        equal
          (List.rev Metrics_csv.summary_header |> List.hd)
          "reference_peak_domain_words" "reference heap column moved";
        equal Metrics_csv.worker_header
          (Metrics_csv.header @ Metrics_csv.process_header)
          "worker CSV column order changed";
        equal
          (List.length Metrics_csv.worker_header)
          (309 + 3 + 23 + 18 + 4)
          "worker CSV column count changed";
        let summary_header, summary_row =
          match String.split_on_char '\n' (Metrics_csv.summary ~output_seconds:0. r) with
          | [ header; row ] -> (String.split_on_char ',' header, row)
          | _ -> failwith "summary CSV is not one header and one row"
        in
        equal summary_header
          (Metrics_csv.base_header @ Metrics_csv.summary_header @ Metrics_csv.worker_group_header
         @ Metrics_csv.isolation_header)
          "summary column order changed";
        equal (List.length summary_header)
          (309 + 19 + 3 + 23 + 18 + 4)
          "summary column count changed";
        equal
          (List.filteri (fun i _ -> i < 309) summary_header)
          Metrics_csv.base_header "summary observation prefix changed";
        equal
          (List.hd (String.split_on_char ',' summary_row))
          "6" "summary metrics_version not bumped";
        List.iter
          (fun (w : Scheduler.worker_metrics) ->
            equal
              (List.length (Metrics_csv.values w))
              (List.length Metrics_csv.header) "CSV field count differs";
            equal
              (List.assoc "r13_consumers_live"
                 (List.combine Metrics_csv.r13_header (Metrics_csv.r13_values w)))
              "0" "legacy broad-consumer gauge changed";
            equal
              (List.hd (Metrics_csv.r13_values w))
              "isolated_requested" "policy observation changed";
            equal
              (List.filteri (fun i _ -> i < 2) (Metrics_csv.r14_values w))
              [ "true"; "false" ] "request/feedback observations changed";
            equal w.engine.transfer.metrics.feedback 0 "default policy enabled accepted feedback")
          r.workers );
  ]

let () = run tests
