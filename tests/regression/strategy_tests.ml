open Axiom_fuzzer
open Test_support
open Wire

let proto_e = Strategy.of_name "proto:e"
let plain = { Strategy.production with name = "test:plain"; queues = Strategy.Plain_queues }
let combo = { (Strategy.of_name "proto:combo") with name = "test:combo"; queues = Plain_queues }

(* Every component of one engine follows that engine's strategy and order. *)
let check_engine (e : Engine.t) (s : Strategy.t) =
  check (e.config.strategy == s) "engine runs another strategy";
  check (e.calculus.strategy == s) "calculus runs another strategy";
  check (e.directions.probe.strategy == s) "direction probe runs another strategy";
  check (e.transfer.calculus.strategy == s) "transfer consumer runs another strategy";
  check (e.calculus.order == e.order) "calculus uses another order";
  check (e.directions.probe.order == e.order) "direction probe uses another order";
  check (e.transfer.calculus.order == e.order) "transfer consumer uses another order";
  check (e.demodulator.order == e.order) "demodulator uses another order";
  check (e.contraction.order == e.order) "contraction uses another order";
  check (e.calculus.memo == e.directions.probe.memo) "probe does not share the selection memo";
  check (e.calculus.memo == e.transfer.calculus.memo) "consumer does not share the selection memo";
  equal e.passive.plain (s.queues = Strategy.Plain_queues) "passive queue setup ignored";
  (* E's FullRewrite level ([Heuristic.loop.full_rewrite]) also needs the unorientable rules. *)
  equal e.demodulator.ordered_rewriting
    (s.ordered_rewriting || Engine.full_rewrite_strategy s)
    "ordered rewriting ignored"

let names (r : Scheduler.result) =
  List.map (fun (w : Scheduler.worker_metrics) -> (w.worker_id, w.strategy.name)) r.workers

let names_of = names

let tests =
  [
    ( "strategy names round-trip and unknown names are rejected",
      fun () ->
        List.iter
          (fun (s : Strategy.t) -> check (Strategy.of_name s.name == s) ("name lost: " ^ s.name))
          Strategy.named;
        equal
          (List.length (List.sort_uniq compare Strategy.names))
          (List.length Strategy.names) "duplicate strategy name";
        check (Strategy.of_name "production" == Strategy.production) "production is not standard";
        check (rejects (fun () -> ignore (Strategy.of_name "calc:none"))) "unknown name accepted" );
    ( "portfolio assignment gives each worker its configured strategy",
      fun () ->
        let assign p workers = List.init workers (Strategy.assign p ~base:plain ~workers) in
        check (List.for_all (( == ) plain) (assign Strategy.Uniform 4)) "uniform changed a worker";
        let explicit = [ Strategy.production; proto_e; plain ] in
        check
          (List.for_all2 ( == ) (assign (Strategy.Workers explicit) 3) explicit)
          "explicit strategies reordered";
        check
          (rejects (fun () -> ignore (assign (Strategy.Workers explicit) 4)))
          "too few worker strategies accepted";
        check
          (rejects (fun () -> ignore (Strategy.assign Strategy.Uniform ~base:plain ~workers:2 2)))
          "worker index outside the portfolio accepted" );
    ( "the default engine is production and the default portfolio is the balanced rule",
      fun () ->
        check (Engine.default_config.strategy == Strategy.production) "default engine strategy";
        check (Scheduler.default_config.portfolio = Strategy.Balanced) "default portfolio changed";
        let default workers =
          List.map
            (fun (c : Scheduler.config) -> c.engine.strategy.name)
            (Scheduler.worker_configs ~workers Scheduler.default_config)
        in
        equal (default 1) [ "production" ] "one default worker left production";
        equal (default 2) [ "production"; "e208" ] "two default workers";
        equal (default 4) [ "production"; "production"; "e208"; "y1346" ] "four default workers";
        let e = Engine.create Engine.default_config in
        check_engine e Strategy.production;
        check (e.order.table = None) "production installed a precedence table" );
    ( "the balanced rule keeps both halves and spreads the diversified half for every worker count",
      fun () ->
        let resolve workers =
          Strategy.resolve Strategy.Balanced ~base:Strategy.production ~workers
        in
        let names workers =
          List.map (fun (w : Strategy.worker) -> w.strategy.name) (resolve workers)
        in
        let phases workers = List.map (fun (w : Strategy.worker) -> w.phase) (resolve workers) in
        let table =
          [
            (1, [ "production" ]);
            (2, [ "production"; "e208" ]);
            (3, [ "production"; "production"; "e208" ]);
            (4, [ "production"; "production"; "e208"; "y1346" ]);
            (5, [ "production"; "production"; "production"; "e208"; "y1346" ]);
            (6, [ "production"; "production"; "production"; "e208"; "y1346"; "sat001" ]);
            ( 8,
              [
                "production";
                "production";
                "production";
                "production";
                "e208";
                "y1346";
                "sat001";
                "calc:e";
              ] );
            ( 10,
              [
                "production";
                "production";
                "production";
                "production";
                "production";
                "e208";
                "y1346";
                "sat001";
                "calc:e";
                "e208";
              ] );
          ]
        in
        List.iter
          (fun (w, expected) -> equal (names w) expected (Printf.sprintf "%d workers" w))
          table;
        (* Up to 8 workers the rule is the earlier one, search for search: production at its
           worker index, each E heuristic once at phase 0 (the search it ran when it ignored the
           phase), calc:e at its worker index. *)
        let earlier workers =
          let p = (workers + 1) / 2 in
          List.init workers (fun i ->
              if i < p then ("production", i)
              else
                match List.nth Strategy.diversified (i - p) with
                | s when s == Strategy.calc_e -> (s.name, i)
                | s -> (s.name, 0))
        in
        for workers = 1 to 8 do
          equal
            (List.combine (names workers) (phases workers))
            (earlier workers)
            (Printf.sprintf "%d workers changed from the earlier rule" workers)
        done;
        equal (phases 10) [ 0; 1; 2; 3; 4; 0; 0; 0; 8; 1 ] "10 workers: phases";
        let members = Array.of_list Strategy.diversified in
        for workers = 1 to 64 do
          let resolved = resolve workers in
          let p = (workers + 1) / 2 and d = workers / 2 in
          (* Half and half: production runs on workers 0 .. p-1, so on queue phases 0 .. p-1: the
             all-production portfolio of p workers. *)
          List.iteri
            (fun i (w : Strategy.worker) ->
              check
                (i < p = (w.strategy == Strategy.production))
                (Printf.sprintf "%d workers: worker %d breaks the halves" workers i);
              if i < p then equal w.phase i (Printf.sprintf "%d workers: production phase" workers)
              else
                (* Round-robin over the diversified members, copy k of an E heuristic at phase
                   k, calc:e at its worker index. *)
                let j = i - p in
                check
                  (w.strategy == members.(j mod Array.length members))
                  (Printf.sprintf "%d workers: worker %d out of turn" workers i);
                equal w.phase
                  (if w.strategy == Strategy.calc_e then i else j / Array.length members)
                  (Printf.sprintf "%d workers: worker %d phase" workers i))
            resolved;
          (* The share bound: no diversified member runs on more than ceil((W/2)/4) workers,
             and the members differ by at most one worker. *)
          let counts =
            Array.map
              (fun m ->
                List.length (List.filter (fun (w : Strategy.worker) -> w.strategy == m) resolved))
              members
          in
          let largest = Array.fold_left max 0 counts
          and smallest = Array.fold_left min max_int counts in
          check
            (largest <= (workers + 7) / 8)
            (Printf.sprintf "%d workers: a member runs on %d workers" workers largest);
          check
            (d < Array.length members || largest - smallest <= 1)
            (Printf.sprintf "%d workers: members differ by %d" workers (largest - smallest));
          equal (Array.fold_left ( + ) 0 counts) d
            (Printf.sprintf "%d workers: diversified half" workers);
          (* No deterministic search runs twice (the E copies stay below their periods: 11 and
             26), and every worker count extends the one before by one worker. *)
          check
            (Strategy.deterministic_repeat resolved = None)
            (Printf.sprintf "%d workers repeat an E search" workers);
          if workers > 1 then
            let before = resolve (workers - 1) in
            let key (w : Strategy.worker) =
              (w.strategy.name, if w.strategy.heuristic = None then -1 else w.phase)
            in
            let sorted l = List.sort compare (List.map key l) in
            let rec remove x = function
              | [] -> None
              | y :: rest when y = x -> Some rest
              | y :: rest -> Option.map (fun r -> y :: r) (remove x rest)
            in
            check
              (List.for_all (fun k -> List.mem k (sorted resolved)) (sorted before)
              && List.length resolved = List.length before + 1
              && Option.is_some
                   (List.fold_left
                      (fun acc k -> Option.bind acc (remove k))
                      (Some (sorted resolved))
                      (sorted before)))
              (Printf.sprintf "%d workers do not extend %d" workers (workers - 1))
        done;
        (* Distinct searches: every worker runs its own (strategy, phase modulo period) up to 44
           workers; from 45 on the production half repeats phases modulo 22, and only it. *)
        for workers = 1 to 64 do
          let repeats = Scheduler.repeated_workers ~workers Scheduler.default_config in
          let p = (workers + 1) / 2 in
          equal repeats
            (List.init (max 0 (p - 22)) (fun k -> (22 + k, k)))
            (Printf.sprintf "%d workers: repeated searches" workers);
          equal
            (Scheduler.repeat_warning ~workers Scheduler.default_config = None)
            (workers <= 44)
            (Printf.sprintf "%d workers: warning" workers)
        done;
        equal (Scheduler.distinct_workers ~workers:64 Scheduler.default_config) 44 "balanced limit";
        equal
          (Scheduler.distinct_workers ~workers:64
             { Scheduler.default_config with portfolio = Strategy.Uniform })
          22 "all-production limit";
        (* The rule is the measured explicit lists, physically and phase for phase. *)
        List.iter
          (fun (spec, workers) ->
            match Strategy.portfolio_of_string spec with
            | Strategy.Workers l, None ->
                check
                  (List.for_all2
                     (fun (a : Strategy.worker) (b : Strategy.worker) ->
                       a.strategy == b.strategy && a.phase = b.phase)
                     (Strategy.resolve (Strategy.Workers l) ~base:Strategy.production ~workers)
                     (resolve workers))
                  (spec ^ " differs from the balanced portfolio")
            | _ -> failwith (spec ^ " is not a worker list"))
          [
            ("production,e208", 2);
            ("production,production,e208,y1346", 4);
            ("production,production,production,production,e208,y1346,sat001,calc:e", 8);
            ( "production,production,production,production,production,e208,y1346,sat001,calc:e,e208",
              10 );
          ];
        check (Strategy.portfolio_of_string "balanced" = (Strategy.Balanced, None)) "balanced spec";
        (* A deterministic base runs at distinct phases (its copy index) until its period. *)
        let e208 = Strategy.of_name "e208" in
        equal
          (List.map
             (fun (w : Strategy.worker) -> (w.strategy.name, w.phase))
             (Strategy.resolve Strategy.Balanced ~base:e208 ~workers:3))
          [ ("e208", 0); ("e208", 1); ("e208", 2) ]
          "a deterministic base did not take its copy index";
        check
          (rejects (fun () -> ignore (Strategy.resolve Strategy.Balanced ~base:e208 ~workers:18)))
          "a deterministic base was repeated past its period";
        check
          (Strategy.assign Strategy.Balanced ~base:e208 ~workers:1 0 == e208)
          "one worker does not run the base";
        (* Through the scheduler, also in a run. *)
        let theory = Theory.create "naive" in
        let r =
          Scheduler.portfolio ~workers:4 { Test_support.config with portfolio = Strategy.Balanced }
            (fun () -> Theory.copy theory)
        in
        equal (names_of r)
          [ (0, "production"); (1, "production"); (2, "e208"); (3, "y1346") ]
          "balanced portfolio was not threaded to the workers";
        List.iter (fun (w : Scheduler.worker_metrics) -> check_engine w.engine w.strategy) r.workers;
        check (r.certificate <> None) "balanced portfolio failed on Russell";
        (* Each worker's configuration carries its phase, plus the internal phase base. *)
        let worker_phases ?(phase_base = 0) workers =
          List.map
            (fun (c : Scheduler.config) -> c.worker_phase)
            (Scheduler.worker_configs ~workers { Scheduler.default_config with phase_base })
        in
        equal (worker_phases 8)
          (List.map Option.some [ 0; 1; 2; 3; 0; 0; 0; 7 ])
          "8 workers: resolved phases";
        equal (worker_phases ~phase_base:5 10)
          (List.map Option.some [ 5; 6; 7; 8; 9; 5; 5; 5; 13; 6 ])
          "10 workers: resolved phases with a phase base" );
    ( "a ported E heuristic is deterministic in its queue phase and distinct across phases",
      fun () ->
        (* A given-bounded search from the same input: the sequence of clauses that became active.
           Groups of exponent 3 need not commute, so every search runs to the bound. *)
        let problem =
          "cnf(left_identity,axiom,mult(e,X)=X). cnf(left_inverse,axiom,mult(inv(X),X)=e). \
           cnf(associativity,axiom,mult(mult(X,Y),Z)=mult(X,mult(Y,Z))). \
           cnf(cube,axiom,mult(X,mult(X,X))=e). cnf(goal,negated_conjecture,mult(a,b)!=mult(b,a))."
        in
        let given (s : Strategy.t) phase =
          let theory = Tptp.parse problem in
          let seen = ref [] in
          let e =
            Engine.create ~phase
              ~on_active:(fun (step : Wire.step) ->
                seen := (step.id, Wire.clause_string step.clause) :: !seen)
              {
                Engine.default_config with
                strategy = s;
                goal_names = [ "goal" ];
                budget = Engine.no_budget;
                limits = { Engine.default_limits with seconds = 30.; max_given = 50 };
              }
          in
          Engine.prepare_ordering e (Theory.fixed theory);
          List.iter (Engine.add_axiom e) (Theory.fixed theory);
          let n = ref 0 in
          while e.root = None && e.stopped = None && Engine.has_work e && !n < 200_000 do
            Engine.step e;
            incr n
          done;
          (List.rev !seen, e.metrics.generated, e.stopped)
        in
        List.iter
          (fun name ->
            let s = Strategy.of_name name in
            let period = Strategy.heuristic_period (Option.get s.heuristic) in
            let base = given s 0 in

            let sequence (l, _, _) = l in
            let _, _, stopped = base in
            equal stopped (Some "given clause limit") (name ^ ": the fixture ends before the bound");
            check (given s 0 = base) (name ^ ": phase 0 twice gave different searches");
            check (given s period = base) (name ^ ": the phase period did not repeat the search");
            check (sequence (given s 1) <> sequence base) (name ^ ": phases 0 and 1 gave one search");
            check
              (sequence (given s 2) <> sequence (given s 1))
              (name ^ ": phases 1 and 2 gave one search"))
          [ "e208"; "y1346"; "sat001" ];
        equal
          (List.map
             (fun name -> Strategy.heuristic_period (Option.get (Strategy.of_name name).heuristic))
             [ "e208"; "y1346"; "sat001"; "e208k"; "y1346k"; "sat001k" ])
          [ 11; 26; 11; 11; 26; 11 ] "E queue-mix periods";
        equal
          (List.map
             (Strategy.queue_period ~policy:Engine.default_config.clause_weight
                ~ratio:Engine.default_config.weight_ratio)
             [ Strategy.production; Strategy.calc_e; Strategy.of_name "e208" ])
          [ 22; 22; 11 ] "queue periods of the default engine" );
    ( "engine components follow a non-production strategy",
      fun () ->
        List.iter
          (fun s ->
            let e = Engine.create { Engine.default_config with strategy = s } in
            check_engine e s)
          [ proto_e; plain; combo ] );
    ( "portfolio threads each worker strategy through the scheduler",
      fun () ->
        let theory = Theory.create "naive" in
        let run portfolio workers =
          let config =
            {
              Test_support.config with
              portfolio;
              engine = { Test_support.config.engine with strategy = plain };
            }
          in
          Scheduler.portfolio ~workers config (fun () -> Theory.copy theory)
        in
        let r = run (Strategy.Workers [ Strategy.production; proto_e; plain ]) 3 in
        equal (names r)
          [ (0, "production"); (1, "proto:e"); (2, "test:plain") ]
          "worker strategies were not applied in worker order";
        List.iter (fun (w : Scheduler.worker_metrics) -> check_engine w.engine w.strategy) r.workers;
        check (r.certificate <> None) "portfolio failed on Russell";
        equal
          (names (run Strategy.Uniform 2))
          [ (0, "test:plain"); (1, "test:plain") ]
          "uniform portfolio ignored the base strategy";
        check
          (rejects (fun () -> ignore (run (Strategy.Workers [ proto_e ]) 2)))
          "portfolio accepted a strategy list of the wrong length" );
    ( "worker and summary CSV rows name each worker strategy",
      fun () ->
        let theory = Theory.create "naive" in
        let config =
          { Test_support.config with portfolio = Strategy.Workers [ Strategy.production; proto_e ] }
        in
        let r = Scheduler.portfolio ~workers:2 config (fun () -> Theory.copy theory) in
        (* Minimal RFC 4180 split: JSON observation columns contain commas. *)
        let fields line =
          let buffer = Buffer.create 64 and out = ref [] in
          let n = String.length line in
          let push () =
            out := Buffer.contents buffer :: !out;
            Buffer.clear buffer
          in
          let rec plain i =
            if i < n then
              match line.[i] with
              | ',' ->
                  push ();
                  plain (i + 1)
              | '"' -> quoted (i + 1)
              | c ->
                  Buffer.add_char buffer c;
                  plain (i + 1)
          and quoted i =
            if i < n then
              if line.[i] = '"' && i + 1 < n && line.[i + 1] = '"' then (
                Buffer.add_char buffer '"';
                quoted (i + 2))
              else if line.[i] = '"' then plain (i + 1)
              else (
                Buffer.add_char buffer line.[i];
                quoted (i + 1))
          in
          plain 0;
          push ();
          List.rev !out
        in
        let column text name =
          match List.map fields (String.split_on_char '\n' (String.trim text)) with
          | header :: rows -> List.map (fun row -> List.assoc name (List.combine header row)) rows
          | [] -> failwith "empty CSV"
        in
        let workers = Metrics_csv.workers r in
        equal (column workers "strategy") [ "production"; "proto:e" ] "worker CSV strategy column";
        equal (column workers "worker") [ "0"; "1" ] "worker CSV order";
        let summary = Metrics_csv.summary ~output_seconds:0. r in
        equal (column summary "strategy")
          [ List.nth [ "production"; "proto:e" ] r.worker_id ]
          "summary names the proving worker strategy" );
    ( "precedence tables are per engine and the standard order is never written",
      fun () ->
        let f x = Fn (Original "f", [ x ]) and a = constant "a" and b = constant "b" in
        (* b occurs more often than a, so invfreq ranks a above b. *)
        let clauses = [ [ positive (p [ b; b; f b ]) ]; [ negative (p [ a; b; b ]) ] ] in
        let order = Ordering.create () in
        Ordering.install order ~weights:false clauses;
        check (Ordering.greater ~order a b) "invfreq did not rank the rare constant higher";
        check (Ordering.greater b a) "alphabetical order changed";
        check (not (Ordering.greater ~order b a)) "invfreq order is not strict";
        check (rejects (fun () -> Ordering.install order ~weights:false clauses)) "reinstalled";
        check
          (rejects (fun () -> Ordering.install Ordering.standard ~weights:false clauses))
          "the shared standard order accepted a table";
        check (Ordering.standard.table = None) "standard order was modified";
        let e = Engine.create { Engine.default_config with strategy = combo } in
        Engine.prepare_ordering e [];
        check (e.order.table <> None) "strategy precedence was not installed";
        let production = Engine.create Engine.default_config in
        Engine.prepare_ordering production [];
        check (production.order.table = None) "production installed a precedence" );
    ( "the standard portfolio runs calc:e on worker 1 only",
      fun () ->
        let assign workers =
          List.init workers (Strategy.assign Strategy.Standard ~base:Strategy.production ~workers)
          |> List.map (fun (s : Strategy.t) -> s.name)
        in
        equal (assign 1) [ "production" ] "one worker left production";
        equal (assign 2) [ "production"; "calc:e" ] "two-worker portfolio";
        equal (assign 4)
          [ "production"; "calc:e"; "production"; "production" ]
          "four-worker portfolio";
        let theory = Theory.create "naive" in
        let r =
          Scheduler.portfolio ~workers:4 { Test_support.config with portfolio = Strategy.Standard }
            (fun () -> Theory.copy theory)
        in
        equal (names r)
          [ (0, "production"); (1, "calc:e"); (2, "production"); (3, "production") ]
          "Standard portfolio was not threaded to the workers";
        List.iter (fun (w : Scheduler.worker_metrics) -> check_engine w.engine w.strategy) r.workers;
        (* The default portfolio is the balanced rule; Uniform runs production on every worker. *)
        let default =
          Scheduler.portfolio ~workers:4 Test_support.config (fun () -> Theory.copy theory)
        in
        equal (names default)
          [ (0, "production"); (1, "production"); (2, "e208"); (3, "y1346") ]
          "default portfolio is not the balanced rule";
        let uniform =
          Scheduler.portfolio ~workers:4 { Test_support.config with portfolio = Strategy.Uniform }
            (fun () -> Theory.copy theory)
        in
        equal (names uniform)
          [ (0, "production"); (1, "production"); (2, "production"); (3, "production") ]
          "uniform portfolio left production";
        let single =
          Scheduler.portfolio ~workers:1 Test_support.config (fun () -> Theory.copy theory)
        in
        equal (names single) [ (0, "production") ] "single worker left production" );
    ( "evaluation portfolio specifications",
      fun () ->
        check (Strategy.portfolio_of_string "standard" = (Strategy.Standard, None)) "standard";
        (match Strategy.portfolio_of_string "calc:e" with
        | Strategy.Uniform, Some s -> check (s == Strategy.calc_e) "uniform calc:e"
        | _ -> failwith "single name is not uniform");
        (match Strategy.portfolio_of_string "production,calc:e,proto:e" with
        | Strategy.Workers [ a; b; c ], None ->
            check (a == Strategy.production && b == Strategy.calc_e && c == proto_e) "worker list"
        | _ -> failwith "list is not per worker");
        check (rejects (fun () -> ignore (Strategy.portfolio_of_string "calc:e,"))) "empty name";
        (* The Standard composition is also expressible as an explicit list. *)
        let standard_as_list =
          match Strategy.portfolio_of_string "production,calc:e,production,production" with
          | Strategy.Workers l, None -> l
          | _ -> failwith "Standard list is not per worker"
        in
        check
          (List.for_all2 ( == ) standard_as_list
             (List.init 4 (Strategy.assign Strategy.Standard ~base:Strategy.production ~workers:4)))
          "explicit Standard list differs from the Standard portfolio";
        (* A deterministic E strategy named again runs at its next queue phase (its copy
           index), in a list as in Uniform; a list that names it more often than its period
           would repeat one search and is refused. Production-queue strategies repeat at their
           worker index, and distinct E strategies, including an E-instance variant, combine. *)
        let times n name = String.concat "," (List.init n (fun _ -> name)) in
        List.iter
          (fun spec ->
            check (rejects (fun () -> ignore (Strategy.portfolio_of_string spec))) (spec ^ " parsed"))
          [ times 12 "e208"; "production," ^ times 12 "sat001"; times 27 "y1346" ];
        List.iter
          (fun spec ->
            match Strategy.portfolio_of_string spec with
            | Strategy.Workers _, None -> ()
            | _ -> failwith (spec ^ " is not a worker list"))
          [
            "production,production";
            "calc:e,calc:e";
            "e208,e208k,y1346,y1346k";
            "e208,production,y1346,production";
            "e208,e208";
            "production,e208,y1346,e208";
            "y1346k,production,y1346k";
            times 11 "e208";
            times 26 "y1346";
          ];
        let e208 = Strategy.of_name "e208" in
        equal
          (List.map
             (fun (w : Strategy.worker) -> w.phase)
             (Strategy.resolve
                (Strategy.Workers [ e208; Strategy.production; e208; Strategy.calc_e; e208 ])
                ~base:Strategy.production ~workers:5))
          [ 0; 1; 1; 3; 2 ] "worker list phases";
        check
          (rejects (fun () ->
               ignore
                 (Strategy.assign
                    (Strategy.Workers (List.init 12 (fun _ -> e208)))
                    ~base:Strategy.production ~workers:12 1)))
          "a configured worker list repeated an e208 search";
        (* One name for every worker: the copies run at phases 0, 1, ... up to the period. *)
        equal
          (List.init 11 (Strategy.phase_of Strategy.Uniform ~base:e208 ~workers:11))
          (List.init 11 Fun.id) "uniform e208 phases";
        check
          (rejects (fun () -> ignore (Strategy.assign Strategy.Uniform ~base:e208 ~workers:12 0)))
          "uniform e208 repeated a search" );
    ( "E-style selection follows SelectMaxLComplexAvoidPosPred",
      fun () ->
        let f x = Fn (Original "f", [ x ]) in
        let atom name ts = P (name, ts) in
        let select clause = Ordering.e_selection clause in
        (* A Horn rule whose head dominates the body selects nothing. *)
        let rule = [ negative (atom "p" [ v 0 ]); positive (atom "q" [ f (v 0) ]) ] in
        equal (Ordering.maximal_flags rule) [| false; true |] "head does not dominate the body";
        equal (select rule) None "unique maximal literal was restricted";
        equal (Ordering.first_negative rule) (Some 0) "production selection changed";
        equal
          (select [ positive (atom "p" [ v 0 ]); positive (atom "q" [ v 1 ]) ])
          None "positive clause selected a literal";
        (* Two maximal literals: the maximal negative one wins over a dominated one. *)
        let two =
          [ negative (atom "p" [ v 0 ]); negative (atom "q" [ v 1 ]); positive (atom "r" [ v 0 ]) ]
        in
        equal (Ordering.maximal_flags two) [| false; true; true |] "maximality flags";
        equal (select two) (Some 1) "a dominated negative literal was selected";
        (* Among maximal negative literals: most complex first ... *)
        let complex =
          [
            negative (atom "p" [ v 0 ]);
            negative (atom "q" [ f (v 1) ]);
            positive (atom "r" [ v 2 ]);
          ]
        in
        equal (select complex) (Some 1) "the more complex literal was not preferred";
        (* ... then avoid predicates that also occur positively. *)
        let avoid =
          [ negative (atom "p" [ v 0 ]); negative (atom "q" [ v 1 ]); positive (atom "p" [ v 2 ]) ]
        in
        equal (select avoid) (Some 1) "a positively occurring predicate was preferred";
        equal (Ordering.best_negative avoid) (Some 1) "maxw ignored the predicate tie-break";
        (* The calculus memoizes the choice and derives the inference candidates. *)
        let step id clause = { id; clause; rule = Input (id, 0) } in
        let fixed = Calculus.create ~ordered:true ~strategy:Strategy.calc_e (Term.create ()) in
        let raw = Calculus.create ~ordered:true ~strategy:proto_e (Term.create ()) in
        let production = Calculus.create ~ordered:true (Term.create ()) in
        equal (Calculus.selected production (step 0 rule)) (Some [ 0 ]) "production selection";
        equal (Hashtbl.length production.memo) 0 "production used the selection memo";
        equal (Calculus.selected fixed (step 0 rule)) None "calc:e restricted a Horn rule";
        (* Step ids are unique in an engine; the memo is keyed by them. *)
        let candidates c id clause =
          List.filteri (fun i _ -> Calculus.candidates c (step id clause) i) clause
        in
        equal (candidates fixed 0 rule) [ List.nth rule 1 ] "only the head is a candidate";
        equal (candidates raw 0 rule) rule "proto:e filtered candidates";
        equal (candidates fixed 1 two) [ List.nth two 1 ] "selected literal is the only candidate";
        equal (Hashtbl.find fixed.memo 1).flags None "a selected clause kept maximality flags";
        check (Hashtbl.mem fixed.memo 0) "calc:e did not memoize its choice";
        Calculus.forget fixed 0;
        check (not (Hashtbl.mem fixed.memo 0)) "forgotten selection stayed" );
    ( "maximal candidates drop only inferences that fail after unification",
      fun () ->
        let rng = Random.State.make [| 20261114; 9 |] in
        let rec term depth =
          if depth = 0 then
            if Random.State.bool rng then v (Random.State.int rng 3) else constant "a"
          else
            match Random.State.int rng 4 with
            | 0 -> v (Random.State.int rng 3)
            | 1 -> constant "b"
            | _ ->
                Fn
                  ( Original (if Random.State.bool rng then "f" else "g"),
                    List.init (1 + Random.State.int rng 2) (fun _ -> term (depth - 1)) )
        in
        let literal () =
          let atom =
            match Random.State.int rng 3 with
            | 0 -> P ("p", [ term 2; term 1 ])
            | 1 -> E (term 2, term 1)
            | _ -> P ("q", [ term 1 ])
          in
          { positive = Random.State.bool rng; atom }
        in
        let f x = Fn (Original "f", [ x ]) in
        let clauses =
          [
            [ negative (P ("q", [ v 0 ])); positive (P ("q", [ f (v 0) ])) ];
            [ negative (P ("q", [ v 0 ])); positive (E (f (v 0), v 0)) ];
            [ positive (P ("q", [ v 0 ])); positive (P ("q", [ f (v 0) ])) ];
            [ negative (P ("q", [ f (f (constant "a")) ])) ];
          ]
          @ List.init 40 (fun _ -> List.init (1 + Random.State.int rng 3) (fun _ -> literal ()))
        in
        let entries =
          List.mapi
            (fun id clause -> { id; clause = Clause.normalize clause; rule = Input (id, 0) })
            clauses
        in
        let fixed = Calculus.create ~ordered:true ~strategy:Strategy.calc_e (Term.create ()) in
        let raw = Calculus.create ~ordered:true ~strategy:proto_e (Term.create ()) in
        let collect f =
          let xs = ref [] in
          f (fun clause rule -> xs := (clause, rule) :: !xs);
          List.rev !xs
        in
        let unselected =
          List.filter
            (fun s -> Calculus.selected fixed s = None && List.length s.clause > 1)
            entries
        in
        check (List.length unselected >= 8) "fixture exercised too few unselected clauses";
        let narrowed =
          List.filter
            (fun s ->
              List.exists
                (fun i -> not (Calculus.candidates fixed s i))
                (List.init (List.length s.clause) Fun.id))
            unselected
        in
        check (List.length narrowed >= 4) "fixture exercised too few dominated literals";
        (* Brute force over every literal pair, against the unfiltered calculus. *)
        let produced = ref 0 in
        List.iter
          (fun given ->
            equal (Calculus.selected fixed given) (Calculus.selected raw given) "selection differs";
            equal
              (collect (Calculus.unary fixed given))
              (collect (Calculus.unary raw given))
              "factoring or equality resolution lost";
            equal
              (collect (Calculus.equality_factor fixed given))
              (collect (Calculus.equality_factor raw given))
              "equality factoring lost";
            List.iter
              (fun other ->
                let expected = collect (Calculus.resolve raw given other) in
                produced := !produced + List.length expected;
                equal (collect (Calculus.resolve fixed given other)) expected "resolution lost";
                equal
                  (collect (Calculus.paramodulate fixed given other))
                  (collect (Calculus.paramodulate raw given other))
                  "paramodulation lost")
              entries)
          entries;
        check (!produced > 50) "fixture produced too few resolvents";
        check (fixed.attempts < raw.attempts) "candidate filter saved no unification attempt";
        check (fixed.ordering_rejected < raw.ordering_rejected) "no rejected unification avoided";
        (* Active indices built from the candidates still find every brute-force inference. *)
        let index = Index.create () and equality = Equality_index.create () in
        List.iter
          (fun s ->
            let eligible = Calculus.candidates fixed s in
            Index.add ~eligible index s;
            Equality_index.add ~eligible equality s)
          entries;
        List.iter
          (fun given ->
            let eligible = Calculus.candidates fixed given in
            let res = Index.matches ~eligible index given.clause in
            let eq = Equality_index.matches ~eligible equality ~variables:false given.clause in
            List.iter
              (fun other ->
                let pairs =
                  match List.find_opt (fun ((s : step), _) -> s.id = other.id) res with
                  | None -> []
                  | Some (_, pairs) -> pairs
                in
                equal
                  (collect (Calculus.resolve ~positions:pairs fixed given other))
                  (collect (Calculus.resolve raw given other))
                  "indexed resolution lost an inference";
                let out_, in_ =
                  match List.find_opt (fun ((s : step), _, _) -> s.id = other.id) eq with
                  | None -> ([], [])
                  | Some (_, out_, in_) -> (out_, in_)
                in
                equal
                  (collect (Calculus.paramodulate ~positions:out_ fixed given other))
                  (collect (Calculus.paramodulate raw given other))
                  "indexed outgoing paramodulation lost an inference";
                equal
                  (collect (Calculus.paramodulate ~positions:in_ fixed other given))
                  (collect (Calculus.paramodulate raw other given))
                  "indexed incoming paramodulation lost an inference")
              entries)
          entries );
    ( "selection memo keeps only live premises",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(r1,axiom,(~holds(X,S) | holds(f(X),do(a,S)))). cnf(r2,axiom,(~holds(X,S) | \
             ~holds(Y,S) | holds(g(X,Y),S))). cnf(r3,axiom,(~holds(X,S) | holds(X,do(b,S)))). \
             cnf(init,axiom,holds(c,s0)). \
             cnf(goal,negated_conjecture,~holds(g(f(c),g(c,c)),do(a,do(b,s0))))."
        in
        let e =
          Engine.create
            {
              Engine.default_config with
              strategy = Strategy.calc_e;
              collect_every = 0;
              limits = { Engine.default_limits with seconds = 5. };
            }
        in
        List.iter (Engine.add_axiom e) (Theory.fixed theory);
        Engine.run_steps e 40;
        check (Hashtbl.length e.calculus.memo > 0) "calc:e kept no selection";
        let live id = Index.mem e.index id || Index.mem e.retained_index id in
        Engine.collect e;
        Hashtbl.iter
          (fun id _ -> check (live id) "collection kept a dead premise selection")
          e.calculus.memo;
        match Hashtbl.fold (fun id _ acc -> id :: acc) e.calculus.memo [] with
        | [] -> failwith "collection dropped every live selection"
        | id :: _ ->
            Engine.retire e id;
            check (not (Hashtbl.mem e.calculus.memo id)) "deactivation kept the selection" );
    ( "calc:e refutes a backward-chaining Horn problem through the kernel",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(r1,axiom,(~holds(X,S) | holds(f(X),do(a,S)))). cnf(r2,axiom,(~holds(X,S) | \
             ~holds(Y,S) | holds(g(X,Y),S))). cnf(r3,axiom,(~holds(X,S) | holds(X,do(b,S)))). \
             cnf(init,axiom,holds(c,s0)). \
             cnf(goal,negated_conjecture,~holds(g(f(c),f(c)),do(a,s0)))."
        in
        List.iter
          (fun strategy ->
            let config =
              {
                Scheduler.default_config with
                reference = false;
                max_instances = 0;
                max_guided_instances = 0;
                portfolio = Strategy.Uniform;
                engine = { Engine.default_config with strategy };
              }
            in
            let r = Scheduler.portfolio ~workers:1 config (fun () -> Theory.copy theory) in
            match r.certificate with
            | None -> failwith (strategy.Strategy.name ^ " found no refutation: " ^ r.reason)
            | Some cert ->
                check (Result.is_ok (Kernel.check theory cert)) "kernel rejected the refutation")
          (* A Vampire slice with a set of support is incomplete by design: without a negated
             conjecture every input clause is active and nothing is ever selected. *)
          (List.filter
             (fun (s : Strategy.t) ->
               match s.heuristic with
               | Some { vampire = Some v; _ } -> Vampire.complete v
               | _ -> true)
             (List.map Strategy.of_name Strategy.names)) );
  ]

let () = run tests
