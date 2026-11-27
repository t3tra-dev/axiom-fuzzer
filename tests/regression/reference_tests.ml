open Axiom_fuzzer
open Test_support
open Wire

let quiet () = ()
let limits n = { Reference.default_config with seconds = 3.; max_trials = n }
let contradiction () = Tptp.parse "fof(p,axiom,p(a)). fof(n,axiom,~p(a))."
let satisfiable () = Tptp.parse "fof(p,axiom,p(a))."

let with_path f =
  let path = Filename.temp_file "axiom-reference-test-" ".checkpoint" in
  Sys.remove path;
  Fun.protect
    ~finally:(fun () ->
      List.iter (fun p -> if Sys.file_exists p then Sys.remove p) [ path; path ^ ".lock" ])
    (fun () -> f path)

let tests =
  [
    ( "typed reference independently refutes complementary inputs",
      fun () ->
        let t = contradiction () in
        let r = Reference.run (limits 1000) t in
        check (r.certificate <> None) "typed reference missed contradiction";
        check
          (Result.is_ok (Kernel.check t (Option.get r.certificate)))
          "reference proof failed replay";
        equal r.tested 29 "reference inference catalogue changed";
        check (r.byte_tested > 0 && r.script_tested > 0) "a lane was starved" );
    ( "reference byte lane and resumed proof retain certificate mode",
      fun () ->
        with_path (fun path ->
            let t = Tptp.parse "fof(bot,axiom,$false)." in
            let cert =
              {
                natural = None;
                avatar = None;
                cnf_mode = Distributive;
                theory = Theory.name t;
                axioms = Theory.fixed t;
                steps = [ { id = 0; clause = []; rule = Input (0, 0) } ];
                root = 0;
              }
            in
            let state = Reference.create t in
            state.tested <- 15;
            state.script_tested <- 15;
            let encoded = Certificate_io.encode cert in
            state.bytes <- Array.init (String.length encoded) (fun i -> Char.code encoded.[i]);
            equal (Reference.step state) (Some cert) "byte lane did not decode and verify a proof";
            Sexp.write_file path (Reference.checkpoint_text state);
            let result = Reference.run { (limits 0) with checkpoint = Some path } t in
            equal (Option.get result.certificate).cnf_mode Distributive
              "reference proof export changed the CNF mode";
            equal result.certificate (Some cert) "reference proof changed after restart") );
    ( "reference unifier checks occurs and scopes independently",
      fun () ->
        let x = V (1, 0) and y = V (2, 0) in
        equal
          (Reference_rules.unify ~guard:quiet [ (x, Fn (Original "f", [ x ])) ])
          None "occurs check failed";
        let sigma = Option.get (Reference_rules.unify ~guard:quiet [ (x, y); (y, constant "a") ]) in
        equal (Reference_rules.apply sigma x) (constant "a") "substitution chain failed" );
    ( "reference inference catalogue includes equality and factoring",
      fun () ->
        let clauses =
          [
            [ positive (E (constant "a", constant "b")) ];
            [ positive (p [ Fn (Original "f", [ constant "a" ]) ]) ];
            [ negative (E (v 0, constant "a")) ];
            [ positive (p [ v 0 ]); positive (p [ constant "a" ]) ];
          ]
        in
        let steps = List.mapi (fun id clause -> { id; clause; rule = Input (0, id) }) clauses in
        let rec all i acc =
          match Reference_rules.choose ~guard:quiet ~inputs:[] ~steps i with
          | None -> acc
          | Some s -> all (i + 1) (s :: acc)
        in
        let results = all 0 [] in
        check
          (List.exists
             (fun (s : step) ->
               match s.rule with Paramodulate (_, _, _, _, _, [ 0; 0 ], _) -> true | _ -> false)
             results)
          "nested paramodulation missing";
        check
          (List.exists
             (fun (s : step) -> match s.rule with Equality_resolve _ -> true | _ -> false)
             results)
          "equality resolution missing";
        check
          (List.exists
             (fun (s : step) -> match s.rule with Factor _ -> true | _ -> false)
             results)
          "factoring missing" );
    ( "reference continues after heuristic budget exhaustion",
      fun () ->
        let cfg =
          {
            config with
            reference = true;
            reference_config = limits 1000;
            engine = { config.engine with limits = { config.engine.limits with max_generated = 0 } };
          }
        in
        let r = Scheduler.run cfg (contradiction ()) in
        check
          ((Option.get r.reference_report).trials = 1000)
          "reference was tied to heuristic budget";
        equal r.engine.metrics.generated 0 "heuristic ignored zero budget";
        let csv = Metrics_csv.summary ~output_seconds:0. r in
        check (String.length csv > 0) "reference summary failed";
        equal (List.length r.workers) 1 "reference counted as a heuristic worker" );
    ( "reference checkpoint restarts at the same next candidate",
      fun () ->
        with_path (fun path ->
            let t = satisfiable () in
            let a = Reference.run { (limits 67) with checkpoint = Some path } t in
            let b = Reference.run { (limits 133) with checkpoint = Some path } t in
            let resumed = Reference.create t in
            Reference.restore resumed (Sexp.read_file path);
            let uninterrupted = Reference.create t in
            for _ = 1 to 200 do
              ignore (Reference.step uninterrupted)
            done;
            equal
              (Reference.checkpoint_text resumed)
              (Reference.checkpoint_text uninterrupted)
              "restart skipped or repeated a cursor";
            equal
              (a.trials, b.trials, b.tested, b.byte_tested)
              (67, 133, 200, 12) "checkpoint counters lost progress";
            check (b.resumed && b.certificate = None) "satisfiable reference result incorrect") );
    ( "schema corpus is reproducible after restart",
      fun () ->
        let theory = Theory.create "zf" in
        let a = Reference.create theory in
        for _ = 1 to 50 do
          ignore (Reference.step a)
        done;
        let b = Reference.create theory in
        Reference.restore b (Reference.checkpoint_text a);
        Reference.ensure_inputs ~guard:quiet a;
        Reference.ensure_inputs ~guard:quiet b;
        equal a.axioms b.axioms "schema IDs or formulas changed after restart";
        equal a.inputs b.inputs "CNF changed after restart";
        check
          (List.exists
             (fun (a : axiom) ->
               match a.origin with Instance (Separation, _) -> true | _ -> false)
             a.axioms)
          "separation starved";
        check
          (List.exists
             (fun (a : axiom) ->
               match a.origin with Instance (Replacement, _) -> true | _ -> false)
             a.axioms)
          "replacement starved" );
    ( "checkpoints bind the complete manifest and reject malformed cursors",
      fun () ->
        let a = Reference.create (satisfiable ()) in
        let b = Reference.create (Tptp.parse "fof(p,axiom,~p(a)).") in
        check
          (rejects (fun () -> Reference.restore b (Reference.checkpoint_text a)))
          "same-name different theory accepted";
        let broken =
          match Sexp.parse (Reference.checkpoint_text a) with
          | Sexp.List (tag :: version :: algorithm :: manifest :: _stage :: rest) ->
              Sexp.to_string
                (Sexp.List (tag :: version :: algorithm :: manifest :: Atom "0" :: rest))
          | _ -> assert false
        in
        check (rejects (fun () -> Reference.restore a broken)) "invalid diagonal accepted";
        check (rejects (fun () -> Reference.restore a "(")) "truncated checkpoint accepted" );
    ( "checkpoint lock excludes concurrent domains",
      fun () ->
        with_path (fun path ->
            Reference.with_checkpoint_lock (Some path) (fun () ->
                let d =
                  Domain.spawn (fun () ->
                      rejects (fun () -> Reference.with_checkpoint_lock (Some path) quiet))
                in
                check (Domain.join d) "another domain acquired the checkpoint lock")) );
    ( "reference rechecks saved witnesses before reporting UNSAT",
      fun () ->
        with_path (fun path ->
            let t = contradiction () in
            let first = Reference.run { (limits 1000) with checkpoint = Some path } t in
            check (first.certificate <> None) "initial witness missing";
            let zero = Reference.run { (limits 0) with seconds = 0.; checkpoint = Some path } t in
            check (zero.certificate = None) "unreplayed checkpoint witness accepted";
            let again = Reference.run { (limits 0) with checkpoint = Some path } t in
            equal first.certificate again.certificate "saved witness did not replay";
            let state = Reference.create t in
            Reference.restore state (Sexp.read_file path);
            state.witness <- Some { (Option.get state.witness) with root = 999 };
            Sexp.write_file path (Reference.checkpoint_text state);
            check
              (rejects (fun () ->
                   ignore (Reference.run { (limits 0) with checkpoint = Some path } t)))
              "forged saved proof accepted") );
    ( "cancellation leaves the pending reference cursor intact",
      fun () ->
        with_path (fun path ->
            let t = satisfiable () in
            ignore (Reference.run { (limits 31) with checkpoint = Some path } t);
            let before = Sexp.read_file path in
            let r =
              Reference.run
                ~cancelled:(fun () -> true)
                { (limits 100) with checkpoint = Some path }
                t
            in
            equal r.trials 0 "cancelled worker advanced";
            equal (Sexp.read_file path) before "cancellation changed pending cursor") );
    ( "small script diagonals cover every bounded choice word",
      fun () ->
        let t = Reference.create (satisfiable ()) and seen = Hashtbl.create 32 in
        while t.stage <= 5 do
          Hashtbl.replace seen (Array.to_list t.choices) ();
          Reference.advance_script t
        done;
        let rec words n =
          if n = 0 then [ [] ]
          else List.concat_map (fun rest -> List.init 3 (fun i -> i :: rest)) (words (n - 1))
        in
        for n = 1 to 3 do
          List.iter (fun word -> check (Hashtbl.mem seen word) "finite script omitted") (words n)
        done;
        t.bytes <- [| 255 |];
        Reference.advance_bytes t;
        equal t.bytes [| 0; 0 |] "shortlex byte carry failed" );
    ( "portfolio owns exactly one reference and joins it",
      fun () ->
        with_path (fun path ->
            let r =
              Scheduler.portfolio ~workers:3
                {
                  config with
                  reference = true;
                  reference_config = { (limits 96) with checkpoint = Some path };
                }
                satisfiable
            in
            let rr = Option.get r.reference_report in
            equal rr.trials 96 "reference was duplicated or stopped with heuristic exhaustion";
            equal (List.length r.workers) 3 "heuristic worker metrics missing";
            check
              (r.wall_seconds >= rr.seconds && r.certificate = None)
              "reference domain did not finish before return") );
  ]

let () = run tests
