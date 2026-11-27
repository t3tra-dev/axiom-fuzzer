open Axiom_fuzzer
open Test_support
open Wire

let drain state =
  let rec loop acc =
    match Guided.take state with None -> List.rev acc | Some f -> loop (f :: acc)
  in
  loop []

let complete_guidance state =
  let rec loop acc =
    if not (Guided.has_work state) then List.rev acc
    else (
      Guided.pump state;
      loop (List.rev_append (drain state) acc))
  in
  loop []

let demod_config =
  {
    config.engine with
    ordered = true;
    demodulation = true;
    backward_demodulation = true;
    weight_ratio = 0;
  }

let tests =
  [
    ( "deep rewrite preparation respects cancellation before building occurrence paths",
      fun () ->
        let rules = Demodulation.create () in
        Demodulation.add rules
          {
            id = 0;
            clause = [ positive (E (Fn (Original "f", [ v 0 ]), v 0)) ];
            rule = Input (0, 0);
          };
        let rec nest left t = if left = 0 then t else nest (left - 1) (Fn (Original "f", [ t ])) in
        let target =
          { id = 1; clause = [ positive (p [ nest 4096 (constant "a") ]) ]; rule = Input (1, 0) }
        in
        let exception Cancelled in
        let calls = ref 0 in
        let cancelled =
          try
            ignore
              (Demodulation.rewrite_once rules target ~guard:(fun () ->
                   incr calls;
                   if !calls = 4 then raise Cancelled));
            false
          with Cancelled -> true
        in
        check cancelled "a large term ignored cancellation during rewrite preparation";
        equal (Tbl.Int.length rules.live) 1 "cancelled preparation changed the rewrite rules" );
    ( "joint demands are conjunctions with one shared variable map",
      fun () ->
        let arena =
          Source.create (Signature.make ~functions:[ ("a", 0) ] ~predicates:[ ("p", 2); ("q", 1) ])
        in
        let guide = Guided.create ~config:{ Guided.default_config with max_size = 7 } arena in
        Guided.request guide [ positive (p [ constant "a"; v 4 ]); negative (P ("q", [ v 4 ])) ];
        let expected =
          Source.and_ arena
            [
              Source.pred arena "p" [ Source.apply arena "a" []; Source.free arena 0 ];
              Source.not_ arena (Source.pred arena "q" [ Source.free arena 0 ]);
            ]
        in
        equal
          (Option.get (Guided.take guide))
          expected "joint obligation became a disjunction or lost sharing";
        equal guide.metrics.demanded_offered 1 "joint demand bypassed the proposal queue" );
    ( "obligations rank legal schema arguments without adding premises",
      fun () ->
        let theory = Theory.create "naive" in
        let arena = Theory.arena theory in
        let state = Guided.create arena in
        Guided.admit state
          ~guard:(fun () -> ())
          (Source.member arena (Source.free arena 0) (Source.free arena 1));
        let demanded = [ negative (P ("member", [ v 4; v 4 ])) ] in
        Guided.request state demanded;
        Guided.request state [ positive (P ("member", [ Fn (Skolem (0, 0), []); v 0 ])) ];
        Guided.request state [ positive (D ((0, 0), [ v 0 ])) ];
        equal state.metrics.demands 1 "generated symbols entered Source guidance";
        let phi = Option.get (Guided.take state) in
        equal (Wire.export arena phi)
          (Neg (Pred ("member", [ F 0; F 0 ])))
          "wanted condition did not retain shared variables and polarity";
        equal state.metrics.demanded_offered 1 "demand selection was not recorded";
        equal (Theory.fixed theory) [] "guidance inserted an unauthorized premise";
        let axiom = Theory.instantiate theory ~id:0 Comprehension phi in
        check (Theory.validate_axiom theory axiom) "demand bypassed normal schema authorization" );
    ( "backward demodulation rewrites unselected Active literals with replayable ancestors",
      fun () ->
        let theory =
          Tptp.parse
            "fof(old,axiom,(p(f(a)) | ~q(a))). fof(rule,axiom,(![X]:f(X)=X)). fof(q,axiom,q(a)). \
             fof(n,axiom,~p(a))."
        in
        let axioms = Theory.fixed theory in
        let engine = Engine.create demod_config in
        Engine.add_axiom engine (List.nth axioms 0);
        select_given engine 0;
        check (Index.mem engine.index 0) "old clause was not active before new equality";
        let rule = Proof.length engine.proof in
        Engine.add_axiom engine (List.nth axioms 1);
        select_given engine rule;
        equal engine.metrics.backward_demodulated 1
          "new unit did not rewrite the unselected literal";
        check
          (not
             (Index.mem engine.index 0 || Index.mem engine.retained_index 0
             || Tbl.Int.mem engine.equality_index.live 0))
          "retired target remains indexed";
        let rewritten =
          List.init (Proof.length engine.proof) (Proof.get engine.proof)
          |> List.find (fun (s : step) ->
              match s.rule with Paramodulate (_, _, _, 0, _, _, _) -> true | _ -> false)
        in
        check (Tbl.Int.mem engine.passive.live rewritten.id) "replacement was not requeued";
        check (not (Index.mem engine.index rewritten.id)) "replacement treated as already processed";
        List.iter (Engine.add_axiom engine) (List.filteri (fun i _ -> i >= 2) axioms);
        Engine.finish engine;
        let certificate = Option.get (Engine.certificate engine ~theory:(Theory.name theory)) in
        check
          (List.exists (fun (s : step) -> s.id = 0) certificate.steps)
          "retired proof ancestor was lost";
        check
          (Result.is_ok (Kernel.check theory certificate))
          "backward rewrite proof failed replay" );
    ( "backward demodulation retires obsolete rewrite rules",
      fun () ->
        let theory = Tptp.parse "fof(old,axiom,(![X]:g(X)=f(X))). fof(new,axiom,(![X]:f(X)=X))." in
        let engine = Engine.create demod_config in
        Engine.add_axiom engine (List.nth (Theory.fixed theory) 0);
        select_given engine 0;
        check (Tbl.Int.mem engine.demodulator.live 0) "old rewrite rule not installed";
        let rule = Proof.length engine.proof in
        Engine.add_axiom engine (List.nth (Theory.fixed theory) 1);
        select_given engine rule;
        check (engine.metrics.backward_demodulated > 0) "rewrite rule RHS was not simplified";
        check
          (not (Tbl.Int.mem engine.demodulator.live 0 || Index.mem engine.index 0))
          "retired rule is still used for rewriting";
        Engine.finish engine;
        check (engine.root = None) "consistent rewrite system refuted" );
    ( "backward rewriting never instantiates target variables",
      fun () ->
        let theory = Tptp.parse "fof(old,axiom,(![X]:p(f(X)))). fof(rule,axiom,f(a)=b)." in
        let engine = Engine.create demod_config in
        Engine.add_axiom engine (List.nth (Theory.fixed theory) 0);
        select_given engine 0;
        let rule = Proof.length engine.proof in
        Engine.add_axiom engine (List.nth (Theory.fixed theory) 1);
        select_given engine rule;
        check (Index.mem engine.index 0) "a nonground target was replaced by a ground instance";
        equal engine.metrics.backward_demodulated 0 "unification was mistaken for matching" );
    ( "backward rewriting composes with subsumption and variant deletion",
      fun () ->
        List.iter
          (fun name ->
            let theory = Theory.create name in
            let result =
              Scheduler.run
                {
                  config with
                  engine =
                    {
                      demod_config with
                      weight_ratio = config.engine.weight_ratio;
                      backward_subsumption = true;
                      variants = true;
                    };
                }
                theory
            in
            let certificate = Option.get result.certificate in
            check
              (Result.is_ok (Kernel.check theory certificate))
              "combined simplifiers damaged the proof")
          [ "naive"; "foundation-self" ];
        let theory =
          Tptp.parse
            "fof(old,axiom,(p(f(a)) | ~q(a))). fof(rule,axiom,(![X]:f(X)=X)). fof(q,axiom,q(a)). \
             fof(n,axiom,~p(a))."
        in
        let engine =
          Engine.create { demod_config with backward_subsumption = true; variants = true }
        in
        let axioms = Theory.fixed theory in
        (* Activate the target before adding its rewrite rule. Admission-time
           unit deletion may otherwise close this fixture before any activation. *)
        Engine.add_axiom engine (List.hd axioms);
        select_given engine 0;
        let rule = Proof.length engine.proof in
        Engine.add_axiom engine (List.nth axioms 1);
        select_given engine rule;
        List.iter (Engine.add_axiom engine) (List.filteri (fun i _ -> i >= 2) axioms);
        Engine.finish engine;
        check
          (engine.metrics.backward_demodulated > 0)
          "combined simplifiers did not exercise a backward rewrite";
        check
          (Result.is_ok
             (Kernel.check theory
                (Option.get (Engine.certificate engine ~theory:(Theory.name theory)))))
          "combined simplifiers lost a retired ancestor" );
    ( "backward rewrite resource exhaustion preserves proof data",
      fun () ->
        let theory =
          Tptp.parse "fof(old,axiom,(p(f(a)) | ~q(a))). fof(rule,axiom,(![X]:f(X)=X))."
        in
        let engine =
          Engine.create { demod_config with limits = { demod_config.limits with max_retained = 2 } }
        in
        List.iter (Engine.add_axiom engine) (Theory.fixed theory);
        Engine.finish engine;
        check
          (engine.root = None && engine.stopped = Some "retained proof node limit")
          "limit did not return UNKNOWN";
        equal (Proof.length engine.proof) 2 "original proof ancestors disappeared";
        check
          (rejects (fun () -> ignore (Engine.create { demod_config with demodulation = false })))
          "inconsistent demodulation flags accepted" );
    ( "incremental atomic guidance agrees with the full-scan oracle",
      fun () ->
        let arena =
          Source.create
            (Signature.make ~functions:[ ("a", 0); ("f", 1) ] ~predicates:[ ("p", 2); ("q", 1) ])
        in
        let terms = [ v 0; v 1; constant "a"; Fn (Original "f", [ v 0 ]) ] in
        let clauses =
          List.concat_map
            (fun x ->
              List.map (fun y -> [ positive (P ("p", [ x; y ])); negative (E (x, y)) ]) terms)
            terms
        in
        let steps = List.mapi (fun id clause -> { id; clause; rule = Input (id, 0) }) clauses in
        let state =
          Guided.create
            ~config:
              { Guided.default_config with compounds = false; constraints = false; capacity = 1024 }
            arena
        in
        List.iter (Guided.observe state) steps;
        let actual = complete_guidance state |> List.sort_uniq compare in
        equal actual (Guided.candidates arena steps) "atomic candidate set changed";
        List.iter (Guided.observe state) steps;
        equal (complete_guidance state) [] "processed Active clauses were rescanned";
        equal state.metrics.processed (List.length steps) "incremental processing count is wrong" );
    ( "guided queue advances past already injected candidates",
      fun () ->
        let arena =
          Source.create
            (Signature.make ~functions:[]
               ~predicates:(List.init 20 (fun i -> ("p" ^ string_of_int i, 1))))
        in
        let state = Guided.create arena in
        List.init 20 (fun id ->
            {
              id;
              rule = Input (id, 0);
              clause = [ positive (P ("p" ^ string_of_int id, [ v 0 ])) ];
            })
        |> List.iter (Guided.observe state);
        for _ = 1 to 3 do
          Guided.pump state
        done;
        let skipped = ref 0 in
        let eligible _ =
          incr skipped;
          !skipped > 16
        in
        check
          (Option.is_some (Guided.take ~eligible state))
          "old first eight candidates blocked new proposals";
        equal state.metrics.already_injected 16 "duplicates consumed proposal slots";
        equal state.metrics.processed 20 "not all new Active clauses were visited" );
    ( "guided work and pending formulas obey local bounds",
      fun () ->
        let arena =
          Source.create
            (Signature.make ~functions:[]
               ~predicates:(List.init 5 (fun i -> ("p" ^ string_of_int i, 1))))
        in
        let state =
          Guided.create
            ~config:{ Guided.default_config with capacity = 2; clauses_per_cycle = 1 }
            arena
        in
        for id = 0 to 4 do
          Guided.observe state
            {
              id;
              rule = Input (id, 0);
              clause = [ positive (P ("p" ^ string_of_int id, [ v 0 ])) ];
            }
        done;
        equal state.metrics.dropped_events 3 "event backlog is unbounded";
        Guided.pump state;
        equal state.metrics.processed 1 "cycle clause budget ignored";
        Guided.pump state;
        equal (Queue.length state.pending) 2 "candidate backlog is unbounded";
        check
          (state.metrics.dropped > 0 && state.metrics.peak_pending = 2)
          "bounded candidate drops not recorded" );
    ( "guided synthesis filters search symbols and skips retired events",
      fun () ->
        let arena =
          Source.create (Signature.make ~functions:[ ("f", 1) ] ~predicates:[ ("p", 1) ])
        in
        let state =
          Guided.create
            ~config:{ Guided.default_config with compounds = true; term_limit = 2 }
            arena
        in
        Guided.observe state
          { id = 0; rule = Input (0, 0); clause = [ positive (P ("p", [ v 0 ])) ] };
        Guided.observe state
          {
            id = 1;
            rule = Input (1, 0);
            clause =
              [
                positive (D ((0, 0), [ v 0 ]));
                positive (P ("p", [ Fn (Skolem (0, 0), []) ]));
                positive (P ("p", [ Fn (Original "f", [ Fn (Original "f", [ v 0 ]) ]) ]));
              ];
          };
        Guided.pump ~is_live:(fun id -> id <> 0) state;
        equal (drain state) [] "search-only symbols or oversized terms entered Source";
        equal
          (state.metrics.stale, state.metrics.rejected_literals)
          (1, 3) "filter coverage missing" );
    ( "compound guidance preserves shared variables and quantifies parameters",
      fun () ->
        let arena =
          Source.create (Signature.make ~functions:[] ~predicates:[ ("p", 2); ("q", 1) ])
        in
        let state = Guided.create ~config:{ Guided.default_config with compounds = true } arena in
        Guided.observe state
          {
            id = 0;
            rule = Input (0, 0);
            clause = [ positive (P ("p", [ v 0; v 1 ])); negative (P ("q", [ v 2 ])) ];
          };
        let candidates = complete_guidance state in
        let f =
          Source.and_ arena
            [
              Source.pred arena "p" [ Source.free arena 0; Source.free arena 1 ];
              Source.not_ arena (Source.pred arena "q" [ Source.free arena 2 ]);
            ]
        in
        List.iter
          (fun expected ->
            check (List.mem expected candidates) "compound or quantified condition missing")
          [ f; Source.all arena [ 2 ] f; Source.ex arena [ 2 ] f ];
        List.iter
          (fun f ->
            check
              (Source.well_scoped arena ~depth:0 f && Source.size arena f <= 5)
              "ill-scoped or oversized guided formula")
          candidates );
    ( "guidance has a separate instance budget and contributes a checked proof",
      fun () ->
        let bounded =
          {
            config with
            max_size = 1;
            max_instances = 4;
            max_guided_instances = 4;
            engine = { config.engine with limits = { config.engine.limits with max_given = 300 } };
          }
        in
        let theory = Theory.create "naive" in
        let base = Scheduler.run bounded theory in
        check (base.certificate = None) "atomic exhaustive baseline unexpectedly refuted";
        let guided = Scheduler.run { bounded with guided = true } theory in
        let cert = Option.get guided.certificate in
        check (Result.is_ok (Kernel.check theory cert)) "guided proof did not replay";
        let worker = List.hd guided.workers in
        check (worker.guided_used > 0) "proof did not use guided instances";
        let stats = List.hd worker.schemas in
        check
          (stats.exhaustive_injected > 0 && stats.exhaustive_injected <= 4)
          "guidance consumed the exhaustive instance budget";
        check (stats.guided_injected > 0 && stats.guided_injected <= 4) "guided budget ignored";
        equal stats.injected
          (stats.exhaustive_injected + stats.guided_injected)
          "schema counts disagree" );
    ( "compound guidance retains the reference worker and UNKNOWN semantics",
      fun () ->
        let result =
          Scheduler.run
            {
              config with
              guided = true;
              guidance = { Guided.default_config with compounds = true };
              max_instances = 4;
              max_guided_instances = 4;
              reference = true;
              reference_config = { Reference.default_config with seconds = 2.; max_trials = 32 };
              engine = { config.engine with limits = { config.engine.limits with max_given = 40 } };
            }
            (Theory.create "zf")
        in
        check (result.certificate = None) "ZF was refuted by heuristic synthesis";
        equal (Option.get result.reference_report).trials 32
          "guided workload stopped the independent reference";
        List.iter
          (fun (s : Scheduler.schema_metrics) ->
            check (s.exhaustive_candidates > 0) "a schema was starved")
          (List.hd result.workers).schemas );
    ( "free-variable collection is read-only on a shared Source DAG",
      fun () ->
        let arena = Source.create Signature.sets in
        let atom = Source.member arena (Source.free arena 3) (Source.free arena 1) in
        let f =
          Source.and_ arena
            [ Source.all arena [ 1 ] atom; Source.ex arena [ 3 ] atom; Source.not_ arena atom ]
        in
        let counts = Source.counts arena in
        for _ = 1 to 100 do
          equal (Source.free_vars arena f) [ 1; 3 ] "free-variable set changed under a binder"
        done;
        equal (Source.counts arena) counts "reading free variables modified the arena" );
    ( "complementary support outranks unrelated FIFO proposals",
      fun () ->
        let arena =
          Source.create
            (Signature.make ~functions:[ ("f", 1); ("a", 0) ] ~predicates:[ ("p", 1); ("q", 1) ])
        in
        let steps =
          [
            [ positive (P ("q", [ v 0 ])) ];
            [ positive (P ("p", [ Fn (Original "f", [ v 0 ]) ])) ];
            [ negative (P ("p", [ Fn (Original "f", [ constant "a" ]) ])) ];
          ]
        in
        let exercise ranked =
          let state = Guided.create ~config:{ Guided.default_config with ranked } arena in
          List.iteri
            (fun id clause -> Guided.observe state { id; clause; rule = Input (id, 0) })
            steps;
          Guided.pump state;
          (state, Option.get (Guided.take state))
        in
        let state, first = exercise true in
        (match Source.view arena first with
        | Source.Pred ("p", _) -> ()
        | _ -> failwith "missing complementary priority");
        check (state.metrics.complementary > 0) "no structural evidence collected";
        let _, first = exercise false in
        match Source.view arena first with
        | Source.Pred ("q", _) -> ()
        | _ -> failwith "FIFO comparison changed" );
    ( "constrained synthesis instantiates residuals with shared and independent variables",
      fun () ->
        let arena =
          Source.create
            (Signature.make ~functions:[ ("f", 1) ] ~predicates:[ ("p", 1); ("q", 2); ("r", 1) ])
        in
        let state =
          Guided.create
            ~config:{ Guided.default_config with constraints = true; max_size = 7 }
            arena
        in
        let clauses =
          [
            [ positive (P ("p", [ v 0 ])); positive (P ("q", [ v 0; v 1 ])) ];
            [ negative (P ("p", [ Fn (Original "f", [ v 0 ]) ])); positive (P ("r", [ v 0 ])) ];
          ]
        in
        List.iteri
          (fun id clause -> Guided.observe state { id; clause; rule = Input (id, 0) })
          clauses;
        let candidates = complete_guidance state in
        let x = Source.free arena 0 and y = Source.free arena 1 in
        let missing =
          Source.not_ arena
            (Source.or_ arena
               [
                 Source.pred arena "r" [ x ];
                 Source.pred arena "q" [ Source.apply arena "f" [ x ]; y ];
               ])
        in
        check (List.mem missing candidates)
          "unifier did not construct the missing residual condition";
        check (state.metrics.constrained > 0) "constraint proposals not measured";
        List.iter
          (fun f -> check (Source.well_scoped arena ~depth:0 f) "constraint leaked a binder")
          candidates );
    ( "constraint matching enforces occurs checks, liveness and local work budgets",
      fun () ->
        let arena =
          Source.create (Signature.make ~functions:[ ("f", 1) ] ~predicates:[ ("p", 2) ])
        in
        let observe state id l =
          Guided.observe state { id; clause = [ l ]; rule = Input (id, 0) }
        in
        let state = Guided.create ~config:{ Guided.default_config with constraints = true } arena in
        observe state 0 (positive (P ("p", [ v 0; v 0 ])));
        observe state 1 (negative (P ("p", [ Fn (Original "f", [ v 0 ]); v 0 ])));
        ignore (complete_guidance state);
        equal state.metrics.complementary 0 "cyclic substitution was admitted";
        equal state.metrics.constrained 0 "failed constraints generated proposals";
        let state =
          Guided.create
            ~config:
              { Guided.default_config with constraints = true; match_steps = 1; match_limit = 1 }
            arena
        in
        observe state 0 (positive (P ("p", [ v 0; v 1 ])));
        observe state 1 (negative (P ("p", [ v 1; v 0 ])));
        Guided.pump state;
        equal
          (state.metrics.matches, state.metrics.exhausted_matches)
          (1, 1) "match work limit ignored";
        let state = Guided.create arena in
        observe state 0 (positive (P ("p", [ v 0; v 1 ])));
        Guided.pump state;
        observe state 1 (negative (P ("p", [ v 0; v 1 ])));
        Guided.pump ~is_live:(fun id -> id <> 0) state;
        equal state.metrics.matches 0 "retired evidence was still matched" );
    ( "history frequency and priority admission survive full candidate queues",
      fun () ->
        let arena =
          Source.create (Signature.make ~functions:[] ~predicates:[ ("p", 1); ("q", 1) ])
        in
        let state = Guided.create ~config:{ Guided.default_config with capacity = 2 } arena in
        Guided.observe state
          { id = 0; clause = [ positive (P ("q", [ v 0 ])) ]; rule = Input (0, 0) };
        Guided.pump state;
        let p = Pred ("p", [ F 0 ]) and np = Neg (Pred ("p", [ F 0 ])) in
        Guided.seed state [ p; np; np ];
        equal (Wire.export arena (Option.get (Guided.take state))) np "proof frequency ignored";
        check
          (state.metrics.replaced > 0 && Queue.length state.pending <= 2)
          "priority admission exceeded capacity";
        equal state.metrics.history_offered 1 "history attribution missing" );
    ( "verified proof history seeds useful instances without consuming exhaustive slots",
      fun () ->
        let theory, cert, _ = prove "naive" in
        let history = Guided.learn theory cert in
        check (history <> []) "no used schema conditions learned";
        check
          (rejects (fun () -> ignore (Guided.learn theory { cert with root = max_int })))
          "forged history accepted";
        let result =
          Scheduler.run ~history
            { config with guided = true; max_instances = 0; max_guided_instances = 4 }
            theory
        in
        check
          (Result.is_ok (Kernel.check theory (Option.get result.certificate)))
          "history did not lead to a verified proof";
        let worker = List.hd result.workers in
        check
          (worker.guidance.history_offered > 0 && worker.guided_used > 0)
          "history did not contribute";
        equal (List.hd worker.schemas).exhaustive_injected 0 "history consumed exhaustive budget" );
    ( "natural history ignores unused assumptions and transfers only Source patterns",
      fun () ->
        let module N = Natural_checker in
        let signature = Signature.make ~functions:[ ("c", 0) ] ~predicates:[ ("p", 1); ("q", 1) ] in
        let p = Pred ("p", [ App ("c", []) ]) and q = Pred ("q", [ App ("c", []) ]) in
        let theory =
          Theory.custom ~name:"history" signature [ ("p", p); ("np", Neg p); ("q", q) ]
        in
        let source i = Wire_types.Pair (Number 0, N.permission_code (FixedPermission i)) in
        let cert =
          Natural.certificate theory
            (N.certificate_code
               {
                 assumptions = List.init 3 source;
                 deduction = ImplicationElimination (Assume 1, Assume 0);
               })
        in
        let history = Guided.learn theory cert in
        check
          (List.mem p history && not (List.mem q history))
          "unused natural premise polluted history";
        let a = Source.create signature and b = Source.create signature in
        let run arena =
          let state = Guided.create arena in
          Guided.seed state history;
          List.map (Wire.export arena) (drain state)
        in
        equal (run a) (run b) "history depended on arena IDs";
        let state = Guided.create (Source.create (Signature.make ~functions:[] ~predicates:[])) in
        Guided.seed state history;
        equal (drain state) [] "foreign symbols entered a new theory" );
  ]

let () = run tests
