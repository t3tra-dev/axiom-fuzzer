open Axiom_fuzzer
open Test_support
open Wire

let tests =
  [
    ( "replacement image is needed for a refutation",
      fun () ->
        let zf = Theory.create "zf" in
        let a = Theory.arena zf in
        let phi = Source.eq a (Source.free a 1) (Source.free a 2) in
        let replacement = Theory.instantiate zf ~id:20 Replacement phi in
        let formulas =
          [
            ("replacement", replacement.formula);
            ("universal-membership", All (All (Pred ("member", [ B 1; B 0 ]))));
            ("two-elements", Ex (Ex (Neg (Eq (B 1, B 0)))));
          ]
        in
        let t = Theory.custom ~name:"replacement-regression" Signature.sets formulas in
        let run formulas =
          let theory = Theory.custom ~name:"replacement-regression" Signature.sets formulas in
          Scheduler.run
            {
              config with
              engine =
                {
                  config.engine with
                  ordered = true;
                  demodulation = true;
                  limits =
                    {
                      config.engine.limits with
                      max_given = 500;
                      max_generated = 15000;
                      max_retained = 12000;
                    };
                };
            }
            theory
        in
        let r = run formulas in
        let c = Option.get r.certificate in
        equal
          (List.map (fun (a : axiom) -> a.name) c.axioms)
          [ "replacement"; "universal-membership"; "two-elements" ]
          "replacement missing from proof core";
        check (Result.is_ok (Kernel.check t c)) "replacement refutation failed replay";
        check
          (List.for_all (fun (_, f) -> sets_model (fun _ _ -> true) f) (List.tl formulas))
          "missing finite witness without replacement" );
    ( "separation and replacement cooperate in a refutation",
      fun () ->
        let zf = Theory.create "zf" in
        let a = Theory.arena zf in
        let v i = Source.free a i in
        let empty =
          Source.ex a [ 1 ] (Source.all a [ 0 ] (Source.not_ a (Source.member a (v 0) (v 1))))
        in
        let singleton =
          Source.ex a [ 1; 2 ]
            (Source.all a [ 0 ]
               (Source.iff a (Source.member a (v 0) (v 2)) (Source.eq a (v 0) (v 1))))
        in
        let sep = Theory.instantiate zf ~id:20 Separation (Source.falsity a) in
        let repl = Theory.instantiate zf ~id:21 Replacement (Source.eq a (v 1) (v 2)) in
        let formulas =
          [
            ("separation", sep.formula);
            ("replacement", repl.formula);
            ("nonempty", Ex (Ex (Pred ("member", [ B 0; B 1 ]))));
            ( "no-empty-and-singleton",
              Wire.export a (Source.not_ a (Source.and_ a [ empty; singleton ])) );
          ]
        in
        let t = Theory.custom ~name:"schema-interaction" Signature.sets formulas in
        let without name = List.filter (fun (n, _) -> n <> name) formulas in
        check
          (List.for_all (fun (_, f) -> sets_model (fun _ set -> set = 1) f) (without "replacement"))
          "replacement-free fragment lacks its finite witness";
        check
          (List.for_all (fun (_, f) -> sets_model (fun x set -> x = set) f) (without "separation"))
          "separation-free fragment lacks its finite witness";
        let r =
          Scheduler.run
            {
              config with
              engine =
                {
                  config.engine with
                  ordered = true;
                  demodulation = true;
                  limits =
                    {
                      config.engine.limits with
                      max_given = 1000;
                      max_generated = 30000;
                      max_retained = 25000;
                    };
                };
            }
            t
        in
        let c = Option.get r.certificate in
        check
          (List.for_all
             (fun name -> List.exists (fun (a : axiom) -> a.name = name) c.axioms)
             [ "separation"; "replacement" ])
          "one schema not used";
        check (Result.is_ok (Kernel.check t c)) "schema interaction proof failed replay" );
    ( "ordered equality factoring has a checked proof rule",
      fun () ->
        let t = Tptp.parse "fof(c,axiom,(c=a | c=b)). fof(n,axiom,a=b). fof(m,axiom,c!=a)." in
        (* Keep resolution contraction from bypassing the rule under test. *)
        let r =
          Scheduler.run
            { config with engine = { config.engine with ordered = true; subsumption = false } }
            t
        in
        let c = Option.get r.certificate in
        check
          (List.exists
             (fun (s : step) -> match s.rule with Equality_factor _ -> true | _ -> false)
             c.steps)
          "equality factoring was not exercised";
        check (Result.is_ok (Kernel.check t c)) "equality factoring replay failed";
        equal
          (Certificate_io.decode (Certificate_io.encode c))
          c "equality factoring serialization lost data";
        let bad =
          {
            c with
            steps =
              List.map
                (fun (s : step) ->
                  match s.rule with
                  | Equality_factor (p, i, r, j, q, sigma) ->
                      { s with rule = Equality_factor (p, i, not r, j, q, sigma) }
                  | _ -> s)
                c.steps;
          }
        in
        check
          (Result.is_error (Kernel.check t bad))
          "forged equality factoring orientation accepted" );
    ( "demodulation records every rewrite in the proof",
      fun () ->
        let t =
          Tptp.parse "fof(eq,axiom,(![X]:f(X)=X)). fof(p,axiom,p(f(f(a)))). fof(n,axiom,~p(a))."
        in
        let r =
          Scheduler.run
            { config with engine = { config.engine with ordered = true; demodulation = true } }
            t
        in
        let c = Option.get r.certificate in
        check (r.engine.metrics.demodulated >= 2) "nested rewriting not exercised";
        check (Result.is_ok (Kernel.check t c)) "rewrite provenance failed replay";
        check
          (List.length
             (List.filter
                (fun (s : step) -> match s.rule with Paramodulate _ -> true | _ -> false)
                c.steps)
          >= 2)
          "rewrite proof missing" );
    ( "backward subsumption keeps retired proof ancestors",
      fun () ->
        let t = Tptp.parse "fof(c,axiom,(p | q)). fof(n,axiom,~p). fof(m,axiom,~q)." in
        let engine = Engine.create { config.engine with backward_subsumption = true } in
        let axioms = Theory.fixed t in
        Engine.add_axiom engine (List.nth axioms 0);
        select_given engine 0;
        Engine.add_axiom engine (List.nth axioms 1);
        Engine.finish engine;
        check (engine.metrics.backward_subsumed > 0) "no clause was retired";
        Engine.collect engine;
        Engine.add_axiom engine (List.nth axioms 2);
        Engine.finish engine;
        let c = Option.get (Engine.certificate engine ~theory:(Theory.name t)) in
        check
          (List.exists
             (fun (s : step) -> s.clause <> [] && not (Index.mem engine.retained_index s.id))
             c.steps)
          "proof did not retain retired ancestors";
        check (Result.is_ok (Kernel.check t c)) "retired ancestor lost during replay" );
    ( "definitional CNF avoids exponential distribution",
      fun () ->
        let big = List.init 14 (fun i -> Printf.sprintf "(p%d & q%d)" i i) |> String.concat " | " in
        let t = Tptp.parse ("fof(big,axiom,(" ^ big ^ ")). fof(r,axiom,r). fof(n,axiom,~r).") in
        let ax = List.hd (Theory.fixed t) in
        let cs = Clausify.run ax in
        check (List.length cs < 100) "CNF still distributes exponentially";
        equal cs (Kernel.input_clauses ax) "hybrid CNF differs from kernel";
        check
          (try
             ignore (Clausify.run ~mode:Distributive ax);
             false
           with Clausify.Limit -> true)
          "distribution reproduction disappeared";
        let r = Scheduler.run config t in
        check (Option.is_some r.certificate) "large irrelevant axiom blocks contradiction";
        check (Result.is_ok (Kernel.check t (Option.get r.certificate))) "large input replay failed"
    );
    ( "auxiliary predicates are checked and cannot enter Source",
      fun () ->
        let t = Tptp.parse "fof(b,axiom,(p & q)). fof(n,axiom,~p). fof(named,axiom,def_0_0)." in
        let r =
          Scheduler.run { config with engine = { config.engine with cnf_mode = Definitional } } t
        in
        let c = Option.get r.certificate in
        check
          (List.exists
             (fun (s : step) ->
               List.exists (fun l -> match l.atom with D _ -> true | _ -> false) s.clause)
             c.steps)
          "proof does not use a definition";
        equal (Certificate_io.decode (Certificate_io.encode c)) c "definition lost in certificate";
        check (Result.is_ok (Kernel.check t c)) "definition proof rejected";
        check
          (Result.is_error (Kernel.check t { c with cnf_mode = Distributive }))
          "wrong CNF mode accepted";
        let forged =
          {
            c with
            steps =
              List.map
                (fun (s : step) ->
                  {
                    s with
                    clause =
                      List.map
                        (fun l ->
                          match l.atom with
                          | D (_, ts) -> { l with atom = D ((999, 0), ts) }
                          | _ -> l)
                        s.clause;
                  })
                c.steps;
          }
        in
        check (Result.is_error (Kernel.check t forged)) "unregistered definition accepted";
        let only_def =
          { id = 0; rule = Input (0, 0); clause = [ positive (D ((0, 0), [ v 0 ])) ] }
        in
        equal (Guided.candidates (Theory.arena t) [ only_def ]) [] "definition leaked into Source";
        let imported = Tptp.parse (Tptp.cnf_problem ~mode:Definitional (Theory.fixed t)) in
        check
          (Option.is_some (Scheduler.run config imported).certificate)
          "CNF export lost auxiliary identity";
        let satisfiable = Tptp.parse "fof(b,axiom,(p & q)). fof(n,axiom,~def_0_0)." in
        let exported =
          Tptp.parse (Tptp.cnf_problem ~mode:Definitional (Theory.fixed satisfiable))
        in
        check
          ((Scheduler.run config exported).certificate = None)
          "export captured an original predicate" );
    ( "Russell is synthesized and factored",
      fun () ->
        let t, c, r = prove "naive" in
        check
          (List.exists
             (fun (a : axiom) ->
               match a.origin with
               | Instance (Comprehension, Neg (Pred ("member", [ F 0; F 0 ]))) -> true
               | _ -> false)
             c.axioms)
          "Russell predicate not discovered";
        check
          (List.exists
             (fun (s : step) -> match s.rule with Factor _ -> true | _ -> false)
             c.steps)
          "factoring unused";
        check (List.length c.steps = 5 && List.length c.axioms = 1) "unexpected Russell proof size";
        check (List.length r.traces > 1) "candidate enumeration bypassed";
        check (Result.is_ok (Kernel.check t c)) "kernel rejected" );
    ( "separation with universal set",
      fun () ->
        let t, c, _ = prove "separation-universal" in
        check
          (List.exists (fun (a : axiom) -> a.origin = Fixed "universal") c.axioms)
          "universal assumption missing";
        check (Result.is_ok (Kernel.check t c)) "separation proof failed replay" );
    ( "foundation requires pairing and self-member",
      fun () ->
        let _, c, _ = prove "foundation-self" in
        equal
          (List.map (fun (a : axiom) -> a.name) c.axioms)
          [ "pairing"; "foundation"; "self-member" ]
          "foundation core incorrect";
        check
          (List.exists
             (fun (s : step) -> match s.rule with Paramodulate _ -> true | _ -> false)
             c.steps)
          "equality inference unused" );
    ( "mutated separation identifies the mutation",
      fun () ->
        let _, c, _ = prove "mutated-separation" in
        check
          (List.for_all
             (fun (a : axiom) ->
               match a.origin with Instance (Unrestricted_separation, _) -> true | _ -> false)
             c.axioms)
          "mutation provenance missing" );
    ( "correct finite fragment is UNKNOWN",
      fun () ->
        let t = Theory.create "separation" in
        let r =
          Scheduler.run
            {
              config with
              max_instances = 5;
              engine = { config.engine with limits = { config.engine.limits with max_given = 40 } };
            }
            t
        in
        check (r.certificate = None) "correct fragment reported inconsistent";
        check (r.reason <> "") "UNKNOWN reason absent" );
    ( "bounded ZF is UNKNOWN",
      fun () ->
        let r =
          Scheduler.run
            {
              config with
              max_instances = 2;
              engine =
                {
                  config.engine with
                  limits = { config.engine.limits with max_given = 5; max_generated = 500 };
                };
            }
            (Theory.create "zf")
        in
        check (r.certificate = None) "ZF reported inconsistent" );
    ( "paramodulation under function symbols",
      fun () ->
        let t = Tptp.parse "fof(eq,axiom,(a=b)). fof(p,axiom,p(f(a))). fof(n,axiom,~p(f(b)))." in
        let r = Scheduler.run config t in
        check (Option.is_some r.certificate) "congruence contradiction missed";
        check (Result.is_ok (Kernel.check t (Option.get r.certificate))) "equality replay failed" );
    ( "parameterized comprehension preserves Skolem dependencies",
      fun () ->
        let t = Theory.create "naive" in
        let a = Theory.arena t in
        let phi = Source.member a (Source.free a 0) (Source.free a 1) in
        let ax = Theory.instantiate t ~id:0 Comprehension phi in
        check (Theory.validate_axiom t ax) "parameterized schema invalid";
        check (Clausify.run ax = Kernel.input_clauses ax) "parameterized Skolem dependency mismatch"
    );
    ( "zero budgets return UNKNOWN",
      fun () ->
        let r =
          Scheduler.run
            {
              config with
              engine =
                { config.engine with limits = { config.engine.limits with max_generated = 0 } };
            }
            (Theory.create "naive")
        in
        check
          (r.certificate = None && r.engine.metrics.retained = 0)
          "zero generation budget ignored" );
    ( "independent Domains produce replayable proofs",
      fun () ->
        let r = Scheduler.portfolio ~workers:3 config (fun () -> Theory.create "naive") in
        check (Option.is_some r.certificate) "portfolio missed Russell";
        check
          (Result.is_ok (Kernel.check (Theory.create "naive") (Option.get r.certificate)))
          "portfolio proof corrupted";
        equal (List.length r.workers) 3 "portfolio metrics lost a worker";
        List.iter
          (fun (w : Scheduler.worker_metrics) ->
            check
              (w.engine.finished <> None && w.engine.metrics.memory_samples > 0)
              "worker final sample missing";
            check (Engine.elapsed w.engine <= r.wall_seconds) "worker time includes join wait")
          r.workers );
    ( "metrics survive limits and exclude replay",
      fun () ->
        List.iter
          (fun name ->
            let r =
              Scheduler.run
                {
                  config with
                  max_instances = 2;
                  engine =
                    { config.engine with limits = { config.engine.limits with max_given = 1 } };
                }
                (Theory.create name)
            in
            let m = r.engine.metrics in
            check (m.memory_samples > 0 && m.allocated_words >= 0.) "final memory sample absent";
            equal m.redundant
              (m.tautologies + m.duplicates + m.variants + m.subsumed)
              "redundancy counts disagree";
            let elapsed = Engine.elapsed r.engine in
            ignore (Metrics_csv.summary ~output_seconds:0. r);
            equal (Engine.elapsed r.engine) elapsed "elapsed was not frozen";
            let injected =
              List.fold_left
                (fun n (w : Scheduler.worker_metrics) ->
                  n
                  + List.fold_left
                      (fun n (s : Scheduler.schema_metrics) -> n + s.injected)
                      0 w.schemas)
                0 r.workers
            in
            equal injected (List.length r.traces) "instance coverage differs from injected trace")
          [ "naive"; "zf" ] );
    ( "minimization and certificate roundtrip",
      fun () ->
        let t, c, _ = prove "separation-universal" in
        let decoded = Certificate_io.decode (Certificate_io.encode c) in
        equal decoded c "serialization lost information";
        let m = Minimizer.run ~config:config.engine t c in
        check (Result.is_ok (Kernel.check t m.certificate)) "minimizer produced invalid proof";
        equal (List.length m.certificate.axioms) 2 "required axiom dropped" );
  ]

let () = run tests
