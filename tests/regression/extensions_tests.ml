open Axiom_fuzzer
open Test_support
open Wire

let take n s = List.of_seq (Seq.take n s)

let definition_fixture () =
  let signature =
    Signature.make ~functions:[ ("a", 0); ("f", 1) ] ~predicates:[ ("p", 1); ("r", 2) ]
  in
  let defs =
    Definitions.create signature |> fun d ->
    Definitions.function_ d ~name:"twice" ~arity:1 (App ("f", [ App ("f", [ F 0 ]) ])) |> fun d ->
    Definitions.predicate d ~name:"named" ~arity:1 (Pred ("p", [ App ("twice", [ F 0 ]) ]))
  in
  ( defs,
    Theory.of_definitions ~name:"defined" defs
      [
        ("positive", Pred ("named", [ App ("a", []) ]));
        ("negative", Neg (Pred ("p", [ App ("f", [ App ("f", [ App ("a", []) ]) ]) ])));
      ] )

let tests =
  [
    ( "mutation streams edit arbitrary formulas while preserving scope",
      fun () ->
        let f = All (Disj [ Pred ("p", [ B 0 ]); Ex (Eq (B 1, B 0)) ]) in
        let edits = List.of_seq (Mutation.mutations f) in
        check (List.length edits > 5) "no nested mutations";
        List.iter
          (fun e -> check (Wire.source_scoped ~closed:true e.Mutation.formula) "open mutant")
          edits;
        check (List.exists (fun e -> e.Mutation.path <> []) edits) "only root mutated";
        equal edits (List.of_seq (Mutation.mutations f)) "mutation order nondeterministic";
        equal (List.length edits)
          (List.length (List.sort_uniq compare (List.map (fun e -> e.Mutation.formula) edits)))
          "duplicate mutants";
        let wide = Conj (List.init 5000 (fun i -> Pred ("p" ^ string_of_int i, []))) in
        let before = Telemetry.allocated_words () in
        let first = take 1 (Mutation.mutations wide) in
        let allocated = Telemetry.allocated_words () -. before in
        check (allocated < 500000.) "unused wide mutations were eagerly allocated";
        equal (List.hd first).Mutation.formula (Neg wide) "wide mutation prefix changed" );
    ( "condition shrinking preserves nested binding and strictly decreases size",
      fun () ->
        let f = All (Ex (Pred ("r", [ B 1; B 0; F 1 ]))) in
        let candidates = List.of_seq (Mutation.shrinks f) in
        check
          (List.exists
             (fun e -> e.Mutation.formula = Ex (Pred ("r", [ F 0; B 0; F 1 ])))
             candidates)
          "removed binder captured an inner variable";
        List.iter
          (fun e ->
            check
              (Wire.source_scoped e.Mutation.formula && Mutation.size e.formula < Mutation.size f)
              "invalid shrink")
          candidates );
    ( "mutated refutations are checked against their own theory",
      fun () ->
        let t = Tptp.parse "fof(p,axiom,p(a))." in
        let snapshot = Mutation.snapshot ~observations:0 t in
        let mutant = List.hd (take 1 (Mutation.theories snapshot)) in
        let variant = Tptp.parse mutant.problem in
        equal (Theory.fixed t) snapshot "snapshot changed original theory";
        check
          ((Scheduler.run config variant).certificate = None)
          "negating a sole atom refuted a satisfiable theory";
        let t = Tptp.parse "fof(a,axiom,(p(a) | ~p(a)))." in
        let mutants = Mutation.theories (Mutation.snapshot t) |> take 12 in
        let found =
          List.find_map
            (fun m ->
              let v = Tptp.parse m.Mutation.problem in
              Option.map (fun c -> (v, c)) (Scheduler.run config v).certificate)
            mutants
        in
        let v, c = Option.get found in
        check (Result.is_ok (Kernel.check v c)) "mutant certificate rejected";
        check (Result.is_error (Kernel.check t c)) "mutant authorized under original theory" );
    ( "minimizer shrinks schema conditions while retaining a checked refutation",
      fun () ->
        let t = Theory.create "naive" in
        let a = Theory.arena t in
        let x = Source.free a 0 and y = Source.free a 1 in
        let atom = Source.not_ a (Source.member a x x) in
        let condition =
          Source.and_ a [ atom; Source.or_ a [ Source.eq a y y; Source.member a y x ] ]
        in
        let ax = Theory.instantiate t ~id:0 Comprehension condition in
        let e = Engine.create config.engine in
        Engine.add_axiom e ax;
        Engine.finish e;
        let original = Option.get (Engine.certificate e ~theory:(Theory.name t)) in
        let small = (Minimizer.run ~shrink_limit:64 ~config:config.engine t original).certificate in
        check (Result.is_ok (Kernel.check t small)) "condition shrink lost proof";
        let weight c =
          List.fold_left
            (fun n (a : axiom) ->
              match a.origin with Instance (_, f) -> n + Mutation.size f | _ -> n)
            0 c.axioms
        in
        check (weight small < weight original) "condition did not shrink" );
    ( "definitions expand acyclic functions and predicates into a base manifest",
      fun () ->
        let definitions, theory = definition_fixture () in
        equal
          (Signature.predicates (Definitions.base_signature definitions))
          [ ("p", 1); ("r", 2) ]
          "base signature changed";
        let result = Scheduler.run config theory in
        let c = Option.get result.certificate in
        check (Result.is_ok (Kernel.check theory c)) "expanded theory proof failed";
        let text = Tptp.problem (Theory.fixed theory) in
        let imported = Tptp.parse text in
        check
          (Result.is_ok (Kernel.check theory (Certificate_io.decode (Certificate_io.encode c))))
          "expanded certificate not portable";
        let imported_proof = Option.get (Scheduler.run config imported).certificate in
        check
          (Result.is_ok (Kernel.check imported imported_proof))
          "expanded TPTP theory lost the contradiction" );
    ( "definition substitution is simultaneous and avoids capture",
      fun () ->
        let base = Signature.make ~functions:[] ~predicates:[ ("r", 2) ] in
        let defs =
          Definitions.predicate (Definitions.create base) ~name:"d" ~arity:2
            (All (Conj [ Pred ("r", [ F 0; B 0 ]); Pred ("r", [ F 1; F 0 ]) ]))
        in
        equal
          (Definitions.expand defs (All (Pred ("d", [ B 0; F 0 ]))))
          (All (All (Conj [ Pred ("r", [ B 1; B 0 ]); Pred ("r", [ F 0; B 1 ]) ])))
          "definition expansion captured an argument or substituted twice" );
    ( "definitions reject recursion shadowing arity and oversized expansion",
      fun () ->
        let defs, _ = definition_fixture () in
        List.iter
          (fun f -> check (rejects f) "invalid definition accepted")
          [
            (fun () -> ignore (Definitions.predicate defs ~name:"p" ~arity:1 Top));
            (fun () ->
              ignore (Definitions.predicate defs ~name:"self" ~arity:0 (Pred ("self", []))));
            (fun () ->
              ignore (Definitions.predicate defs ~name:"bad" ~arity:1 (Pred ("p", [ F 1 ]))));
            (fun () -> ignore (Definitions.function_ defs ~name:"bad" ~arity:0 (B 0)));
            (fun () -> ignore (Definitions.expand defs (Pred ("named", []))));
            (fun () ->
              ignore (Definitions.expand ~budget:2 defs (Pred ("named", [ App ("a", []) ]))));
            (fun () -> ignore (Definitions.create Signature.unrestricted));
          ] );
    ( "proof collection preserves transitive retired ancestors and monotone IDs",
      fun () ->
        let p = Proof.create () in
        let clause = [ positive (P ("p", [])) ] in
        let a = Proof.add p clause (Input (0, 0)) in
        let b = Proof.add p clause (Factor (a.id, 0, 1, [])) in
        ignore (Proof.add p clause (Input (1, 0)));
        let c = Proof.add p clause (Factor (b.id, 0, 1, [])) in
        equal (Proof.reclaim p [ c.id ]) 1 "dead node not removed";
        equal (List.map (fun (s : step) -> s.id) (Proof.steps p)) [ 0; 1; 3 ] "ancestor lost";
        equal (Proof.add p clause (Factor (c.id, 0, 1, []))).id 4 "reclaimed ID reused" );
    ( "engine collection drops dead nodes caches and postings but preserves replay",
      fun () ->
        let t = Tptp.parse "fof(p,axiom,p(a)). fof(n,axiom,~p(a)). fof(junk,axiom,q(b))." in
        let e =
          Engine.create
            { config.engine with collect_every = 1; collect_adaptive = false; subsumption = false }
        in
        Engine.add_axiom e (List.nth (Theory.fixed t) 2);
        Engine.run_steps e 1;
        let retired = List.hd (Proof.steps e.proof) in
        Engine.retire e retired.id;
        let old = Term.of_wire e.terms (Fn (Original "b", [])) in
        Engine.collect e;
        equal (Proof.stored e.proof, Term.count e.terms) (0, 0) "dead storage retained";
        check (rejects (fun () -> ignore (Term.view e.terms old))) "stale term handle recycled";
        equal (Index.all e.index) [] "retired Active entry retained";
        List.iter (Engine.add_axiom e)
          (List.filter (fun (a : axiom) -> a.axiom_id < 2) (Theory.fixed t));
        Engine.finish e;
        let c = Option.get (Engine.certificate e ~theory:(Theory.name t)) in
        check (Result.is_ok (Kernel.check t c)) "reclaimed engine could not emit a portable proof";
        check (e.metrics.reclaimed_nodes > 0) "no collection accounting" );
    ( "automatic collection retains backward rewrite proof dependencies",
      fun () ->
        let t =
          Tptp.parse "fof(old,axiom,p(f(a))). fof(rule,axiom,(![X]:f(X)=X)). fof(n,axiom,~p(a))."
        in
        let cfg =
          {
            config.engine with
            collect_every = 1;
            collect_adaptive = false;
            ordered = true;
            demodulation = true;
            backward_demodulation = true;
            weight_ratio = 0;
          }
        in
        let e = Engine.create cfg in
        Engine.add_axiom e (List.nth (Theory.fixed t) 0);
        Engine.run_steps e 1;
        Engine.add_axiom e (List.nth (Theory.fixed t) 1);
        Engine.run_steps e 1;
        Engine.collect e;
        Engine.add_axiom e (List.nth (Theory.fixed t) 2);
        Engine.finish e;
        let c = Option.get (Engine.certificate e ~theory:(Theory.name t)) in
        check (List.exists (fun (s : step) -> s.id = 0) c.steps) "retired ancestor was reclaimed";
        check (Result.is_ok (Kernel.check t c)) "reclaimed backward rewrite proof rejected" );
    ( "adaptive collection at every point agrees with full collection and checks",
      fun () ->
        (* Production interleaving: with collect_every = 1 every inference batch
           is a collection point; the adaptive path runs only the scheduling
           collectors at most of them and the memory sweep at some. AVATAR
           splits both disjunctions and the ground clauses go to the ground
           Boolean solver. *)
        let t =
          Tptp.parse
            "fof(c1,axiom,((![X]:p(X)) | (![Y]:q(Y)))). fof(c2,axiom,((![X]:r(X)) | (![Y]:s(Y)))). \
             fof(n1,axiom,(~p(a) | ~r(b))). fof(n2,axiom,(~p(a) | ~s(b))). fof(n3,axiom,(~q(a) | \
             ~r(b))). fof(n4,axiom,(~q(a) | ~s(b))). fof(e1,axiom,(![X]:(f(f(X))=X))). \
             fof(e2,axiom,(![X]:(t(X) => t(f(X))))). fof(e3,axiom,t(c))."
        in
        let run ~avatar adaptive =
          let points = ref 0 in
          let e =
            Engine.create
              ~on_collect:(fun _ -> incr points)
              { config.engine with collect_every = 1; collect_adaptive = adaptive }
          in
          (* As in the AVATAR engine tests: without the ground Boolean solver
             the ground clash must close through the conditional AVATAR path. *)
          if avatar then Ground_boolean.release e.ground_boolean;
          List.iter (Engine.add_axiom e) (Theory.fixed t);
          Engine.finish e;
          let c = Option.get (Engine.certificate e ~theory:(Theory.name t)) in
          check (Result.is_ok (Kernel.check t c)) "collected engine emitted a rejected proof";
          (!points, e.metrics.collections, c.avatar <> None)
        in
        List.iter
          (fun avatar ->
            let points, sweeps, closed = run ~avatar true in
            Printf.printf
              "    adaptive (avatar=%b): %d points, %d sweeps, AVATAR certificate %b\n%!" avatar
              points sweeps closed;
            check (sweeps >= 1) "adaptive run never swept";
            check (points > sweeps) "adaptive run never took the scheduling-only path";
            let legacy_points, legacy_sweeps, _ = run ~avatar false in
            equal legacy_points legacy_sweeps "legacy collection skipped a sweep";
            check (legacy_points >= 1) "legacy run never collected")
          [ false; true ] );
    ( "indexed primitive replay agrees with list replay including invalid suffixes",
      fun () ->
        let module R = Rocq_checker in
        let p = [ (true, R.Pred (0, [])) ] and n = [ (false, R.Pred (0, [])) ] in
        let prefix = [ (R.Input 0, p); (R.Input 1, n) ] in
        for count = 0 to 120 do
          let copies = List.init count (fun i -> (R.Copy (if i = 0 then 0 else i + 1), p)) in
          let last = if count = 0 then 0 else count + 1 in
          let good = prefix @ copies @ [ (R.Resolve (last, 0, 1, 0), []) ] in
          check (R.check [ p; n ] good) "indexed valid replay rejected";
          List.iter
            (fun proof ->
              equal (R.check [ p; n ] proof) (R.check_list [ p; n ] proof) "indexed/list mismatch")
            [
              good;
              prefix @ copies;
              good @ [ (R.Copy (count + 3), []) ];
              good @ [ (R.Input 99, []) ];
              (R.Input 0, []) :: good;
            ]
        done;
        let xs = List.init 1024 Fun.id in
        let lookup = R.cached xs in
        for i = 0 to 1030 do
          equal (lookup i) (List.nth_opt xs i) "cached input index differs"
        done );
    ( "linear Source identity agrees with the normalization comparison",
      fun () ->
        let module S = Source_checker in
        let f = Conj (List.init 256 (fun i -> Pred (string_of_int i, [ F 0; F 1 ]))) in
        let variants =
          [
            f;
            Conj (List.rev (match f with Conj fs -> fs | _ -> []));
            Conj [ Top; f; f ];
            Neg (Neg f);
            Conj [ f; Bot ];
          ]
        in
        List.iter
          (fun g ->
            equal (S.equivalent f g)
              (S.formula_equal (S.simplify f) (S.simplify g))
              "identity shortcut changed authorization")
          variants );
  ]

let () =
  match Array.to_list Sys.argv with
  | [ _; "--export-rocq"; path ] ->
      let _, t = definition_fixture () in
      let c = Option.get (Scheduler.run config t).certificate in
      Sexp.write_file path (Result.get_ok (Kernel.rocq_document t c))
  | _ -> run tests
