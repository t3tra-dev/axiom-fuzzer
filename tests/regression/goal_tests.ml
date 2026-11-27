open Axiom_fuzzer
open Test_support
open Wire

let settings =
  {
    Engine.default_config with
    avatar = false;
    subsumption = false;
    demodulation = false;
    backward_demodulation = false;
    collect_every = 0;
    limits = { Engine.seconds = 5.; max_given = 2000; max_generated = 30000; max_retained = 30000 };
  }

let prepare text =
  let theory = Tptp.parse text in
  let engine = Engine.create settings in
  List.iter (Engine.add_axiom engine) (Theory.fixed theory);
  (theory, engine)

let advance ?(attempts = 16) (e : Engine.t) =
  Engine.protect (fun () ->
      Goal.advance ~attempts e.Engine.goals
        ~guard:(fun () -> Engine.check_time e)
        ~blocked:(Avatar.blocked e.avatar ~guard:(fun () -> ()))
        ~alive:(Engine.current_ticket e) ~record:(Engine.record e) ~emit:(Engine.emit e)
        ~redundant:(fun parents clause ->
          let support =
            List.concat_map (Avatar.dependency e.avatar) parents |> List.sort_uniq compare
          in
          Avatar.duplicate e.avatar ~guard:(fun () -> ()) ~variants:true ~except:(-1) support clause)
        ~demand:e.on_demand)

let run ?(slices = 1000) e =
  for _ = 1 to slices do
    if e.Engine.root = None && e.stopped = None && Goal.has_work e.goals then advance e
  done

let checked theory e =
  check (e.Engine.stopped = None) "goal search exhausted engine budget";
  equal e.metrics.given 0 "fixture used ordinary saturation";
  Engine.collect e;
  let cert =
    match Engine.certificate e ~theory:(Theory.name theory) with
    | Some cert -> cert
    | None -> failwith "goal search did not refute the fixture"
  in
  (match Kernel.check theory cert with Ok _ -> () | Error error -> failwith error);
  cert

let growth =
  "cnf(goal,axiom,~p(a)). cnf(rule,axiom,(p(X)|~q(X)|~r(X))). cnf(choice,axiom,(q(a)|s(a))). \
   cnf(r,axiom,r(a)). cnf(ns,axiom,~s(a))."

let equality =
  "cnf(goal,axiom,~p(f(a))). cnf(eq,axiom,(a=b|r)). cnf(rule,axiom,(p(f(b))|s)). cnf(nr,axiom,~r). \
   cnf(ns,axiom,~s)."

let cube ?(arity = 3) prefix =
  List.init (1 lsl arity) (fun i ->
      let literals =
        List.init arity (fun bit ->
            (if i land (1 lsl bit) = 0 then "" else "~") ^ prefix ^ string_of_int bit ^ "(X)")
      in
      Printf.sprintf "cnf(c%d,axiom,(%s))." i (String.concat "|" literals))
  |> String.concat " "

let conditional () =
  let theory =
    Tptp.parse
      "cnf(choice,axiom,(p(a)|escape)). cnf(rule,axiom,(~p(X)|~q(X)|~r(X))). \
       cnf(q,axiom,(q(a)|s)). cnf(ns,axiom,~s). cnf(r,axiom,r(a)). cnf(ne,axiom,~escape)."
  in
  let e = Engine.create settings in
  let axioms = Theory.fixed theory in
  Engine.add_axiom e (List.hd axioms);
  Avatar.offer_split e.avatar ~guard:(fun () -> ()) (Proof.get e.proof 0);
  Engine.split_step e e.avatar;
  e.avatar.model <- Array.make (Tbl.Int.length e.avatar.components) true;
  Tbl.Int.to_seq e.avatar.components
  |> List.of_seq
  |> List.iter (fun (id, (c : Avatar.component)) ->
      Engine.protect (fun () ->
          match c.node with
          | Some node -> Engine.admit e (Proof.get e.proof node)
          | None -> Engine.emit e c.clause (Component id)));
  List.iteri (fun i a -> if i > 0 && i < 5 then Engine.add_axiom e a) axioms;
  (theory, e, List.nth axioms 5)

let conditional_refutation () =
  let theory, e, last = conditional () in
  run ~slices:300 e;
  Engine.protect (fun () -> Engine.synchronize e);
  Engine.add_axiom e last;
  for _ = 1 to 300 do
    Engine.protect (fun () -> Engine.synchronize e);
    if e.root = None then advance e
  done;
  (theory, e)

let promoted_refutation () =
  let theory =
    Tptp.parse
      "cnf(a,axiom,(p(a)|q(a))). cnf(b,axiom,~q(a)). cnf(link,axiom,(~p(a)|r)). \
       cnf(close,axiom,~r)."
  in
  let e = Engine.create settings in
  let axioms = Theory.fixed theory in
  List.iteri (fun i a -> if i < 3 then Engine.add_axiom e a) axioms;
  run ~slices:80 e;
  check (e.goals.metrics.promoted > 0) "connected lemma never reached ordinary search";
  let has_p =
    Index.all e.retained_index
    |> List.exists (fun (s : step) ->
        s.clause = [ { positive = true; atom = P ("p", [ Fn (Original "a", []) ]) } ])
  in
  check has_p "promoted unit was not retained";
  Engine.collect e;
  Engine.add_axiom e (List.nth axioms 3);
  run e;
  (theory, e)

let first_refutation () =
  let theory = Tptp.parse "cnf(eq,axiom,f(X,Y)=g(X)). cnf(n,axiom,f(a,b)!=f(a,c))." in
  let e = Engine.create settings in
  let axioms = Theory.fixed theory in
  Engine.add_axiom e (List.hd axioms);
  run ~slices:100 e;
  check
    (Tbl.Int.fold
       (fun _ (s : Goal.state) found ->
         found
         || match s.proof.step.rule with Paramodulate (p, _, _, q, _, _, _) -> p = q | _ -> false)
       e.goals.states false)
    "an unopposed equation received no self-inference trial";
  Engine.add_axiom e (List.nth axioms 1);
  run e;
  (theory, e)

let tests =
  [
    ( "an initially unopposed equation supports a later checked refutation",
      fun () ->
        let theory, e = first_refutation () in
        ignore (checked theory e) );
    ( "all retained premises receive a first trial under continuing arrivals",
      fun () ->
        let t = Goal.create () in
        let note id =
          Goal.note t
            ~guard:(fun () -> ())
            ~support:[] (id, 0)
            {
              id;
              clause = [ { positive = true; atom = P ("unopposed" ^ string_of_int id, []) } ];
              rule = Input (id, 0);
            }
        in
        for i = 0 to 39 do
          note i
        done;
        for i = 40 to 439 do
          note i;
          Goal.advance ~attempts:1 t
            ~guard:(fun () -> ())
            ~alive:(fun _ -> true)
            ~record:(fun _ _ -> assert false)
            ~emit:(fun _ _ -> assert false)
            ~redundant:(fun _ _ -> false)
            ~demand:(fun ~guard:_ _ -> ())
        done;
        for i = 0 to 39 do
          check (Tbl.Int.find t.states i).started "an old positive premise was never tried"
        done;
        equal t.metrics.widened 0 "initial trials triggered unbounded positive expansion" );
    ( "residual inference requests real retained premises and rejects stale requests",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(g,axiom,(~p(a)|~q(a))). cnf(p0,axiom,p(b)). cnf(q0,axiom,q(c)). \
             cnf(p,axiom,p(a)). cnf(q,axiom,q(a))."
        in
        let e = Engine.create settings in
        let axioms = Theory.fixed theory in
        List.iteri (fun i a -> if i < 3 then Engine.add_axiom e a) axioms;
        let step () =
          Engine.protect (fun () ->
              Goal.advance e.goals
                ~guard:(fun () -> Engine.check_time e)
                ~alive:(Engine.current_ticket e) ~record:(Engine.record e) ~emit:(Engine.emit e)
                ~redundant:(fun _ _ -> false)
                ~use:(Engine.request_premises e) ~demand:e.on_demand)
        in
        for _ = 1 to 60 do
          step ()
        done;
        equal e.directions.demand_requests 0 "incompatible constants created a demand";
        Engine.add_axiom e (List.nth axioms 3);
        for _ = 1 to 80 do
          step ()
        done;
        check
          (Queue.to_seq e.directions.requested |> Seq.exists (fun (parent, _) -> parent = 3))
          "a successful residual step did not select its retained premise";
        let old = Proof.get e.proof 3 in
        Engine.deactivate e 3;
        let seen = ref [] in
        while not (Queue.is_empty e.directions.requested) do
          Option.iter
            (fun (id, _) -> seen := id :: !seen)
            (Directions.demanded e.directions ~alive:(Engine.current_ticket e))
        done;
        check (not (List.mem 3 !seen)) "a retired premise retained its demand ticket";
        Engine.admit e old;
        Engine.add_axiom e (List.nth axioms 4);
        run e;
        ignore (checked theory e) );
    ( "a delta continuation does not retry unchanged partners",
      fun () ->
        let t = Goal.create () in
        let note id clause =
          Goal.note t
            ~guard:(fun () -> ())
            ~support:[] (id, 0)
            { id; clause = Clause.normalize clause; rule = Input (id, 0) }
        in
        let p x = { positive = true; atom = P ("p", [ x ]) } in
        note 0 [ { (p (V (0, 0))) with positive = false } ];
        note 1 [ p (Fn (Original "a", [])) ];
        let proof = (Tbl.Int.find t.states 0).proof and epoch = t.epoch in
        let run since =
          let count = ref 0 in
          fst (Goal.cursor ~since t ~guard:(fun () -> ()) ~alive:(fun _ -> true) proof)
          |> Seq.iter (fun (_, f) -> f (fun _ _ -> incr count));
          !count
        in
        check (run 0 > 0) "fixture had no inference";
        equal (run epoch) 0 "unchanged partners were rescanned";
        note 2 [ p (Fn (Original "b", [])) ];
        equal (run epoch) 1 "new partner was missed or old work replayed" );
    ( "useful partial derivations survive cache pressure without permanent pinning",
      fun () ->
        let t = Goal.create () in
        let add id =
          let clause = [ { positive = false; atom = P ("g" ^ string_of_int (-id), []) } ] in
          let proof : Goal.recipe =
            {
              step = { id; clause; rule = Input (0, 0) };
              raw = clause;
              parents = [];
              leaves = [ (0, 0) ];
              support = [];
              height = 1;
            }
          in
          Goal.add_state t ~guard:(fun () -> ()) ~owner:(0, 0) ~depth:4 ~weight:100 proof
        in
        let valuable = add (-1) in
        valuable.credit <- 16;
        for i = 2 to 512 do
          ignore (add (-i))
        done;
        (* Force a merit-based replacement, followed eventually by the age slot. *)
        t.metrics.evicted <- 1;
        ignore (add (-513));
        check (Tbl.Int.mem t.states (-1)) "useful continuation was evicted first";
        for i = 514 to 518 do
          ignore (add (-i))
        done;
        check (Tbl.Clause_ints.length t.memo <= 512) "merit protection exceeded the cache bound";
        check (not (Tbl.Int.mem t.states (-1))) "old work became permanently pinned" );
    ( "promotion rejects recipes after a premise generation expires",
      fun () ->
        let _, e = prepare "cnf(g,axiom,(~p(X)|~q(X)|~r(X))). cnf(p,axiom,p(a))." in
        run ~slices:40 e;
        let partial =
          Tbl.Int.to_seq_values e.goals.states
          |> List.of_seq
          |> List.find (fun (s : Goal.state) -> s.proof.height > 0 && not s.promoted)
        in
        partial.connections <- 8;
        let leaf = List.find (fun (id, _) -> id <> fst partial.owner) partial.proof.leaves in
        Engine.deactivate e (fst leaf);
        let before = e.metrics.generated in
        Goal.promote e.goals
          ~guard:(fun () -> ())
          ~alive:(Engine.current_ticket e)
          ~blocked:(fun _ -> false)
          ~redundant:(fun _ _ -> false)
          ~record:(Engine.record e) ~emit:(Engine.emit e);
        equal e.metrics.generated before "stale recipe was exported";
        check (e.goals.metrics.promotion_stale > 0) "expired premise was not diagnosed" );
    ( "equality receives an attempt before a large resolution stream finishes",
      fun () ->
        let t = Goal.create () in
        let note id clause =
          let step = { id; clause = Clause.normalize clause; rule = Input (id, 0) } in
          Goal.note t ~guard:(fun () -> ()) ~support:[] (id, 0) step
        in
        let a = Fn (Original "a", []) and b = Fn (Original "b", []) in
        let fa = Fn (Original "f", [ a ]) in
        note 0 [ { positive = false; atom = P ("p", [ fa ]) } ];
        for i = 1 to 100 do
          note i
            [
              { positive = true; atom = P ("p", [ fa ]) };
              { positive = true; atom = P ("r" ^ string_of_int i, []) };
            ]
        done;
        note 101 [ { positive = true; atom = E (fa, b) } ];
        let proof = (Tbl.Int.find t.states 0).proof and first_equality = ref None in
        fst (Goal.cursor t ~guard:(fun () -> ()) ~alive:(fun _ -> true) proof)
        |> Seq.take 16
        |> Seq.iter (fun (_, attempt) ->
            attempt (fun _ rule ->
                match rule with
                | Paramodulate _ when !first_equality = None ->
                    first_equality := Some t.metrics.resolution_attempts
                | _ -> ()));
        check
          (Option.fold ~none:false ~some:(fun n -> n < 8) !first_equality)
          "resolution fanout starved equality" );
    ( "a connected partial lemma is promoted with its real proof and survives collection",
      fun () ->
        let theory, e = promoted_refutation () in
        ignore (checked theory e) );
    ( "late non-unit equalities resume parked roots without a retained target index",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(g,axiom,~p(f(a))). cnf(p,axiom,(p(f(b))|s)). cnf(ns,axiom,~s). \
             cnf(e,axiom,(a=b|r)). cnf(nr,axiom,~r)."
        in
        let e = Engine.create settings in
        let axioms = Theory.fixed theory in
        List.iteri (fun i a -> if i < 3 then Engine.add_axiom e a) axioms;
        run ~slices:100 e;
        equal e.root None "a missing equality was assumed";
        Engine.collect e;
        List.iteri (fun i a -> if i >= 3 then Engine.add_axiom e a) axioms;
        run e;
        let cert = checked theory e in
        check
          (List.exists
             (fun (s : step) -> match s.rule with Paramodulate _ -> true | _ -> false)
             cert.steps)
          "the resumed proof omitted its equality" );
    ( "general obligations may grow and preserve all non-Horn remainders",
      fun () ->
        let theory, e = prepare growth in
        run e;
        let cert = checked theory e in
        check (e.goals.metrics.committed > 0) "general proof path was not used";
        check
          (List.exists
             (fun (s : step) ->
               match s.rule with
               | Resolve (p, _, q, _, _) ->
                   List.length s.clause >= 2
                   && List.exists
                        (fun (r : step) -> (r.id = p || r.id = q) && List.length r.clause = 1)
                        cert.steps
               | _ -> false)
             cert.steps)
          "no temporarily growing obligation was replayed" );
    ( "conditional equality expansion replays ordinary paramodulation",
      fun () ->
        let theory, e = prepare equality in
        run e;
        let cert = checked theory e in
        check
          (List.exists
             (fun (s : step) -> match s.rule with Paramodulate _ -> true | _ -> false)
             cert.steps)
          "equality was handled without a proof rule" );
    ( "unfinished derivations are shared across roots",
      fun () ->
        let theory, e = prepare (cube "p") in
        run e;
        ignore (checked theory e);
        check (e.goals.metrics.shared > 0) "roots did not reuse any partial proof" );
    ( "whole-obligation substitutions cannot combine incompatible witnesses",
      fun () ->
        let _, e =
          prepare
            "cnf(g,axiom,(~p(X)|~q(X))). cnf(p,axiom,(p(a)|r)). cnf(q,axiom,(q(b)|s)). \
             cnf(nr,axiom,~r). cnf(ns,axiom,~s)."
        in
        run ~slices:300 e;
        equal e.root None "incompatible witnesses refuted a satisfiable theory";
        equal e.avatar.conflicts 0 "a failed match was learned as a conflict" );
    ( "a late clause wakes the substituted obligation after collection",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(g,axiom,(~p(X)|~q(X)|~r(X))). cnf(p,axiom,(p(a)|s)). cnf(ns,axiom,~s). \
             cnf(q,axiom,q(a)). cnf(r,axiom,r(a))."
        in
        let e = Engine.create settings in
        let axioms = Theory.fixed theory in
        List.iteri (fun i a -> if i < 3 then Engine.add_axiom e a) axioms;
        let generated = e.metrics.generated and stored = Proof.stored e.proof in
        run ~slices:150 e;
        equal e.root None "missing obligations were ignored";
        check (e.metrics.generated - generated <= 8) "partial lemmas flooded ordinary search";
        check (Proof.stored e.proof - stored <= 8) "partial lemma promotion grew an unbounded proof";
        check (Tbl.Clause_ints.length e.goals.memo > 0) "partial derivations were not retained";
        Engine.collect e;
        let before = e.goals.metrics.woken in
        List.iteri (fun i a -> if i >= 3 then Engine.add_axiom e a) axioms;
        run e;
        ignore (checked theory e);
        check (e.goals.metrics.woken > before) "new facts did not wake old residual clauses" );
    ( "stale generations invalidate partial recipes without pinning proof nodes",
      fun () ->
        let _, e = prepare "cnf(g,axiom,(~p(X)|~q(X)|~r(X))). cnf(p,axiom,p(a))." in
        run ~slices:80 e;
        check (Tbl.Clause_ints.length e.goals.memo > 0) "fixture has no partial proof";
        let old = Proof.get e.proof 1 in
        Engine.deactivate e old.id;
        Engine.collect e;
        check (e.goals.metrics.invalidated > 0) "reclaimed premise was not diagnosed";
        check
          (Tbl.Int.fold
             (fun _ (s : Goal.state) ok ->
               ok && Goal.valid ~alive:(Engine.current_ticket e) s.proof)
             e.goals.states true)
          "invalid recipe survived collection";
        Engine.admit e old;
        run ~slices:20 e;
        equal e.root None "reactivation revived an old substitution" );
    ( "work limits suspend inference cursors instead of learning failure",
      fun () ->
        let _, e = prepare (cube "q") in
        for _ = 1 to 12 do
          if e.root = None then advance ~attempts:1 e
        done;
        check (e.goals.metrics.slices > 0) "tiny slices did not suspend work";
        check (e.goals.metrics.resumed > 0) "inference cursor was restarted instead of resumed";
        equal e.avatar.conflicts 0 "budget exhaustion became a Boolean constraint" );
    ( "proved branch conflicts prune support supersets and survive proof collection",
      fun () ->
        let _, e, _ = conditional () in
        run ~slices:300 e;
        check (e.avatar.conflicts > 0) "goal derivation did not reach Boolean learning";
        check (e.goals.metrics.blocked > 0) "proved conflicts were not reused";
        equal e.root None "conditional refutation became unconditional";
        let core = List.hd e.avatar.conflict_cores in
        check
          (Avatar.blocked e.avatar ~guard:(fun () -> ()) (List.sort_uniq compare (999 :: core)))
          "a sufficient conflict did not prune a larger support";
        check
          (not (Avatar.blocked e.avatar ~guard:(fun () -> ()) []))
          "conflict escaped its support";
        Engine.collect e;
        Engine.protect (fun () -> Engine.synchronize e);
        run ~slices:80 e;
        equal e.root None "satisfiable alternative was discarded";
        check
          (Avatar.blocked e.avatar ~guard:(fun () -> ()) core)
          "collection forgot a proved conflict" );
    ( "general partial derivations compose with a final AVATAR certificate",
      fun () ->
        let theory, e = conditional_refutation () in
        let cert = checked theory e in
        check (cert.avatar <> None) "fixture did not retain its Boolean refutation" );
    ( "root rotation reaches late clauses and increases depth contours",
      fun () ->
        let chain = [ cube ~arity:4 "deep" ] in
        let distractions =
          List.init 40 (fun i -> Printf.sprintf "cnf(d%d,axiom,(~u%d(X)|v%d(X)))." i i i)
        in
        let theory = Tptp.parse (String.concat " " (distractions @ chain)) in
        let e = Engine.create settings in
        let axioms = Theory.fixed theory in
        List.iteri (fun i a -> if i < 40 then Engine.add_axiom e a) axioms;
        run ~slices:500 e;
        List.iteri (fun i a -> if i >= 40 then Engine.add_axiom e a) axioms;
        run ~slices:6000 e;
        ignore (checked theory e);
        check (e.goals.metrics.roots >= 40) "oldest roots were bypassed";
        check (e.goals.metrics.widened > 0) "initial depth became a permanent cap" );
    ( "renaming symbols and reversing input order preserves general proofs",
      fun () ->
        List.iter
          (fun prefix ->
            let input = cube prefix in
            let statements =
              String.split_on_char '.' input |> List.filter (fun s -> String.trim s <> "")
            in
            List.iter
              (fun xs ->
                let theory, e = prepare (String.concat "." xs ^ ".") in
                run e;
                ignore (checked theory e))
              [ statements; List.rev statements ])
          [ "alpha"; "renamed" ] );
    ( "positive-only knowledge parks instead of expanding inverse equalities forever",
      fun () ->
        let _, e = prepare "cnf(p,axiom,p(f(a))). cnf(e,axiom,(r|f(X)=X))." in
        run ~slices:100 e;
        check (not (Goal.has_work e.goals)) "unopposed positive clauses started an infinite search"
    );
  ]

let () =
  match Array.to_list Sys.argv with
  | [ _; "--export-rocq"; directory ] -> (
      List.iter
        (fun (file, text) ->
          let theory, e = prepare text in
          run e;
          match Kernel.rocq_document theory (checked theory e) with
          | Ok document -> Sexp.write_file (Filename.concat directory file) document
          | Error error -> failwith error)
        [
          ("GoalRefutation.v", growth);
          ("GoalEqualityRefutation.v", equality);
          ("GoalSharedRefutation.v", cube "p");
        ];
      let theory, e = promoted_refutation () in
      (match Kernel.rocq_document theory (checked theory e) with
      | Ok document ->
          Sexp.write_file (Filename.concat directory "GoalPromotedRefutation.v") document
      | Error error -> failwith error);
      let theory, e = first_refutation () in
      (match Kernel.rocq_document theory (checked theory e) with
      | Ok document ->
          Sexp.write_file (Filename.concat directory "GoalFirstTrialRefutation.v") document
      | Error error -> failwith error);
      let theory, e = conditional_refutation () in
      match Kernel.rocq_document theory (checked theory e) with
      | Ok document -> Sexp.write_file (Filename.concat directory "GoalAvatarRefutation.v") document
      | Error error -> failwith error)
  | _ -> Test_support.run tests
