open Axiom_fuzzer
open Test_support
open Wire

let settings =
  {
    config.engine with
    avatar = true;
    subsumption = false;
    variants = true;
    collect_every = 0;
    cnf_mode = Distributive;
    limits = { Engine.seconds = 5.; max_given = 1000; max_generated = 30000; max_retained = 30000 };
  }

let original_inputs : (Theory.t * string) list ref = ref []
let saved = ref 0

let prepare text =
  let theory = Tptp.parse text in
  original_inputs := (theory, text) :: !original_inputs;
  let engine = Engine.create settings in
  List.iter (Engine.add_axiom engine) (Theory.fixed theory);
  (theory, engine)

let input engine axiom =
  List.find (fun (step : step) -> step.rule = Input (axiom, 0)) (Proof.steps engine.Engine.proof)

let index literal clause = Option.get (List.find_index (( = ) literal) clause)

let checked theory engine =
  let certificate = Option.get (Engine.certificate engine ~theory:(Theory.name theory)) in
  (match Kernel.check theory certificate with Ok _ -> () | Error error -> failwith error);
  Option.iter
    (fun directory ->
      let stem = Filename.concat directory (Printf.sprintf "fixture-%02d" !saved) in
      incr saved;
      let text = snd (List.find (fun (original, _) -> original == theory) !original_inputs) in
      Sexp.write_file (stem ^ ".p") text;
      Certificate_io.write (stem ^ ".cert") certificate)
    (Sys.getenv_opt "AXIOM_PROOF_FIXTURES");
  certificate

let table_entries fold table = fold (fun _ ids total -> total + List.length ids) table 0

let has_proof engine id =
  try
    ignore (Proof.get engine.Engine.proof id);
    true
  with Not_found -> false

let explanation engine =
  let p = input engine 0 and link = input engine 1 in
  Engine.record_ground_explanation ~support:[] engine
    [ positive (P ("q", [ constant "a" ])) ]
    (Resolve (p.id, 0, link.id, index (negative (P ("p", [ constant "a" ]))) link.clause, []))

let chain = "cnf(p,axiom,p(a)). cnf(link,axiom,(~p(a)|q(a))). cnf(no,axiom,~q(a))."

let tests =
  [
    ( "ground proof storage shares the Engine retained-node budget",
      fun () ->
        let engine =
          Engine.create { settings with limits = { settings.limits with max_retained = 9 } }
        in
        let theory =
          Tptp.parse
            "cnf(pp,axiom,(p|q)). cnf(np,axiom,(~p|q)). cnf(pn,axiom,(p|~q)). \
             cnf(nn,axiom,(~p|~q))."
        in
        List.iter (Engine.add_axiom engine) (Theory.fixed theory);
        (* Exercise storage pressure rather than a deliberately tiny turn's
           cooperative work limit. The storage capacity remains unchanged. *)
        engine.ground_boolean.quantum <- 1000;
        let turns = ref 0 in
        while Ground_boolean.has_work engine.ground_boolean && !turns < 100 do
          incr turns;
          Engine.protect (fun () -> Engine.ground_step engine)
        done;
        check engine.ground_boolean.exhausted
          (Printf.sprintf
             "shared proof budget was ignored: proof=%d Boolean=%d root=%b stopped=%s turns=%d"
             (Proof.stored engine.proof)
             (Ground_boolean.proof_size engine.ground_boolean)
             (engine.root <> None)
             (Option.value ~default:"none" engine.stopped)
             !turns);
        check (not engine.ground_boolean.running) "capacity release left a running context";
        equal engine.stopped None "optional proof cache stopped ordinary search";
        equal (Ground_boolean.proof_size engine.ground_boolean) 0 "cache was not released";
        check (Engine.has_work engine) "ordinary search work was lost" );
    ( "ordinary admission releases optional ground storage before consuming more nodes",
      fun () ->
        let engine =
          Engine.create { settings with limits = { settings.limits with max_retained = 4 } }
        in
        let theory = Tptp.parse "cnf(p,axiom,p(a)). cnf(q,axiom,q(a)). cnf(r,axiom,r(a))." in
        List.iter (Engine.add_axiom engine) (Theory.fixed theory);
        equal engine.metrics.generated 3 "ordinary third input was rejected";
        equal engine.stopped None "optional context consumed the last ordinary slots";
        check engine.ground_boolean.exhausted "optional context did not relinquish its budget";
        equal (Proof.stored engine.proof) 3 "original proof inputs were discarded" );
    ( "capacity during proof conversion unwinds before releasing and permits ordinary fallback",
      fun () ->
        let theory, engine =
          prepare
            "cnf(pp,axiom,(p|q)). cnf(np,axiom,(~p|q)). cnf(pn,axiom,(p|~q)). \
             cnf(nn,axiom,(~p|~q))."
        in
        let partial = ref None and turns = ref 0 and collection_refused = ref false in
        while Ground_boolean.has_work engine.ground_boolean && !turns < 100 do
          incr turns;
          ignore
            (Ground_boolean.advance engine.ground_boolean
               ~guard:(fun () ->
                 if not !collection_refused then (
                   check
                     (rejects (fun () -> Engine.collect engine))
                     "collection invalidated an active ground proof";
                   collection_refused := true);
                 Engine.check_time engine;
                 if !partial <> None then
                   Ground_boolean.enforce_space engine.ground_boolean ~available:0)
               ~get:(Proof.get engine.proof)
               ~record:(fun clause rule ->
                 let step = Engine.record_ground_explanation engine clause rule in
                 partial := Some step.id;
                 step))
        done;
        check (Option.is_some !partial) "fixture did not begin proof conversion";
        check !collection_refused "fixture did not reach an active guard";
        check engine.ground_boolean.exhausted "conversion did not yield its storage";
        check (not engine.ground_boolean.running) "conversion remained active after release";
        equal engine.root None "partial proof was accepted";
        Engine.collect engine;
        check (not (has_proof engine (Option.get !partial))) "partial explanation remained pinned";
        Engine.finish engine;
        ignore (checked theory engine) );
    ( "explanation records retain dependencies without search registrations",
      fun () ->
        let _, engine = prepare chain in
        let seen = table_entries Avatar.Seen.fold engine.avatar.seen
        and variants = table_entries Avatar.Variants.fold engine.avatar.variants
        and focus = Tbl.Int.length engine.focus.entries in
        let step = explanation engine in
        equal (Avatar.dependency engine.avatar step.id) [] "unconditional support changed";
        equal (Tbl.Int.find engine.avatar.entries step.id).role Avatar.Retired
          "proof-only node is searchable";
        equal
          (table_entries Avatar.Seen.fold engine.avatar.seen)
          seen "proof node entered duplicate index";
        equal
          (table_entries Avatar.Variants.fold engine.avatar.variants)
          variants "proof node entered variant index";
        equal (Tbl.Int.length engine.focus.entries) focus "proof node entered Focus";
        check (not (Index.mem engine.retained_index step.id)) "proof node was admitted" );
    ( "reward traverses a proof-only node and reaches its searchable ancestors",
      fun () ->
        let _, engine = prepare chain in
        let p = input engine 0 and link = input engine 1 in
        let step = explanation engine in
        let rewarded = ref [] in
        Focus.reward engine.focus ~get:(Proof.get engine.proof)
          ~promote:(fun id _ -> rewarded := id :: !rewarded)
          [ step.id ] 8;
        check (List.mem p.id !rewarded && List.mem link.id !rewarded) "ancestor reward was lost";
        check (not (List.mem step.id !rewarded)) "unsearchable explanation was rewarded" );
    ( "legacy record callers keep their Focus reward accounting",
      fun () ->
        let _, engine = prepare chain in
        let p = input engine 0 and link = input engine 1 in
        let step =
          Engine.record engine
            [ positive (P ("q", [ constant "a" ])) ]
            (Resolve (p.id, 0, link.id, index (negative (P ("p", [ constant "a" ]))) link.clause, []))
        in
        check (Tbl.Int.mem engine.focus.entries step.id) "legacy reward accounting changed";
        equal (Tbl.Int.find engine.avatar.entries step.id).role Avatar.Retired
          "legacy explanation became a search candidate" );
    ( "old and thin explanation registries give identical admission and activation decisions",
      fun () ->
        let trace thin =
          let avatar = Avatar.create () in
          let p = positive (P ("p", [ v 0 ])) and q = positive (P ("q", [ v 0 ])) in
          Tbl.Int.add avatar.components 0 { Avatar.clause = [ p ]; node = None };
          let add id clause rule =
            let step = { id; clause; rule } in
            ignore (Avatar.remember avatar ~variants:true step);
            step
          in
          let parent = add 0 [ p ] (Component 0) in
          let link = add 1 [ { p with positive = false }; q ] (Input (0, 0)) in
          let explanation =
            { id = 2; clause = [ q ]; rule = Resolve (parent.id, 0, link.id, 0, []) }
          in
          if thin then ignore (Avatar.remember_explanation avatar ~support:[ 0 ] explanation)
          else (
            ignore (Avatar.remember avatar ~variants:true explanation);
            Avatar.retire avatar explanation.id);
          let inspect () =
            let duplicate support clause =
              Avatar.duplicate avatar
                ~guard:(fun () -> ())
                ~variants:true ~except:(-1) support clause
            in
            let queries =
              List.concat_map
                (fun support ->
                  List.map (duplicate support) [ [ q ]; [ positive (P ("q", [ v 9 ])) ]; [ p ] ])
                [ []; [ 0 ]; [ 0; 1 ] ]
            in
            let activated =
              Avatar.affected_entries avatar ~guard:(fun () -> ()) [ 0 ]
              |> List.map (fun (e : Avatar.entry) -> e.step.id)
            in
            (queries, activated, List.sort compare (Avatar.roots avatar))
          in
          let before = inspect () in
          check
            (not
               (Avatar.duplicate avatar
                  ~guard:(fun () -> ())
                  ~variants:true ~except:(-1) [ 0 ] [ q ]))
            "retired explanation suppressed a later candidate";
          ignore (add 3 [ q ] (Input (1, 0)));
          let admitted = inspect () in
          Avatar.retire avatar 3;
          let retired = inspect () in
          Avatar.collect avatar ~keep:(fun id -> id <> 2 && id <> 3);
          [ before; admitted; retired; inspect () ]
        in
        equal (trace false) (trace true)
          "thin registry changed duplicate/variant or model decisions" );
    ( "unreferenced explanations do not become permanent collection roots",
      fun () ->
        let _, engine = prepare chain in
        let before = Proof.stored engine.proof in
        let step = explanation engine in
        Engine.collect engine;
        equal (Proof.stored engine.proof) before "orphan explanation survived collection";
        check (not (Tbl.Int.mem engine.avatar.entries step.id)) "orphan dependency was retained";
        check (not (has_proof engine step.id)) "orphan proof node was retained" );
    ( "a final ordinary proof pins its explanation chain across collection",
      fun () ->
        let theory, engine = prepare chain in
        let q = explanation engine and denied = input engine 2 in
        let root =
          Engine.record_ground_explanation ~support:[] engine []
            (Resolve (q.id, 0, denied.id, 0, []))
        in
        engine.root <- Some root.id;
        let before = checked theory engine in
        Engine.collect engine;
        equal (checked theory engine) before "collection changed the final proof";
        check (Tbl.Int.mem engine.avatar.entries q.id) "retained ancestor lost support lookup" );
    ( "conditional explanation chains close their branches and survive proof collection",
      fun () ->
        let theory, engine =
          prepare
            "cnf(choice,axiom,(p|q)). cnf(link,axiom,(~p|r)). cnf(nr,axiom,~r). cnf(nq,axiom,~q)."
        in
        Ground_boolean.release engine.ground_boolean;
        let choice = input engine 0 and link = input engine 1 in
        check (Avatar.split engine.avatar ~guard:(fun () -> ()) choice) "fixture did not split";
        let components =
          Tbl.Int.fold
            (fun id (component : Avatar.component) steps ->
              Engine.record engine component.clause (Component id) :: steps)
            engine.avatar.components []
        in
        let cp = List.find (fun (s : step) -> s.clause = [ positive (P ("p", [])) ]) components
        and cq = List.find (fun (s : step) -> s.clause = [ positive (P ("q", [])) ]) components in
        let support = Avatar.dependency engine.avatar cp.id in
        check (support <> []) "component was unconditional";
        let middle =
          Engine.record_ground_explanation ~support engine
            [ positive (P ("r", [])) ]
            (Resolve (cp.id, 0, link.id, index (negative (P ("p", []))) link.clause, []))
        in
        let nr = input engine 2 and nq = input engine 3 in
        let left =
          Engine.record_ground_explanation ~support engine [] (Resolve (middle.id, 0, nr.id, 0, []))
        in
        Avatar.conflict engine.avatar ~guard:(fun () -> ()) left;
        ignore (Avatar.solve engine.avatar ~guard:(fun () -> ()));
        check (not engine.avatar.unsat) "one conditional contradiction refuted the theory";
        equal engine.root None "conditional empty clause became a global root";
        Engine.collect engine;
        equal (Avatar.dependency engine.avatar middle.id) support "GC lost branch dependency";
        let right =
          Engine.record_ground_explanation
            ~support:(Avatar.dependency engine.avatar cq.id)
            engine []
            (Resolve (cq.id, 0, nq.id, 0, []))
        in
        Avatar.conflict engine.avatar ~guard:(fun () -> ()) right;
        Engine.synchronize engine;
        check engine.avatar.unsat "both branch conflicts did not close the split";
        let certificate = checked theory engine in
        Engine.collect engine;
        equal (checked theory engine) certificate "conditional proof changed after collection" );
    ( "explanation API rejects invented branch support without allocating a node",
      fun () ->
        let _, engine = prepare chain in
        let before = Proof.length engine.proof in
        check
          (rejects (fun () ->
               ignore (Engine.record_explanation ~support:[ 42 ] engine [] (Input (0, 0)))))
          "invented branch dependency accepted";
        equal (Proof.length engine.proof) before "invalid support allocated a proof node" );
    ( "each explanation derives its own support before a later joint branch conflict",
      fun () ->
        let _, engine = prepare "cnf(choice,axiom,(p|q)). cnf(apart,axiom,(~p|~q))." in
        Ground_boolean.release engine.ground_boolean;
        check
          (Avatar.split engine.avatar ~guard:(fun () -> ()) (input engine 0))
          "fixture did not split";
        let components =
          Tbl.Int.fold
            (fun id (component : Avatar.component) steps ->
              Engine.record engine component.clause (Component id) :: steps)
            engine.avatar.components []
        in
        let cp = List.find (fun (s : step) -> s.clause = [ positive (P ("p", [])) ]) components
        and cq = List.find (fun (s : step) -> s.clause = [ positive (P ("q", [])) ]) components in
        let apart = input engine 1 in
        let middle =
          Engine.record_ground_explanation engine
            [ negative (P ("q", [])) ]
            (Resolve (cp.id, 0, apart.id, index (negative (P ("p", []))) apart.clause, []))
        in
        let first_support = Avatar.dependency engine.avatar cp.id in
        equal
          (Avatar.dependency engine.avatar middle.id)
          first_support "intermediate inherited a later assumption";
        let root =
          Engine.record_ground_explanation engine [] (Resolve (middle.id, 0, cq.id, 0, []))
        in
        let joint = Avatar.union first_support (Avatar.dependency engine.avatar cq.id) in
        equal (Avatar.dependency engine.avatar root.id) joint "joint support was not derived";
        equal (List.length joint) 2 "fixture did not require both assumptions";
        Avatar.conflict engine.avatar ~guard:(fun () -> ()) root;
        Engine.synchronize engine;
        check (not engine.avatar.unsat) "conditional joint conflict refuted a satisfiable theory";
        equal engine.root None "joint branch conflict became an unconditional root" );
    ( "explanation API keeps component assumptions on their separate admission path",
      fun () ->
        let _, engine = prepare chain in
        let before = Proof.length engine.proof in
        check
          (rejects (fun () -> ignore (Engine.record_explanation engine [] (Component 0))))
          "component bypassed the component registry";
        equal (Proof.length engine.proof) before "rejected component allocated a node" );
    ( "ground normalization rejects free variables before allocating a node",
      fun () ->
        let _, engine = prepare chain in
        let before = Proof.length engine.proof in
        check
          (rejects (fun () ->
               ignore
                 (Engine.record_ground_explanation engine
                    [ positive (P ("p", [ v 0 ])) ]
                    (Input (0, 0)))))
          "nonground fast path accepted a variable";
        equal (Proof.length engine.proof) before "rejected ground clause allocated a node" );
    ( "ground fast normalization agrees with the independent checker ordering",
      fun () ->
        let engine = Engine.create settings in
        let a = constant "a" and b = constant "b" in
        let p = positive (P ("p", [ Fn (Original "f", [ a; b ]) ])) in
        let literals = [ p; negative (E (b, a)); p; positive (E (a, b)); negative (E (b, a)) ] in
        let step = Engine.record_ground_explanation engine literals (Input (0, 0)) in
        equal step.clause (Kernel.normalize literals) "ground normalization changed the clause" );
    ( "Boolean proof lifting rejects unproved symmetric atom collapse",
      fun () ->
        let a = constant "a" and b = constant "b" in
        let ab = E (a, b) and ba = E (b, a) in
        let clauses = [ [ positive ab; positive ba ]; [ negative ab ]; [ negative ba ] ] in
        let solver = Boolean.create () and proof = Proof.create () in
        ignore (Boolean.new_variable solver);
        ignore (Boolean.new_variable solver);
        List.iteri
          (fun id clause -> ignore (Proof.add proof (Clause.normalize clause) (Input (id, 0))))
          clauses;
        List.iteri
          (fun id clause -> ignore (Boolean.add_clause solver ~origin:(Split id) clause))
          [ [ 1; 2 ]; [ -1 ]; [ -2 ] ];
        equal
          (Boolean.solve solver ~guard:(fun () -> ()))
          Boolean.Unsat "finite fixture was not contradictory";
        let leaf (node : Boolean.proof_node) =
          match node.rule with
          | Input (Split id) -> Proof.get proof id
          | _ -> failwith "unexpected leaf"
        in
        check
          (rejects (fun () ->
               ignore
                 (Ground_boolean.lift_proof
                    ~guard:(fun () -> ())
                    ~proof:(Boolean.proof solver)
                    ~encode:(fun l -> if l.positive then 1 else -1)
                    ~leaf
                    ~record:(fun _ _ -> failwith "invalid projection reached recording")
                    ~on_record:(fun _ -> ()))))
          "unproved symmetric atom collapse was accepted";
        let encode literal =
          let variable =
            if literal.atom = ab then 1 else if literal.atom = ba then 2 else assert false
          in
          if literal.positive then variable else -variable
        in
        let root =
          Ground_boolean.lift_proof
            ~guard:(fun () -> ())
            ~proof:(Boolean.proof solver) ~encode ~leaf
            ~record:(fun clause rule -> Proof.add proof clause rule)
            ~on_record:(fun _ -> ())
        in
        equal root.clause [] "exact orientations did not produce a refutation";
        let steps = ref [] in
        let inputs = List.mapi (fun id clause -> (id, [ Clause.normalize clause ])) clauses in
        List.iter
          (fun (step : step) ->
            let expected =
              match Kernel.derive ~inputs ~steps:!steps step.rule with
              | Ok clause -> clause
              | Error error -> failwith error
            in
            equal step.clause expected "lifted inference disagreed with independent replay";
            steps := step :: !steps)
          (Proof.steps proof) );
    ( "cancelled proof lifting leaves collectible intermediates and can restart",
      fun () ->
        let theory, engine =
          prepare
            "cnf(pp,axiom,(p|q)). cnf(np,axiom,(~p|q)). cnf(pn,axiom,(p|~q)). \
             cnf(nn,axiom,(~p|~q))."
        in
        let orphan = ref None in
        (try
           ignore
             (Ground_boolean.advance engine.ground_boolean
                ~guard:(fun () -> ())
                ~get:(Proof.get engine.proof)
                ~record:(fun clause rule ->
                  let step = Engine.record_ground_explanation engine clause rule in
                  orphan := Some step.id;
                  raise Exit));
           (* The Boolean work quantum may yield before reaching a proof. *)
           let tries = ref 0 in
           while !orphan = None && !tries < 100 do
             incr tries;
             ignore
               (Ground_boolean.advance engine.ground_boolean
                  ~guard:(fun () -> ())
                  ~get:(Proof.get engine.proof)
                  ~record:(fun clause rule ->
                    let step = Engine.record_ground_explanation engine clause rule in
                    orphan := Some step.id;
                    raise Exit))
           done
         with Exit -> ());
        check (Option.is_some !orphan) "fixture never reached proof lifting";
        Engine.collect engine;
        check
          (not (has_proof engine (Option.get !orphan)))
          "cancelled explanation defeated collection";
        let turns = ref 0 in
        while
          engine.root = None && engine.stopped = None
          && Ground_boolean.has_work engine.ground_boolean
          && !turns < 100
        do
          incr turns;
          Engine.protect (fun () -> Engine.ground_step engine)
        done;
        ignore (checked theory engine) );
    ( "explanation recording honors cancellation and generation limits",
      fun () ->
        let cancelled = Engine.create ~cancelled:(fun () -> true) settings in
        Engine.protect (fun () ->
            ignore (Engine.record_ground_explanation cancelled [] (Input (0, 0))));
        equal (Proof.stored cancelled.proof) 0 "cancelled recording allocated a node";
        equal cancelled.stopped (Some "cancelled") "cancellation was ignored";
        let bounded =
          Engine.create { settings with limits = { settings.limits with max_generated = 0 } }
        in
        Engine.protect (fun () -> ignore (Engine.record_explanation bounded [] (Input (0, 0))));
        equal (Proof.stored bounded.proof) 0 "generation bound was exceeded";
        equal bounded.stopped (Some "generated clause limit") "generation bound was ignored" );
    ( "explanation recording cannot exceed the retained proof-node bound",
      fun () ->
        let engine =
          Engine.create { settings with limits = { settings.limits with max_retained = 1 } }
        in
        ignore (Engine.record_explanation engine [ positive (P ("p", [])) ] (Input (0, 0)));
        Engine.protect (fun () -> ignore (Engine.record_explanation engine [] (Input (1, 0))));
        equal (Proof.stored engine.proof) 1 "retained proof-node bound was exceeded";
        equal engine.stopped (Some "retained proof node limit") "retained bound was ignored" );
  ]

let () = run tests
