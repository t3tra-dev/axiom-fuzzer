open Axiom_fuzzer
open Test_support
open Wire

let settings =
  {
    config.engine with
    avatar = false;
    subsumption = false;
    selection = false;
    collect_every = 0;
    limits = { Engine.seconds = 5.; max_given = 1000; max_generated = 30000; max_retained = 30000 };
  }

let prepare text =
  let theory = Tptp.parse text in
  let engine = Engine.create settings in
  List.iter (Engine.add_axiom engine) (Theory.fixed theory);
  (theory, engine)

let run_bridge e =
  let turns = ref 0 in
  while e.Engine.root = None && Ground_boolean.has_work e.ground_boolean && !turns < 100 do
    incr turns;
    Engine.protect (fun () -> Engine.ground_step e)
  done;
  check (!turns < 100) "Boolean bridge did not finish its finite diagnostic"

let checked theory e =
  let certificate =
    match Engine.certificate e ~theory:(Theory.name theory) with
    | None -> failwith ("expected a ground refutation: " ^ Engine.reason e)
    | Some c -> c
  in
  (match Kernel.check theory certificate with Ok _ -> () | Error error -> failwith error);
  certificate

let square =
  "cnf(pp,axiom,(p(a)|q(a))). cnf(np,axiom,(~p(a)|q(a))). cnf(pn,axiom,(p(a)|~q(a))). \
   cnf(nn,axiom,(~p(a)|~q(a)))."

(* Everything a context exposes, with the two hash tables that are only looked up as sorted
   bindings (their bucket order is not observable). *)
let snapshot (t : Ground_boolean.t) =
  let sorted fold table = List.sort compare (fold (fun k v acc -> (k, v) :: acc) table []) in
  ( ( sorted Tbl.Atom.fold t.atoms,
      sorted Tbl.Clause.fold t.seen,
      Tbl.Int.fold (fun k v acc -> (k, v) :: acc) t.leaves [],
      Ground_boolean.roots t,
      Ground_boolean.size t ),
    ( t.dirty,
      t.exhausted,
      t.quantum,
      t.statistics,
      Boolean.proof t.solver,
      Boolean.statistics t.solver,
      t.solver.variables ) )

let tests =
  [
    ( "the rebuild without notes leaves the context the noted rebuild leaves",
      fun () ->
        let rng = Random.State.make [| 4242 |] in
        let atom () =
          let c = constant (string_of_int (Random.State.int rng 4)) in
          match Random.State.int rng 3 with
          | 0 -> P ("p", [ c ])
          | 1 -> P ("q", [ c; constant "k" ])
          | _ -> E (c, constant "k")
        in
        for round = 1 to 150 do
          let capacity = if round mod 5 = 0 then 10 + Random.State.int rng 40 else 100000 in
          let quick = Ground_boolean.create ~capacity ()
          and slow = Ground_boolean.create ~capacity ()
          and lazy_ = Ground_boolean.create ~capacity () in
          let alive = Hashtbl.create 64 and next = ref 0 and steps = Hashtbl.create 64 in
          let get id = Hashtbl.find steps id in
          for _ = 1 to 1 + Random.State.int rng 10 do
            for _ = 1 to Random.State.int rng 12 do
              let clause =
                List.init
                  (1 + Random.State.int rng 3)
                  (fun _ -> { positive = Random.State.bool rng; atom = atom () })
                |> Clause.normalize
              in
              let step : step = { id = !next; clause; rule = Input (!next, 0) } in
              incr next;
              Hashtbl.replace steps step.id step;
              Hashtbl.replace alive step.id ();
              Ground_boolean.note quick ~guard:(fun () -> ()) ~support:[] step;
              Ground_boolean.note slow ~guard:(fun () -> ()) ~support:[] step;
              Ground_boolean.note lazy_ ~guard:(fun () -> ()) ~support:[] step
            done;
            if Random.State.bool rng then (
              ignore (Boolean.solve quick.solver ~guard:(fun () -> ()));
              ignore (Boolean.solve slow.solver ~guard:(fun () -> ()));
              (* The solver is read: a deferred rebuild happens first, as in [advance]. *)
              Ground_boolean.materialize lazy_;
              ignore (Boolean.solve lazy_.solver ~guard:(fun () -> ())));
            (* Deaths reach the deferring context as the engine's deactivations do. *)
            Hashtbl.filter_map_inplace
              (fun id () ->
                if Random.State.int rng 3 = 0 then (
                  Ground_boolean.forget lazy_ id;
                  None)
                else Some ())
              alive;
            let keep id = Hashtbl.mem alive id in
            Ground_boolean.collect quick ~keep ~get;
            Ground_boolean.collect_reference slow ~keep ~get;
            Ground_boolean.collect_logged lazy_ ~keep;
            equal (snapshot quick) (snapshot slow) "the rebuild changed the ground context";
            (* Before the deferred rebuild, the deferring context answers as a rebuilt one. *)
            equal
              ( List.sort compare (Ground_boolean.roots lazy_),
                Ground_boolean.proof_size lazy_,
                Ground_boolean.has_work lazy_,
                List.sort compare (Tbl.Clause.fold (fun k v acc -> (k, v) :: acc) lazy_.seen []),
                lazy_.statistics.rebuilt )
              ( List.sort compare (Ground_boolean.roots quick),
                Ground_boolean.proof_size quick,
                Ground_boolean.has_work quick,
                List.sort compare (Tbl.Clause.fold (fun k v acc -> (k, v) :: acc) quick.seen []),
                quick.statistics.rebuilt )
              "the deferring context answers differently before its rebuild";
            if Random.State.int rng 3 = 0 then (
              Ground_boolean.materialize lazy_;
              equal (snapshot lazy_) (snapshot quick) "the deferred rebuild differs")
          done;
          Ground_boolean.materialize lazy_;
          equal (snapshot lazy_) (snapshot quick) "the deferred rebuild differs at the end";
          let a = Boolean.solve quick.solver ~guard:(fun () -> ())
          and b = Boolean.solve slow.solver ~guard:(fun () -> ())
          and c = Boolean.solve lazy_.solver ~guard:(fun () -> ()) in
          equal a b "the rebuilt contexts solve differently";
          equal c a "the deferred context solves differently";
          equal (snapshot quick) (snapshot slow) "the rebuilt contexts learned differently";
          equal (snapshot lazy_) (snapshot quick) "the deferred context learned differently"
        done );
    ( "a leaf noted while a rebuild is pending is the leaf noted after it, even interrupted",
      fun () ->
        (* Two contexts take the same leaves, deaths and collections; one is materialized before
           every note, so its notes take the immediate path, the other defers them. Some notes
           are interrupted by their guard at a random literal, as the engine's cooperative check
           can. Both must answer alike while pending and be the same context when read. *)
        let rng = Random.State.make [| 1119; 5 |] in
        let atom () =
          let c = constant (string_of_int (Random.State.int rng 30)) in
          match Random.State.int rng 3 with
          | 0 -> P ("p", [ c ])
          | 1 -> P ("q", [ c; constant "k" ])
          | _ -> E (c, constant "k")
        in
        let deferred = ref 0 and interrupted = ref 0 in
        for round = 1 to 200 do
          let capacity = if round mod 7 = 0 then 20 + Random.State.int rng 40 else 100000 in
          let eager = Ground_boolean.create ~capacity ()
          and lazy_ = Ground_boolean.create ~capacity () in
          let alive = Hashtbl.create 64 and next = ref 0 in
          for _ = 1 to 1 + Random.State.int rng 12 do
            for _ = 1 to Random.State.int rng 10 do
              let clause =
                List.init
                  (1 + Random.State.int rng 3)
                  (fun _ -> { positive = Random.State.bool rng; atom = atom () })
                |> Clause.normalize
              in
              let step : step = { id = !next; clause; rule = Input (!next, 0) } in
              incr next;
              (* The ground test calls the guard once per function symbol; the addition's calls
                 (one per literal) follow. *)
              let symbols =
                let rec count = function
                  | V _ -> 0
                  | Fn (_, ts) -> 1 + List.fold_left (fun n t -> n + count t) 0 ts
                in
                List.fold_left
                  (fun n (l : literal) ->
                    n + List.fold_left (fun n t -> n + count t) 0 (Clause.atom_terms l.atom))
                  0 clause
              in
              let stop =
                if Random.State.int rng 4 = 0 then
                  symbols + Random.State.int rng (List.length clause)
                else -1
              in
              let note t =
                let calls = ref 0 in
                try
                  Ground_boolean.note t ~support:[] step ~guard:(fun () ->
                      if !calls = stop then raise Exit;
                      incr calls);
                  true
                with Exit -> false
              in
              Ground_boolean.materialize eager;
              if lazy_.pending then incr deferred;
              let a = note eager and b = note lazy_ in
              equal a b "the guard raised in one context only";
              if a then Hashtbl.replace alive step.id ()
              else (
                (* The interrupted note left the context as the addition stopped. *)
                incr interrupted;
                Ground_boolean.materialize lazy_;
                equal (snapshot lazy_) (snapshot eager) "an interrupted note left another context")
            done;
            Hashtbl.filter_map_inplace
              (fun id () ->
                if Random.State.int rng 3 = 0 then (
                  Ground_boolean.forget eager id;
                  Ground_boolean.forget lazy_ id;
                  None)
                else Some ())
              alive;
            let keep id = Hashtbl.mem alive id in
            Ground_boolean.collect_logged eager ~keep;
            Ground_boolean.collect_logged lazy_ ~keep;
            equal
              ( List.sort compare (Ground_boolean.roots lazy_),
                Ground_boolean.proof_size lazy_,
                Ground_boolean.has_work lazy_ )
              ( List.sort compare (Ground_boolean.roots eager),
                Ground_boolean.proof_size eager,
                Ground_boolean.has_work eager )
              "the deferring context answers differently while pending";
            if Random.State.int rng 4 = 0 then (
              Ground_boolean.materialize eager;
              Ground_boolean.materialize lazy_;
              equal (snapshot lazy_) (snapshot eager) "the deferred notes made another context";
              let x = Boolean.solve eager.solver ~guard:(fun () -> ())
              and y = Boolean.solve lazy_.solver ~guard:(fun () -> ()) in
              equal x y "the contexts solve differently")
          done;
          Ground_boolean.materialize eager;
          Ground_boolean.materialize lazy_;
          equal (snapshot lazy_) (snapshot eager)
            "the deferred notes made another context at the end"
        done;
        check (!deferred > 500) "too few notes met a pending rebuild";
        check (!interrupted > 100) "too few interrupted notes" );
    ( "ground non-Horn refutation uses only ordinary resolution",
      fun () ->
        let theory, e = prepare square in
        run_bridge e;
        let cert = checked theory e in
        equal e.metrics.given 0 "Boolean proof required a given clause";
        equal cert.avatar None "bridge introduced a new certificate branch";
        check (Ground_boolean.final_steps e.ground_boolean cert > 0) "bridge proof absent";
        List.iter
          (fun (s : step) ->
            match s.rule with
            | Input _ | Resolve _ -> ()
            | _ -> failwith "unexpected lifted inference")
          cert.steps );
    ( "an unconditional ground component closes a mixed theory",
      fun () ->
        let theory, e = prepare (square ^ " cnf(noise,axiom,(~grow(X)|grow(f(X)))).") in
        run_bridge e;
        let cert = checked theory e in
        equal e.ground_boolean.statistics.inputs 4 "non-ground distractor entered projection";
        equal (List.length cert.axioms) 4 "unused distractor is a proof authority" );
    ( "ground SAT projection is not a consistency answer",
      fun () ->
        let _, e = prepare "cnf(pp,axiom,(p(a)|q(a))). cnf(np,axiom,(~p(a)|q(a)))." in
        run_bridge e;
        equal e.root None "SAT projection was called a refutation";
        equal e.stopped None "SAT projection stopped ordinary search";
        check (Engine.has_work e) "ordinary search was discarded";
        equal e.ground_boolean.statistics.conflicts 0 "SAT projection counted a conflict" );
    ( "ground Horn clauses are admitted without a dedicated mode",
      fun () ->
        let theory, e =
          prepare "cnf(seed,axiom,p(a)). cnf(link,axiom,(~p(a)|q(a))). cnf(deny,axiom,~q(a))."
        in
        run_bridge e;
        ignore (checked theory e) );
    ( "a later unconditional ground resolvent extends the same context",
      fun () ->
        let theory, e =
          prepare
            "cnf(lift,axiom,(p(X)|q(X)|r(X))). cnf(np,axiom,~p(a)). cnf(qn,axiom,(q(a)|~r(a))). \
             cnf(nq,axiom,(~q(a)|r(a))). cnf(nn,axiom,(~q(a)|~r(a)))."
        in
        run_bridge e;
        equal e.root None "ground fragment should initially be satisfiable";
        let input n = List.find (fun (s : step) -> s.rule = Input (n, 0)) (Proof.steps e.proof) in
        Engine.protect (fun () -> Calculus.resolve e.calculus (input 0) (input 1) (Engine.emit e));
        check (e.ground_boolean.statistics.derived_inputs > 0) "derived ground clause was ignored";
        run_bridge e;
        let cert = checked theory e in
        check
          (List.exists (fun (a : axiom) -> a.axiom_id = 0) cert.axioms)
          "non-ground premise was lost from the lifted proof" );
    ( "conditional facts never become unconditional SAT leaves",
      fun () ->
        let t = Ground_boolean.create ~capacity:100 () in
        let p : step = { id = 0; clause = [ positive (P ("p", [])) ]; rule = Component 0 } in
        let n : step = { id = 1; clause = [ negative (P ("p", [])) ]; rule = Component 1 } in
        Ground_boolean.note t ~guard:(fun () -> ()) ~support:[ 0 ] p;
        Ground_boolean.note t ~guard:(fun () -> ()) ~support:[ 1 ] n;
        Ground_boolean.note t ~guard:(fun () -> ()) ~support:[] p;
        equal t.statistics.inputs 0 "conditional component accepted";
        equal (Ground_boolean.roots t) [] "conditional root pinned" );
    ( "collection removes retired Boolean explanations before ID reinsertion",
      fun () ->
        let theory, e = prepare square in
        let old = List.map (Proof.get e.proof) (Ground_boolean.roots e.ground_boolean) in
        List.iter (fun (s : step) -> Engine.retire e s.id) old;
        Engine.collect e;
        equal (Proof.stored e.proof) 0 "obsolete context defeated collection";
        equal (Ground_boolean.proof_size e.ground_boolean) 0 "old SAT explanation survived";
        check (e.ground_boolean.statistics.rebuilt > 0) "context was not rebuilt";
        List.iter (fun (s : step) -> Engine.protect (fun () -> Engine.emit e s.clause s.rule)) old;
        run_bridge e;
        let cert = checked theory e in
        check
          (List.for_all
             (fun (s : step) -> not (List.exists (fun (o : step) -> o.id = s.id) old))
             cert.steps)
          "old proof ID reappeared";
        Engine.collect e;
        ignore (checked theory e) );
    ( "discarding a context releases its proof dependencies",
      fun () ->
        let _, e = prepare "cnf(p,axiom,p(a))." in
        let ids = Ground_boolean.roots e.ground_boolean in
        Engine.collect e;
        equal (Proof.stored e.proof) 1 "input was not pinned";
        Ground_boolean.release e.ground_boolean;
        List.iter (Engine.retire e) ids;
        Engine.collect e;
        equal (Proof.stored e.proof) 0 "discarded context retained input proof";
        equal (Ground_boolean.roots e.ground_boolean) [] "released context retained roots";
        check (not (Ground_boolean.has_work e.ground_boolean)) "discarded SAT work revived" );
    ( "a SAT budget exhaustion releases the cache and permits fallback",
      fun () ->
        let t = Ground_boolean.create ~capacity:1 () in
        Ground_boolean.note t
          ~guard:(fun () -> ())
          ~support:[]
          { id = 0; clause = [ positive (P ("p", [])) ]; rule = Input (0, 0) };
        check t.exhausted "tiny Boolean capacity was ignored";
        equal (Ground_boolean.roots t) [] "over-budget context pins proof leaves";
        equal (Boolean.proof_size t.solver) 0 "over-budget solver was not discarded" );
    ( "cooperative cancellation preserves a resumable proof context",
      fun () ->
        let theory, e = prepare square in
        let calls = ref 0 in
        let guard () =
          incr calls;
          if !calls = 2 then raise Exit
        in
        (try
           ignore
             (Ground_boolean.advance e.ground_boolean ~guard ~get:(Proof.get e.proof)
                ~record:(Engine.record e));
           failwith "expected cancellation"
         with Exit -> ());
        run_bridge e;
        ignore (checked theory e) );
    ( "equality is a conservative atom abstraction with ordinary fallback",
      fun () ->
        let theory, e = prepare "cnf(eq,axiom,a=b). cnf(p,axiom,p(f(a))). cnf(n,axiom,~p(f(b)))." in
        let result =
          Ground_boolean.advance e.ground_boolean
            ~guard:(fun () -> ())
            ~get:(Proof.get e.proof) ~record:(Engine.record e)
        in
        equal result None "Boolean equality abstraction should have a model";
        Engine.protect (fun () -> Engine.ground_step e);
        ignore (checked theory e);
        equal e.ground_boolean.statistics.conflicts 0
          "congruence was misattributed to Boolean search" );
    ( "non-ground infinite models are never declared impossible",
      fun () ->
        let _, e =
          prepare "fof(i,axiom,(![X,Y]:((f(X)=f(Y))=>(X=Y)))). fof(n,axiom,(![X]:~(f(X)=a)))."
        in
        run_bridge e;
        equal e.root None "finite-domain failure refuted an infinite model";
        equal e.ground_boolean.statistics.inputs 0 "non-ground clauses were silently grounded" );
    ( "the bridge path is enabled in the common Engine scheduler",
      fun () ->
        let theory, e = prepare square in
        Engine.finish e;
        let cert = checked theory e in
        check
          (Ground_boolean.final_steps e.ground_boolean cert > 0)
          "scheduler did not reach the ground bridge" );
  ]

let () = run tests
