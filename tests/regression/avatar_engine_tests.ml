open Axiom_fuzzer
open Test_support
open Wire

let engine_config =
  {
    config.engine with
    avatar = true;
    cnf_mode = Distributive;
    weight_ratio = 0;
    collect_every = 0;
    limits = { Engine.seconds = 5.; max_given = 1000; max_generated = 30000; max_retained = 30000 };
  }

let avatar (engine : Engine.t) = engine.avatar
let add engine theory i = Engine.add_axiom engine (List.nth (Theory.fixed theory) i)

let checked theory engine =
  let certificate =
    match Engine.certificate engine ~theory:(Theory.name theory) with
    | None -> failwith ("expected refutation: " ^ Engine.reason engine)
    | Some certificate -> certificate
  in
  (match Kernel.check theory certificate with Ok _ -> () | Error error -> failwith error);
  certificate

let run_engine ?(split_first = false) ?(bridge = true) ?(settings = engine_config) theory =
  let engine = Engine.create settings in
  if not bridge then Ground_boolean.release engine.ground_boolean;
  List.iter (Engine.add_axiom engine) (Theory.fixed theory);
  if split_first then
    List.iter
      (fun (step : step) ->
        if List.length step.clause > 1 then (
          Avatar.offer_split (avatar engine) ~guard:(fun () -> ()) step;
          Engine.protect (fun () -> Engine.split_step engine (avatar engine));
          Engine.deactivate engine step.id))
      (Proof.steps engine.proof);
  Engine.finish engine;
  engine

let no_refutation engine =
  check (engine.Engine.root = None) "a satisfiable problem was refuted";
  equal engine.stopped None "the finite satisfiable fixture hit a bound";
  check (not (Engine.has_work engine)) "fixture has pending work"

let absent_from_indices (engine : Engine.t) id =
  List.iter
    (fun (name, present) -> check (not present) ("deactivated clause remains in " ^ name))
    [
      ("Passive", Tbl.Int.mem engine.passive.live id);
      ("Active", Index.mem engine.index id);
      ("retained resolution index", Index.mem engine.retained_index id);
      ("ground unit pool", Tbl.Int.mem engine.ground_units id);
      ( "ground literal index",
        Tbl.Literal.fold (fun _ ids found -> found || List.mem id ids) engine.ground_literals false
      );
      ("equality index", Tbl.Int.mem engine.equality_index.live id);
      ("demodulation index", Tbl.Int.mem engine.demodulator.live id);
      ("forward subsumption index", Tbl.Int.mem engine.subsumption_index.live id);
      ("backward subsumption index", Tbl.Int.mem engine.retained_subsumption.live id);
    ]

let ground_four =
  "fof(pp,axiom,(p(a)|q(a))). fof(np,axiom,(~p(a)|q(a))). fof(pn,axiom,(p(a)|~q(a))). \
   fof(nn,axiom,(~p(a)|~q(a)))."

let non_ground =
  "fof(choice,axiom,((![X]:p(X))|(![Y]:q(Y)))). fof(notp,axiom,~p(a)). fof(notq,axiom,~q(b))."

(* The engine's ground-unit counters against a recount of its ground units and literals. *)
let ground_counts_consistent (engine : Engine.t) =
  let clashes =
    Tbl.Literal.fold
      (fun (l : literal) _ n ->
        if l.positive && Tbl.Literal.mem engine.ground_literals { l with positive = false } then
          n + 1
        else n)
      engine.ground_literals 0
  and reflexive, equations =
    Tbl.Int.fold
      (fun _ (_, (l : literal)) (r, e) ->
        match l.atom with
        | E _ when l.positive -> (r, e + 1)
        | E (a, b) when a = b -> (r + 1, e)
        | _ -> (r, e))
      engine.ground_units (0, 0)
  in
  equal
    (engine.ground_clashes, engine.ground_reflexive, engine.ground_equations)
    (clashes, reflexive, equations) "ground unit counters differ from a recount"

let tests =
  [
    ( "a fresh Boolean refutation replaces the incremental one only with fewer steps",
      fun () ->
        (* Three-atom pigeonhole-like ground clauses split into components: several Boolean
           conflicts, so the incremental solver learns clauses before its refutation. *)
        let problem =
          "fof(c1,axiom,(p(a)|q(a)|r(a))). fof(c2,axiom,(~p(a)|q(a)|r(a))). \
           fof(c3,axiom,(p(a)|~q(a)|r(a))). fof(c4,axiom,(p(a)|q(a)|~r(a))). \
           fof(c5,axiom,(~p(a)|~q(a)|r(a))). fof(c6,axiom,(~p(a)|q(a)|~r(a))). \
           fof(c7,axiom,(p(a)|~q(a)|~r(a))). fof(c8,axiom,(~p(a)|~q(a)|~r(a)))."
        in
        let theory = Tptp.parse problem in
        let steps fresh =
          let engine =
            run_engine ~split_first:true ~bridge:false
              ~settings:{ engine_config with fresh_refutation = fresh }
              theory
          in
          let c = checked theory engine in
          check (c.avatar <> None) "the fixture was not an AVATAR refutation";
          (match Kernel.check theory (Certificate_io.decode (Certificate_io.encode c)) with
          | Ok _ -> ()
          | Error e -> failwith e);
          fst (Proof.statistics c)
        in
        let incremental = steps false and chosen = steps true in
        check (chosen <= incremental)
          (Printf.sprintf "the chosen refutation is longer (%d > %d)" chosen incremental) );
    ( "the ground-unit counters follow additions, removals and branch changes",
      fun () ->
        let units = ref 0 and equations = ref 0 and clashes = ref 0 in
        let ground_counts_consistent (engine : Engine.t) =
          ground_counts_consistent engine;
          units := max !units (Tbl.Int.length engine.ground_units);
          equations := max !equations engine.ground_equations;
          clashes := max !clashes (engine.ground_clashes + engine.ground_reflexive)
        in
        List.iter
          (fun problem ->
            let theory = Tptp.parse problem in
            let engine = Engine.create engine_config in
            List.iter (Engine.add_axiom engine) (Theory.fixed theory);
            ground_counts_consistent engine;
            let steps = ref 0 in
            while
              !steps < 400 && engine.root = None && engine.stopped = None && Engine.has_work engine
            do
              Engine.protect (fun () -> Engine.step engine);
              ground_counts_consistent engine;
              incr steps
            done;
            List.iter
              (fun (step : step) ->
                Engine.deactivate engine step.id;
                ground_counts_consistent engine)
              (Proof.steps engine.proof))
          [
            ground_four;
            non_ground;
            "fof(a1,axiom,(p(a)|q(b))). fof(a2,axiom,(~p(a)|r(c))). fof(a3,axiom,~r(c)). \
             fof(a4,axiom,(q(b) => s)). fof(a5,axiom,~s).";
            "fof(e1,axiom,(f(a)=b|t)). fof(e2,axiom,(~t|f(b)=a)). fof(e3,axiom,f(f(a))!=f(a)). \
             fof(e4,axiom,(b!=b|q)). fof(e5,axiom,(~q|p(f(a)))). fof(e6,axiom,~p(b)).";
            "fof(u1,axiom,r(a,b)). fof(u2,axiom,(q|r(b,a))). fof(u3,axiom,~q). \
             fof(u4,axiom,~r(a,b)).";
            "fof(r1,axiom,f(a)!=f(a)). fof(r2,axiom,(p(a)|q)).";
          ];
        check
          (!units > 2 && !equations > 0 && !clashes > 0)
          (Printf.sprintf "fixtures too weak: %d units, %d equations, %d clashes" !units !equations
             !clashes) );
    ( "AVATAR ground four-clause contradiction produces a checked Boolean root",
      fun () ->
        let theory = Tptp.parse ground_four in
        let engine =
          run_engine ~split_first:true ~settings:{ engine_config with subsumption = false } theory
        in
        let certificate = checked theory engine in
        check (Option.is_some certificate.avatar) "ground splitting did not use the SAT proof";
        let state = avatar engine in
        check (Tbl.Int.length state.splits >= 4) "input ground clauses were not split";
        check (state.conflicts > 0) "FO conflicts were not communicated to SAT";
        let pushed = ref [] in
        Avatar.iter_roots state (fun id -> pushed := id :: !pushed);
        equal (List.sort compare !pushed)
          (List.sort compare (Avatar.roots state))
          "the pushed AVATAR roots differ from the listed ones" );
    ( "AVATAR splits variable-disjoint non-ground components with checked provenance",
      fun () ->
        let theory = Tptp.parse non_ground in
        let engine = run_engine ~split_first:true theory in
        let certificate = checked theory engine in
        let proof = Option.get certificate.avatar in
        check
          (List.exists (fun clause -> Wire.variables clause <> []) proof.components)
          "non-ground component disappeared";
        check
          (List.exists
             (fun (s : step) -> match s.rule with Component _ -> true | _ -> false)
             certificate.steps)
          "component assumptions are missing from the proof" );
    ( "AVATAR does not split shared variables in a satisfiable two-element example",
      fun () ->
        let theory =
          Tptp.parse
            "fof(choice,axiom,(![X]:(p(X)|q(X)))). fof(notp,axiom,~p(a)). fof(notq,axiom,~q(b))."
        in
        (* Witness: a=0, b=1, p(x) iff x=1, q(x) iff x=0. *)
        let engine = run_engine theory in
        no_refutation engine;
        equal (Tbl.Int.length (avatar engine).splits) 0 "shared-variable clause was divided";
        no_refutation (run_engine ~settings:{ engine_config with avatar = false } theory) );
    ( "AVATAR conditional empty clause closes only its own branch",
      fun () ->
        let theory = Tptp.parse "fof(choice,axiom,(p|q)). fof(notq,axiom,~q)." in
        (* Isolate branch conflict handling from admission-time unit deletion. *)
        let engine = run_engine ~settings:{ engine_config with subsumption = false } theory in
        no_refutation engine;
        let state = avatar engine in
        check (state.conflicts > 0) "fixture did not explore its inconsistent branch";
        check (not state.unsat) "one branch conflict became a global contradiction";
        check
          (List.exists
             (fun (s : step) -> s.clause = [] && Avatar.dependency state s.id <> [])
             (Proof.steps engine.proof))
          "conditional empty proof node was lost";
        equal
          (Engine.certificate engine ~theory:(Theory.name theory))
          None "a branch conflict was exposed as a certificate" );
    ( "AVATAR conditional backward subsumption restores the original clause after a model change",
      fun () ->
        let theory =
          Tptp.parse
            "fof(old,axiom,(o|p(a))). fof(choice,axiom,(![X]:(a|p(X)))). \
             fof(refute_branch,axiom,~p(b)). fof(refute_old,axiom,~p(a)). fof(no_o,axiom,~o)."
        in
        let engine = Engine.create { engine_config with backward_subsumption = true } in
        add engine theory 0;
        Engine.finish engine;
        let target =
          Avatar.ordered_entries (avatar engine)
          |> List.find (fun (e : Avatar.entry) ->
              e.support <> [] && e.step.clause = [ positive (P ("p", [ constant "a" ])) ])
          |> fun e -> e.step.id
        in
        add engine theory 1;
        Engine.finish engine;
        let state = avatar engine in
        check (Option.is_some (Tbl.Int.find state.entries target).lock) "old clause was not frozen";
        absent_from_indices engine target;
        Engine.collect engine;
        ignore (Proof.get engine.proof target);
        add engine theory 2;
        Engine.finish engine;
        no_refutation engine;
        check (state.unlocked > 0 && Index.mem engine.index target) "frozen clause did not return";
        equal (Tbl.Int.find state.entries target).lock None "obsolete simplification lock survived";
        List.iter (add engine theory) [ 3; 4 ];
        Engine.finish engine;
        ignore (checked theory engine) );
    ( "AVATAR conditional demodulation restores its target and retires all branch memberships",
      fun () ->
        let theory =
          Tptp.parse
            "fof(old,axiom,(o|p(f(a)))). fof(choice,axiom,(![X]:(a|f(X)=X))). \
             fof(refute_branch,axiom,f(b)!=b). fof(refute_old,axiom,~p(f(a))). fof(no_o,axiom,~o)."
        in
        let engine =
          Engine.create
            { engine_config with ordered = true; demodulation = true; backward_demodulation = true }
        in
        add engine theory 0;
        Engine.finish engine;
        let target =
          Avatar.ordered_entries (avatar engine)
          |> List.find (fun (e : Avatar.entry) ->
              e.support <> []
              && e.step.clause = [ positive (P ("p", [ Fn (Original "f", [ constant "a" ]) ])) ])
          |> fun e -> e.step.id
        in
        add engine theory 1;
        Engine.finish engine;
        let state = avatar engine in
        check (engine.metrics.backward_demodulated > 0) "conditional rewrite was not exercised";
        check
          (Option.is_some (Tbl.Int.find state.entries target).lock)
          "rewrite target was not frozen";
        absent_from_indices engine target;
        let condition = fst (Option.get (Tbl.Int.find state.entries target).lock) in
        let branch_nodes =
          Avatar.ordered_entries state
          |> List.filter (fun (e : Avatar.entry) ->
              List.exists (fun id -> List.mem id e.support) condition && Avatar.enabled state e)
          |> List.map (fun (e : Avatar.entry) -> e.step.id)
        in
        check (branch_nodes <> []) "conditional branch has no retained nodes";
        Engine.collect engine;
        add engine theory 2;
        Engine.finish engine;
        no_refutation engine;
        check
          (Index.mem engine.index target && state.unlocked > 0)
          "rewrite target was not restored";
        List.iter (absent_from_indices engine) branch_nodes;
        List.iter (add engine theory) [ 3; 4 ];
        Engine.finish engine;
        ignore (checked theory engine) );
    ( "AVATAR keeps incomparable supports and admits a later unconditional strengthening",
      fun () ->
        let theory =
          Tptp.parse
            "fof(first,axiom,(![X]:(a|r(X)))). fof(second,axiom,(![X]:(b|s(X)))). \
             fof(rp,axiom,(![X]:(~r(X)|p(X)))). fof(sp,axiom,(![X]:(~s(X)|p(X)))). \
             fof(global,axiom,(![X]:p(X))). fof(nr,axiom,~r(c)). fof(ns,axiom,~s(c)). \
             fof(np,axiom,~p(c))."
        in
        let engine =
          (* Keep both implication clauses until they have independently derived
             p; conditional subsumption could legitimately freeze the second. *)
          Engine.create { engine_config with subsumption = false; variants = true }
        in
        List.iter (add engine theory) [ 0; 1; 2; 3 ];
        Engine.finish engine;
        let state = avatar engine in
        let clause = Clause.normalize [ positive (P ("p", [ v 0 ])) ] in
        let copies () =
          Avatar.ordered_entries state
          |> List.filter (fun (e : Avatar.entry) -> e.step.clause = clause)
        in
        let supports =
          List.map (fun (e : Avatar.entry) -> e.support) (copies ()) |> List.sort_uniq compare
        in
        check (List.length supports >= 2) "one incomparable support suppressed another";
        check (List.for_all (( <> ) []) supports) "fixture unexpectedly derived global p";
        add engine theory 4;
        Engine.finish engine;
        check
          (List.exists
             (fun (e : Avatar.entry) -> e.support = [] && e.role = Avatar.Candidate)
             (copies ()))
          "conditional copies suppressed the unconditional strengthening";
        List.iter (add engine theory) [ 5; 6 ];
        Engine.finish engine;
        no_refutation engine;
        add engine theory 7;
        Engine.finish engine;
        ignore (checked theory engine) );
    ( "AVATAR collection after Boolean refutation does not require the reclaimed FO node zero",
      fun () ->
        let theory =
          Tptp.parse
            "fof(old,axiom,p(a)). fof(stronger,axiom,(![X]:p(X))). fof(choice,axiom,(q|r)). \
             fof(nq,axiom,~q). fof(nr,axiom,~r)."
        in
        let engine =
          Engine.create
            {
              engine_config with
              backward_subsumption = true;
              collect_every = 1;
              collect_adaptive = false;
            }
        in
        (* Keep this fixture on the conditional AVATAR certificate path. *)
        Ground_boolean.release engine.ground_boolean;
        add engine theory 0;
        add engine theory 1;
        Engine.finish engine;
        Engine.collect engine;
        check
          (try
             ignore (Proof.get engine.proof 0);
             false
           with Not_found -> true)
          "fixture did not reclaim the unrelated first FO clause";
        let choice = Proof.length engine.proof in
        add engine theory 2;
        (* Isolate the Boolean path: joint unit resolution can now close the
           preserved global disjunction before the SAT branch is needed. *)
        Avatar.offer_split (avatar engine) ~guard:(fun () -> ()) (Proof.get engine.proof choice);
        Engine.split_step engine (avatar engine);
        Engine.deactivate engine choice;
        List.iter (add engine theory) [ 3; 4 ];
        Engine.finish engine;
        check (avatar engine).unsat "fixture did not close through SAT";
        Engine.collect engine;
        ignore (checked theory engine) );
    ( "AVATAR resumes a saturated consistent branch when another axiom is added",
      fun () ->
        let theory = Tptp.parse "fof(choice,axiom,(p|q)). fof(nq,axiom,~q). fof(np,axiom,~p)." in
        let engine = Engine.create engine_config in
        List.iter (add engine theory) [ 0; 1 ];
        Engine.finish engine;
        no_refutation engine;
        let previous_elapsed = Engine.elapsed engine in
        check (Option.is_some engine.finished) "initial saturation was not sealed";
        add engine theory 2;
        equal engine.finished None "resumed search retained its old finish time";
        check
          (Engine.has_work engine || engine.root <> None)
          "new axiom neither resumed nor closed work";
        Engine.finish engine;
        check
          (Option.is_some engine.finished && Engine.elapsed engine >= previous_elapsed)
          "resumed search did not update its completion measurement";
        ignore (checked theory engine) );
    ( "collection of the dropped nodes leaves the duplicate tables as the full filter does",
      fun () ->
        (* Random clauses remembered (some only as explanations, some exact or alpha copies of
           others) and random sweeps; one state is collected with the store as [keep], the other
           from the dropped ids; entries and both duplicate tables must agree binding for binding
           in table order. *)
        let rng = Random.State.make [| 5; 2026; 18 |] in
        let pick xs = List.nth xs (Random.State.int rng (List.length xs)) in
        let clause () =
          List.init
            (1 + Random.State.int rng 2)
            (fun _ ->
              let arg () =
                pick [ V (0, Random.State.int rng 2); Fn (Original (pick [ "a"; "b" ]), []) ]
              in
              (if Random.State.bool rng then positive else negative)
                (P (pick [ "p"; "q" ], [ arg () ])))
          |> Clause.normalize
        in
        List.iter
          (fun variants ->
            for _ = 1 to 100 do
              let full = Avatar.create () and quick = Avatar.create () in
              let stored = Hashtbl.create 64 and next = ref 0 in
              for _ = 1 to 12 do
                for _ = 1 to Random.State.int rng 15 do
                  let step = { id = !next; clause = clause (); rule = Input (0, !next) } in
                  incr next;
                  Hashtbl.replace stored step.id ();
                  if Random.State.int rng 5 = 0 then (
                    ignore (Avatar.remember_explanation full ~support:[] step);
                    ignore (Avatar.remember_explanation quick ~support:[] step))
                  else (
                    ignore (Avatar.remember full ~variants step);
                    ignore (Avatar.remember quick ~variants step))
                done;
                let dropped = ref [] in
                Hashtbl.filter_map_inplace
                  (fun id () ->
                    if Random.State.int rng 3 = 0 then (
                      dropped := id :: !dropped;
                      None)
                    else Some ())
                  stored;
                Avatar.collect full ~keep:(Hashtbl.mem stored);
                Avatar.collect_dropped quick !dropped;
                let order fold table = fold (fun k v acc -> (k, v) :: acc) table [] in
                equal
                  (List.map fst (order Tbl.Int.fold quick.entries))
                  (List.map fst (order Tbl.Int.fold full.entries))
                  "dropped collection changed the entries";
                equal
                  (order Avatar.Seen.fold quick.seen)
                  (order Avatar.Seen.fold full.seen)
                  "dropped collection changed the exact table";
                equal
                  (order Avatar.Variants.fold quick.variants)
                  (order Avatar.Variants.fold full.variants)
                  "dropped collection changed the variant table"
              done
            done)
          [ false; true ] );
    ( "collection prunes duplicate indices while preserving live exact and alpha matches",
      fun () ->
        List.iter
          (fun variants ->
            let state = Avatar.create () in
            let p v = [ positive (P ("p", [ V (1, v) ])) ] in
            let q c = [ positive (P ("q", [ Fn (Original c, []) ])) ] in
            let remember id clause =
              ignore (Avatar.remember state ~variants { id; clause; rule = Input (0, id) })
            in
            let duplicate clause =
              Avatar.duplicate state ~variants ~except:(-1) ~guard:(fun () -> ()) [] clause
            in
            List.iteri remember [ p 0; p 9; q "a"; q "b" ];
            Avatar.retire state 0;
            Avatar.collect state ~keep:(fun id -> id <> 1 && id <> 2);
            check (not (duplicate (p 9))) "removed candidate still suppressed a clause";
            check (not (duplicate (p 0))) "retired proof ancestor suppressed a clause";
            check (not (duplicate (q "a"))) "removed ground clause remained searchable";
            check (duplicate (q "b")) "collection lost a live exact match";
            remember 4 (p 3);
            Avatar.collect state ~keep:(fun id -> id >= 3);
            check (duplicate (p 3)) "later admission lost its exact match";
            equal (duplicate (p 7)) variants "collection changed alpha matching policy";
            Avatar.collect state ~keep:(fun _ -> false);
            equal (Avatar.Seen.length state.seen) 0 "empty exact buckets were retained";
            equal (Avatar.Variants.length state.variants) 0 "empty variant buckets were retained")
          [ false; true ] );
    ( "AVATAR model deltas ignore stale locks and collection preserves live dependencies",
      fun () ->
        let state = Avatar.create () in
        let guard () = () in
        List.iteri
          (fun id name ->
            let clause = [ positive (P (name, [])) ] in
            equal (Avatar.name state clause) id "unexpected component numbering";
            ignore (Avatar.remember state ~variants:false { id; clause; rule = Component id }))
          [ "r"; "p"; "q" ];
        List.iter
          (fun id ->
            ignore
              (Avatar.remember state ~variants:false
                 { id; clause = [ positive (P ("target", [])) ]; rule = Factor (0, 0, 0, []) }))
          [ 10; 11 ];
        List.iter
          (fun using -> check (Avatar.reduce state ~target:10 ~using) "failed to install a lock")
          [ 1; 2; 2 ];
        check (Avatar.reduce state ~target:11 ~using:2) "failed to install the obsolete lock";
        Avatar.retire state 11;
        let update clause =
          Avatar.constraint_ state ~guard (Boolean.Split 0) clause;
          let changed = Avatar.solve state ~guard in
          let entries = Avatar.affected_entries state ~guard changed in
          Avatar.unlock state ~guard entries;
          (changed, List.map (fun (e : Avatar.entry) -> e.step.id) entries)
        in
        equal
          (update [ 1; 3 ])
          ([ 2 ], [ 2; 10 ])
          "initial model did not deduplicate live lock dependencies";
        equal (update [ 2 ]) ([ 1 ], [ 1 ]) "a replaced lock caused unrelated branch work";
        equal (Tbl.Int.find state.entries 10).lock
          (Some ([ 2 ], [ 2 ]))
          "an obsolete lock condition unlocked the current one";
        Avatar.collect state ~keep:(fun id -> id <> 11);
        equal (update [ -3 ])
          ([ 0; 2 ], [ 0; 2; 10 ])
          "collection lost support or current-lock dependencies";
        equal (Tbl.Int.find state.entries 10).lock None "the changed live lock was not released";
        equal state.unlocked 1 "a duplicated lock posting caused repeated unlocking";
        equal state.model_examined 6 "model work counted unaffected or duplicate entries";
        ignore (Avatar.name state [ positive (P ("unused", [])) ]);
        equal (Avatar.solve state ~guard) [] "a new false component changed branch membership" );
    ( "AVATAR stable models skip old clauses while later axioms still switch branches",
      fun () ->
        let unrelated =
          List.init 100 (fun i -> Printf.sprintf "fof(u%d,axiom,unrelated(c%d))." i i)
        in
        let theory =
          Tptp.parse
            (String.concat " "
               (unrelated
               @ [
                   "fof(choice,axiom,(p|q)).";
                   "fof(weaker,axiom,(p|q|r)).";
                   "fof(later,axiom,later).";
                   "fof(nq,axiom,~q).";
                   "fof(np,axiom,~p).";
                 ]))
        in
        let engine = Engine.create { engine_config with subsumption = false } in
        List.iter (add engine theory) (List.init 101 Fun.id);
        Engine.finish engine;
        no_refutation engine;
        let state = avatar engine in
        let old_model = Array.copy state.model in
        let old_examined = state.model_examined in
        let old_calls = state.sat_calls in
        let q = Tbl.Clause.find state.names [ positive (P ("q", [])) ] in
        check state.model.(q) "fixture did not start on q";
        let old_node = Option.get (Tbl.Int.find state.components q).node in
        add engine theory 101;
        Engine.finish engine;
        no_refutation engine;
        check (state.sat_calls > old_calls) "new constraint was not solved";
        equal
          (Array.sub state.model 0 (Array.length old_model))
          old_model "the already satisfied constraint unexpectedly changed the old model";
        check (Array.length state.model > Array.length old_model) "fixture did not add a component";
        equal state.model_examined old_examined "unchanged branch rescanned existing clauses";
        add engine theory 102;
        Engine.finish engine;
        check
          (List.exists
             (fun (s : step) -> s.clause = [ positive (P ("later", [])) ])
             (Index.all engine.index))
          "an unconditional late axiom waited for a model change";
        Engine.collect engine;
        add engine theory 103;
        Engine.finish engine;
        no_refutation engine;
        check (not state.model.(q)) "the refuted component remained selected";
        absent_from_indices engine old_node;
        let examined = state.model_examined - old_examined in
        check (examined > 0 && examined < 10) "a branch change scanned the unrelated global clauses";
        add engine theory 104;
        Engine.finish engine;
        ignore (checked theory engine) );
    ( "AVATAR on and off agree on finite satisfiable and refutable fixtures",
      fun () ->
        List.iter
          (fun (problem, refutable) ->
            let theory = Tptp.parse problem in
            List.iter
              (fun enabled ->
                let engine = run_engine ~settings:{ engine_config with avatar = enabled } theory in
                if refutable then ignore (checked theory engine) else no_refutation engine)
              [ false; true ])
          [
            (ground_four, true);
            (non_ground, true);
            ("fof(c,axiom,(p|q)). fof(n,axiom,~q).", false);
            ("fof(c,axiom,(![X]:(p(X)|q(X)))). fof(p,axiom,~p(a)). fof(q,axiom,~q(b)).", false);
          ] );
    ( "AVATAR cancellation and bounds leave no global proof or active inference",
      fun () ->
        let theory = Tptp.parse "fof(choice,axiom,(p|q))." in
        let cancel = ref false in
        let engine = Engine.create ~cancelled:(fun () -> !cancel) engine_config in
        add engine theory 0;
        cancel := true;
        Engine.finish engine;
        equal engine.stopped (Some "cancelled") "SAT work ignored cancellation";
        equal engine.root None "cancelled branch became a refutation";
        check
          ((not engine.busy) && Unify.mark engine.calculus.unifier = 0)
          "cancel left inference state live";
        List.iter
          (fun limits ->
            let limited =
              (* This checks the selection budget of the AVATAR path; the
                 ground bridge can close without selecting any given clause. *)
              run_engine ~bridge:false ~settings:{ engine_config with limits }
                (Tptp.parse ground_four)
            in
            check (Option.is_some limited.stopped) "bound did not stop search";
            equal limited.root None "bounded search reported a refutation";
            check
              (Proof.stored limited.proof + Boolean.proof_size (avatar limited).solver
              <= limits.max_retained)
              (Printf.sprintf "combined proof bound exceeded: FO=%d SAT=%d limit=%d"
                 (Proof.stored limited.proof)
                 (Boolean.proof_size (avatar limited).solver)
                 limits.max_retained))
          [
            { engine_config.limits with max_given = 0 };
            { engine_config.limits with max_generated = 1 };
            { engine_config.limits with max_retained = 4 };
          ];
        for maximum = 1 to 28 do
          let theory = Tptp.parse ground_four in
          let settings =
            { engine_config with limits = { engine_config.limits with max_retained = maximum } }
          in
          let limited = run_engine ~settings theory in
          check
            (Proof.stored limited.proof + Boolean.proof_size (avatar limited).solver <= maximum)
            (Printf.sprintf "proof allocation crossed the boundary at %d nodes" maximum);
          if limited.root <> None then ignore (checked theory limited)
          else
            check (Option.is_some limited.stopped) "bounded ground contradiction stopped silently"
        done );
    ( "AVATAR reactivation leaves one current resolution and equality posting generation",
      fun () ->
        let index = Index.create () and equalities = Equality_index.create () in
        let f = Fn (Original "f", [ constant "a" ]) and g = Fn (Original "g", [ constant "a" ]) in
        let step =
          {
            id = 7;
            clause = [ positive (p [ f ]); positive (P ("q", [ g ])) ];
            rule = Input (0, 0);
          }
        in
        let equation =
          {
            id = 8;
            clause = [ positive (E (f, constant "a")); positive (E (g, constant "a")) ];
            rule = Input (0, 0);
          }
        in
        for cycle = 0 to 39 do
          Index.remove index step.id;
          Equality_index.remove equalities equation.id;
          equal (Index.all index) [] "inactive clause remains in the brute resolution index";
          let selected = cycle mod 2 in
          Index.add ~eligible:(( = ) selected) index step;
          Equality_index.add ~eligible:(( = ) selected) equalities equation;
          equal
            (List.map (fun (s : step) -> s.id) (Index.all index))
            [ step.id ] "reactivation duplicated Index.all";
          let old = if selected = 0 then negative (P ("q", [ g ])) else negative (p [ f ]) in
          equal (Index.matches index [ old ]) []
            "an obsolete selected literal became eligible again";
          let visits = ref 0 in
          Equality_index.query equalities equalities.targets ~variables:false f (fun _ ->
              incr visits);
          equal !visits 1 "reactivation duplicated equality target candidates";
          let old_term = if selected = 0 then g else f in
          let visits = ref 0 in
          Equality_index.query ~inference:true equalities equalities.sources ~variables:false
            old_term (fun _ -> incr visits);
          equal !visits 0 "obsolete equality source eligibility was revived";
          let _, work, exhausted =
            Index.lookahead index ~budget:2 [ negative (p [ f ]); negative (P ("q", [ g ])) ]
          in
          equal (work, exhausted) (1, 0) "old generations consumed the lookahead budget"
        done;
        Index.compact index;
        Equality_index.compact equalities;
        equal (List.length (Index.all index)) 1 "compaction lost current generation" );
    ( "AVATAR reactivation does not retry obsolete demodulation generations",
      fun () ->
        let rewriter = Demodulation.create () in
        (* f(X, X) = X: its left side has the target's shape, so every candidate rule reaches a
           matching attempt (one guard call each), which fails on the repeated variable. A rule
           whose shape differs is passed over without an attempt (Subsumption.matchable). *)
        let step =
          {
            id = 9;
            rule = Input (0, 0);
            clause = [ positive (E (Fn (Original "f", [ v 0; v 0 ]), v 0)) ];
          }
        in
        let target =
          {
            id = 10;
            rule = Input (1, 0);
            clause = [ positive (p [ Fn (Original "f", [ constant "a"; constant "b" ]) ]) ];
          }
        in
        for _ = 0 to 39 do
          Demodulation.remove rewriter step.id;
          equal (Demodulation.rewrite_once rewriter target) None "inactive rewrite rule survived";
          Demodulation.add rewriter step;
          let attempts = ref 0 in
          equal
            (Demodulation.rewrite_once ~guard:(fun () -> incr attempts) rewriter target)
            None "non-linear rule incorrectly matched distinct constants";
          equal !attempts 1 "obsolete generations were retried as rewrite candidates"
        done;
        Demodulation.compact rewriter;
        let concrete =
          {
            target with
            clause = [ positive (p [ Fn (Original "f", [ constant "a"; constant "a" ]) ]) ];
          }
        in
        check
          (Option.is_some (Demodulation.rewrite_once rewriter concrete))
          "current rewrite generation was lost" );
  ]

let () = run tests
