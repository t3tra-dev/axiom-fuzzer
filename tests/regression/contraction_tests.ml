open Axiom_fuzzer
open Test_support
open Wire

let step id clause = { id; clause = Clause.normalize clause; rule = Input (id, 0) }
let guard () = ()
let find t s = Contraction.find ~guard t s
let f x = Fn (Original "f", [ x ])
let q x = P ("q", [ x ])

(* The goal's literal r(f(a)) exceeds ~p(a), so rewriting q(f(a)) to p(a) retires a goal that is
   larger than its inverse instance q(f(a)) | ~p(a): a redundancy deletion. nr follows the goal, so
   the unit ~r(f(a)) cannot first shrink the goal to a unit, which is never rewritten. *)
let text prefix =
  Printf.sprintf
    "cnf(forward,axiom,(%sp(X)|~%sq(f(X)))). cnf(inverse,axiom,(~%sp(Y)|%sq(f(Y)))). \
     cnf(np,axiom,~%sp(a)). cnf(goal,axiom,(%sq(f(a))|r(f(a)))). cnf(nr,axiom,~r(f(a)))."
    prefix prefix prefix prefix prefix prefix

(* Tests that depend on the equivalence rule select it, whatever the default. *)
let prove ?on_clause ?(equivalence = Contraction.Redundant) input =
  let theory = Tptp.parse input in
  let engine =
    Engine.create ?on_clause { Engine.default_config with avatar = false; equivalence }
  in
  List.iter (Engine.add_axiom engine) (Theory.fixed theory);
  Engine.finish engine;
  Engine.collect engine;
  let cert = Option.get (Engine.certificate engine ~theory:(Theory.name theory)) in
  (match Kernel.check theory cert with Ok _ -> () | Error e -> failwith e);
  (theory, engine, cert)

let tests =
  [
    ( "costly work retains a service opportunity amid cheap ready work",
      fun () ->
        let open Directions.Schedule in
        let t = create () in
        for _ = 1 to 120 do
          let job = Option.get (choose t [ Continue; First; Demand ]) in
          charge t job (if job = Continue then 1000000 else 1)
        done;
        Array.iter (fun lane -> check (lane.runs >= 4) "a ready work class starved") t.lanes;
        check (t.lanes.(2).runs < t.lanes.(0).runs) "expensive slices were counted as cheap calls"
    );
    ( "a full continuation queue still permits new premise selection",
      fun () ->
        let theory = Tptp.parse "cnf(p,axiom,p(a)). cnf(q,axiom,q(a))." in
        let e = Engine.create { Engine.default_config with avatar = false } in
        List.iter (Engine.add_axiom e) (Theory.fixed theory);
        let ticket = (0, Tbl.Int.find e.retained_index.live 0) in
        for _ = 1 to 40 do
          Queue.add
            {
              Directions.owner = ticket;
              groups = Seq.empty;
              current = Some ([ ticket ], Seq.repeat (fun _ -> ()));
            }
            e.pending
        done;
        (* Exercise the public scheduler: Goal work runs in its own service. *)
        for _ = 1 to 160 do
          Engine.step e
        done;
        check (Index.mem e.index 1) "pending work blocked all new givens";
        check (e.goals.metrics.first_trials >= 2) "pending work blocked first trials";
        equal e.root None "work scheduling invented a contradiction" );
    ( "incremental index snapshots exclude late insertions and stale premises",
      fun () ->
        let index = Index.create () and equality = Equality_index.create () in
        let initial =
          step 0
            [ positive (p [ f (constant "a") ]); positive (E (f (constant "a"), constant "b")) ]
        in
        let later = { initial with id = 1 } in
        Index.add index initial;
        Equality_index.add equality initial;
        let generation = index.generation in
        let clause = [ negative (p [ f (constant "a") ]) ] in
        let res = Index.cursor index clause
        and eq = Equality_index.cursor equality ~variables:false clause in
        Index.add index later;
        Equality_index.add equality later;
        let ids xs =
          xs |> Seq.filter_map Fun.id
          |> Seq.map (fun ((s : step), _) -> s.id)
          |> List.of_seq |> List.sort_uniq compare
        in
        equal (ids res) [ 0 ] "snapshot included a later premise";
        equal
          (ids (Index.cursor ~since:generation index clause))
          [ 1 ] "delta repeated old resolution work";
        (* Pause after an equality posting but before its occurrence pairs. *)
        let rest =
          match eq () with
          | Seq.Nil -> failwith "missing equality posting"
          | Seq.Cons (_, rest) -> rest
        in
        Equality_index.remove equality 0;
        Equality_index.compact equality;
        check
          (Seq.is_empty (Seq.filter_map Fun.id rest))
          "suspended position pairs revived a retired premise";
        let eq_ids =
          Equality_index.cursor ~since:generation equality ~variables:false clause
          |> Seq.filter_map Fun.id
          |> Seq.map (fun ((s : step), _, _) -> s.id)
          |> List.of_seq |> List.sort_uniq compare
        in
        equal eq_ids [ 1 ] "equality delta lost the new premise" );
    ( "bounded alternative equality preserves selection and cursors and produces a checked \
       refutation",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(g,axiom,(~p(a)|q(f(a)))). cnf(e,axiom,f(a)=b). cnf(p,axiom,p(a)). \
             cnf(n,axiom,~q(b))."
        in
        let e =
          Engine.create
            {
              Engine.default_config with
              avatar = false;
              subsumption = false;
              demodulation = false;
              backward_demodulation = false;
            }
        in
        let axioms = Theory.fixed theory in
        List.iteri (fun i a -> if i < 2 then Engine.add_axiom e a) axioms;
        let target = Proof.get e.proof 0 and side = Proof.get e.proof 1 in
        let negative = List.find_index (fun l -> not l.positive) target.clause |> Option.get in
        Tbl.Int.replace e.calculus.selected 0 (Some [ negative ]);
        Engine.activate e side;
        Engine.activate e target;
        let old = Engine.prepare_inferences e target in
        (Tbl.Int.find e.directions.entries 0).seen <- -32;
        e.metrics.inference_ordinary_batches <- 15;
        let work = Option.get (Engine.revisit_direction e) in
        check
          (Engine.current_ticket e old.owner)
          "selection extension invalidated retained premises";
        let chosen = Option.get (Calculus.selected e.calculus target) in
        equal chosen [ negative ] "bounded retry changed the ordinary selection";
        Engine.protect (fun () -> Engine.process_inference e work);
        check (e.directions.useful > 0) "probed equality produced no retained consequence";
        List.iteri (fun i a -> if i >= 2 then Engine.add_axiom e a) axioms;
        Engine.finish e;
        Engine.collect e;
        let cert = Option.get (Engine.certificate e ~theory:(Theory.name theory)) in
        (match Kernel.check theory cert with Ok _ -> () | Error err -> failwith err);
        check
          (List.exists
             (fun s -> match s.rule with Paramodulate _ -> true | _ -> false)
             cert.steps)
          "refutation bypassed equality" );
    ( "direction probes see equality connections and reject duplicate conclusions",
      fun () ->
        let index = Index.create () and equations = Equality_index.create () in
        let source = step 1 [ positive (E (f (constant "a"), constant "b")) ] in
        Index.add index source;
        Equality_index.add equations source;
        let target = step 0 [ negative (p [ constant "a" ]); positive (q (f (constant "a"))) ] in
        let pivot = List.find_index (fun l -> l.positive) target.clause |> Option.get in
        let calc = Calculus.create ~ordered:true (Term.create ()) and d = Directions.create () in
        let before = Calculus.selected calc target in
        let choose fresh =
          Directions.choose d ~guard ~calculus:calc ~index ~equalities:equations ~fresh target 0
          |> Option.map (fun p -> p.Directions.pivot)
        in
        equal (choose (fun _ _ -> true)) (Some pivot) "equality-only connection was invisible";
        equal (choose (fun _ _ -> false)) None "duplicate output was counted as progress";
        equal (Calculus.selected calc target) before "probe mutated production selection";
        check (d.probes > 0) "no primitive inference was sampled" );
    ( "direction retries wait for knowledge and do not revive stale generations",
      fun () ->
        let d = Directions.create () and calc = Calculus.create ~ordered:true (Term.create ()) in
        let index = Index.create () and equations = Equality_index.create () in
        let target = step 0 [ negative (p [ constant "a" ]); positive (q (f (constant "a"))) ] in
        let side = step 1 [ positive (E (f (constant "a"), constant "b")) ] in
        Equality_index.add equations side;
        Directions.register d ~epoch:0 (0, 1);
        let next epoch alive =
          Directions.next d ~guard ~epoch ~alive
            ~get:(fun _ -> target)
            ~calculus:calc ~index ~equalities:equations
            ~fresh:(fun _ _ -> true)
        in
        equal (next 1 (fun _ -> true)) None "unchanged knowledge was rescanned";
        check (Option.is_some (next 16 (fun _ -> true))) "new equality did not enable retry";
        Directions.compact d ~alive:(fun _ -> false);
        equal (next 1000 (fun _ -> false)) None "stale selection survived collection" );
    ( "calculus reports failed matching and ordering without emitting a proof",
      fun () ->
        let c = Calculus.create ~ordered:true ~selection:false (Term.create ()) in
        let seen = ref [] in
        c.observe <- Some (fun stage _ -> seen := stage :: !seen);
        let left = step 0 [ positive (p [ constant "a" ]) ] in
        Calculus.resolve c left
          (step 1 [ negative (p [ constant "b" ]) ])
          (fun _ _ -> failwith "false match");
        check (List.mem "unification_rejected" !seen) "failed matching was not observed";
        let target =
          {
            id = 2;
            rule = Input (2, 0);
            clause = [ negative (p [ constant "a" ]); positive (q (f (constant "a"))) ];
          }
        in
        Calculus.resolve c left target (fun _ _ -> failwith "nonmaximal pivot was used");
        check (List.mem "ordering_rejected" !seen) "ordering rejection was not observed" );
    ( "retained units delete literals with a rigid target and replayable scopes",
      fun () ->
        let t = Contraction.create () in
        Contraction.add t (step 0 [ negative (p [ constant "a" ]) ]);
        equal
          (find t (step 1 [ positive (p [ v 0 ]) ]))
          None "ground unit specialized a universal target";
        Contraction.add t (step 2 [ negative (p [ v 0 ]) ]);
        let reduced = Option.get (find t (step 3 [ positive (p [ v 1 ]); positive (q (v 1)) ])) in
        equal (Clause.normalize reduced.clause) [ positive (q (v 0)) ] "wrong deleted literal";
        equal reduced.using [ 2 ] "wrong simplifying premise";
        check
          (List.for_all
             (fun ((scope, _), _) -> scope = 1)
             (match reduced.rule with Resolve (_, _, _, _, s) -> s | _ -> assert false))
          "unit reduction substituted the target";
        Contraction.remove t 2;
        Contraction.compact t;
        equal (find t (step 4 [ positive (p [ v 0 ]) ])) None "deleted unit remained usable" );
    ( "binary rewriting requires a genuine equivalence, a strict decrease and a smaller inverse \
       instance",
      fun () ->
        let t = Contraction.create ~equivalence:Contraction.Redundant () in
        let side = step 0 [ positive (p [ v 0 ]); negative (q (f (v 0))) ] in
        let large = positive (P ("r", [ f (f (constant "a")) ])) in
        let target = step 2 [ positive (q (f (constant "a"))); large ] in
        Contraction.add t side;
        equal (find t target) None "one implication was treated as an equivalence";
        Contraction.add t (step 1 [ negative (p [ v 8 ]); positive (q (f (v 8))) ]);
        let result = Option.get (find t target) in
        equal (Clause.normalize result.clause)
          (Clause.normalize [ positive (p [ constant "a" ]); large ])
          "literal was not rewritten";
        equal (List.sort compare result.using) [ 0; 1 ]
          "inverse premise missing from redundancy support";
        equal (find t (step 3 result.clause)) None "rewrite could cycle";
        (* The target follows from the result and the inverse instance q(f(a)) | ~p(a). Retiring
           it is a redundancy deletion only because r(f(f(a))) exceeds ~p(a), which makes that
           instance smaller than the target. A smaller second literal, or none, does not: the
           legacy rule rewrote the unit q(f(a)) here and so deleted a clause whose inferences the
           inverse (with ~p(a) selected) can never restore. *)
        equal
          (find t (step 4 [ positive (q (f (constant "a"))); positive (P ("s", [])) ]))
          None "a target smaller than its inverse instance was retired";
        equal
          (find t (step 5 [ positive (q (f (constant "a"))) ]))
          None "a unit target was retired by an equivalence";
        equal t.literal_justified t.literal_rewritten "an unjustified rewrite was counted";
        Contraction.remove t 1;
        Contraction.compact t;
        equal (find t target) None "retired inverse still authorized rewriting";
        Contraction.add t (step 1 [ negative (p [ v 8 ]); positive (q (f (v 8))) ]);
        check (Option.is_some (find t target)) "reactivated inverse was not indexed" );
    ( "the cached complement and variant key of a binary side equal recomputed ones",
      fun () ->
        let t = Contraction.create () in
        let sides =
          [
            step 0 [ positive (p [ v 0 ]); negative (q (f (v 0))) ];
            step 1 [ negative (p [ v 8 ]); positive (q (f (v 8))) ];
            step 2 [ positive (E (f (v 0), v 1)); negative (P ("p", [ v 1; v 0 ])) ];
            step 3 [ negative (E (v 2, f (v 2))); positive (q (constant "a")) ];
          ]
        in
        List.iter (Contraction.add t) sides;
        Contraction.add t (step 4 [ negative (p [ constant "a" ]) ]);
        check (not (Tbl.Int.mem t.inverse 4)) "a unit side got a binary inverse key";
        List.iter
          (fun (s : step) ->
            let cached = Tbl.Int.find t.inverse s.id in
            equal cached.opposite (Contraction.complement s.clause) "cached complement differs";
            equal cached.opposite_key.value
              (Variant_index.key (Contraction.complement s.clause))
              "cached variant key differs";
            equal cached.opposite_key.hash
              (Tbl.Hash.clause_ints (Variant_index.key (Contraction.complement s.clause)))
              "cached variant key hash differs")
          sides;
        let target =
          step 9 [ positive (q (f (constant "a"))); positive (P ("r", [ f (f (constant "a")) ])) ]
        in
        let cached = find t target in
        check (Option.is_some cached) "the equivalence did not rewrite the target";
        Contraction.remove t 1;
        check (not (Tbl.Int.mem t.inverse 1)) "a removed side kept its cached key";
        Contraction.compact t;
        equal (find t target) None "a removed inverse authorized rewriting";
        Contraction.add t (step 1 [ negative (p [ v 8 ]); positive (q (f (v 8))) ]);
        equal (find t target) cached "re-adding the inverse changed the contraction" );
    ( "classes, the skip and the variant cache answer as the reference contraction (random sides)",
      fun () ->
        (* Two Contractions and the reference (Contraction_reference) take the same random
           adds (fresh ids, and stored or removed steps added again, as proof ids keep their
           clause), removals and compactions of units and binary sides over a few symbols, with
           complementary pairs; every 500 rounds all clauses are removed, so the counts drain and
           the complements come back one at a time. Every target (fresh, or a stored clause under its own id) is searched with
           random budgets: the full query (~skip:false) must give the reference's answers, trials and
           exhaustions, and the skipping one the reference's answers. After every operation each
           class's ids equal the reference's [equivalents] entry, each side holds the class of its complement's
           key, is counted exactly while that class has ids, and [partnered] equals the count
           recomputed from the counted sides. *)
        let rng = Random.State.make [| 9; 2026; 11; 19 |] in
        let pick xs = List.nth xs (Random.State.int rng (List.length xs)) in
        let arg () = pick [ constant "a"; constant "b"; f (v 0); v 0; f (constant "a") ] in
        let atom () =
          match Random.State.int rng 7 with
          | 0 -> E (arg (), arg ())
          | _ -> P (pick [ "p"; "q"; "r"; "s"; "t"; "u"; "w"; "z" ], [ arg () ])
        in
        let lit () = if Random.State.bool rng then positive (atom ()) else negative (atom ()) in
        let sides = Array.init 24 (fun _ -> [ lit (); lit () ]) in
        let clause () =
          match Random.State.int rng 8 with
          | 0 | 1 -> [ lit () ]
          | 2 -> Contraction.complement sides.(Random.State.int rng (Array.length sides))
          | 3 | 4 -> sides.(Random.State.int rng (Array.length sides))
          | _ -> [ lit (); lit () ]
        in
        let invariant (t : Contraction.t) (r : Contraction_reference.t) =
          Contraction_reference.Keys.iter
            (fun k ids ->
              equal
                (Contraction.equivalents t (Contraction.key k.value))
                ids "a class's ids differ from the reference's equivalents entry")
            r.equivalents;
          Contraction.Keys.iter
            (fun k (c : Contraction.klass) ->
              if c.ids <> [] then
                check
                  (Contraction_reference.Keys.mem r.equivalents (Contraction_reference.key k.value))
                  "a class has ids that the reference's equivalents lacks")
            t.classes;
          let expected = Tbl.Feature.create 16 in
          Tbl.Int.iter
            (fun _ (side : Contraction.side) ->
              check
                (Contraction.Keys.find_opt t.classes side.opposite_key == Some side.opp
                ||
                match Contraction.Keys.find_opt t.classes side.opposite_key with
                | Some c -> c == side.opp
                | None -> false)
                "a side does not hold the class of its complement's key";
              equal side.counted (side.opp.ids <> [])
                "a side is counted without (or not counted with) inverse candidates";
              if side.counted then
                List.iter
                  (fun f ->
                    Tbl.Feature.replace expected f
                      (1 + Option.value ~default:0 (Tbl.Feature.find_opt expected f)))
                  side.features)
            t.inverse;
          equal (Tbl.Feature.length expected) (Tbl.Feature.length t.partnered)
            "partnered keys differ from the counted sides";
          Tbl.Feature.iter
            (fun f n ->
              equal
                (Tbl.Feature.find_opt t.partnered f)
                (Some n) "a partnered count differs from the counted sides")
            expected
        in
        let main (r : Contraction_reference.result option) =
          Option.map (fun (r : Contraction_reference.result) -> (r.clause, r.rule, r.using)) r
        and ours (r : Contraction.result option) =
          Option.map (fun (r : Contraction.result) -> (r.clause, r.rule, r.using)) r
        in
        List.iter
          (fun (equivalence, reference) ->
            let fast = Contraction.create ~equivalence ()
            and full = Contraction.create ~equivalence ()
            and old = Contraction_reference.create ~equivalence:reference () in
            let live = Hashtbl.create 64 and known = Hashtbl.create 64 in
            let found = ref 0 and none = ref 0 and next = ref 0 in
            let all f =
              f fast;
              f full
            in
            for round = 1 to 5000 do
              (* A known id (one of the last 64 made) or a fresh one. *)
              let id =
                if !next > 0 && Random.State.int rng 3 > 0 then
                  max 0 (!next - 1 - Random.State.int rng 64)
                else (
                  incr next;
                  !next - 1)
              in
              let s =
                match Hashtbl.find_opt known id with
                | Some s -> s
                | None ->
                    let s = step id (clause ()) in
                    Hashtbl.replace known id s;
                    s
              in
              if round mod 500 = 0 then (
                Hashtbl.iter
                  (fun id _ ->
                    all (fun t -> Contraction.remove t id);
                    Contraction_reference.remove old id)
                  live;
                Hashtbl.reset live;
                all Contraction.compact;
                Contraction_reference.compact old);
              (match Random.State.int rng 7 with
              | 0 | 1 ->
                  if Hashtbl.mem live id && Random.State.bool rng then (
                    all (fun t -> Contraction.remove t id);
                    Contraction_reference.remove old id);
                  all (fun t -> Contraction.add t s);
                  Contraction_reference.add old s;
                  Hashtbl.replace live id s
              | 2 ->
                  all (fun t -> Contraction.remove t id);
                  Contraction_reference.remove old id;
                  Hashtbl.remove live id
              | 3 ->
                  if round mod 5 = 0 then
                    if round mod 15 = 0 then (
                      all Contraction.compact_all;
                      Contraction_reference.compact_all old)
                    else (
                      all Contraction.compact;
                      Contraction_reference.compact old)
              | _ ->
                  let target =
                    match Hashtbl.find_opt live id with
                    | Some s when Random.State.bool rng -> s
                    | _ -> step (1_000_000 + round) (clause ())
                  in
                  let budget = pick [ 6; 40; 1024 ] in
                  let reference = main (Contraction_reference.find ~budget ~guard old target) in
                  equal
                    (ours (Contraction.find ~budget ~skip:false ~guard full target))
                    reference "a find differs from the reference's";
                  equal
                    (ours (Contraction.find ~budget ~guard fast target))
                    reference "a skipped find differs from the reference's";
                  let derived = main (Contraction_reference.derive ~budget ~guard old target) in
                  equal
                    (ours (Contraction.derive ~budget ~skip:false ~guard full target))
                    derived "a derive differs from the reference's";
                  equal
                    (ours (Contraction.derive ~budget ~guard fast target))
                    derived "a skipped derive differs from the reference's";
                  equal (full.trials, full.exhausted) (old.trials, old.exhausted)
                    "the full query's trials or exhaustions differ from the reference's";
                  if reference = None && derived = None then incr none else incr found);
              invariant fast old;
              invariant full old
            done;
            check (fast.skipped > 200) "the skip was not exercised";
            check (!found > 50 && !none > 200) "the queries did not exercise both answers";
            equal full.skipped 0 "the reference skipped a query")
          [
            (Contraction.Derive, Contraction_reference.Derive);
            (Contraction.Redundant, Contraction_reference.Redundant);
            (Contraction.Legacy, Contraction_reference.Legacy);
          ] );
    ( "the derive variant keeps the target and offers the legacy rewrite as a consequence",
      fun () ->
        let side = [ positive (p [ v 0 ]); negative (q (f (v 0))) ] in
        let unit = step 2 [ positive (q (f (constant "a"))) ] in
        let large = positive (P ("r", [ f (f (constant "a")) ])) in
        let justified = step 3 [ positive (q (f (constant "a"))); large ] in
        let make equivalence =
          let t = Contraction.create ~equivalence () in
          Contraction.add t (step 0 side);
          Contraction.add t (step 1 (Contraction.complement side));
          t
        in
        List.iter
          (fun equivalence ->
            equal
              (Contraction.derive ~guard (make equivalence) unit)
              None "derive offered a consequence outside the derive variant")
          [ Contraction.Redundant; Contraction.Legacy ];
        let t = make Contraction.Derive in
        equal (find t unit) None "the derive variant retired a unit";
        (match Contraction.derive ~guard t unit with
        | Some { clause; using; rule = Resolve (0, _, 2, 0, _) } ->
            equal (Clause.normalize clause) [ positive (p [ constant "a" ]) ] "wrong consequence";
            equal using [ 0 ] "a consequence named a premise to retire"
        | _ -> failwith "the derive variant offered no consequence for the unit");
        check (Option.is_some (find t justified)) "the derive variant lost a justified rewrite";
        equal
          (Contraction.derive ~guard t justified)
          None "a justified rewrite was also offered as a consequence";
        equal t.literal_derived 1 "derived consequences were not counted";
        (* At admission the unit stays and p(a) is added beside it. *)
        let theory =
          Tptp.parse
            "cnf(forward,axiom,(p(X)|~q(f(X)))). cnf(inverse,axiom,(~p(Y)|q(f(Y)))). \
             cnf(unit,axiom,q(f(a)))."
        in
        let e =
          Engine.create
            { Engine.default_config with avatar = false; equivalence = Contraction.Derive }
        in
        List.iter (Engine.add_axiom e) (Theory.fixed theory);
        let retained =
          Tbl.Int.fold
            (fun id _ clauses -> (Proof.get e.proof id).clause :: clauses)
            e.retained_index.live []
        in
        check (List.mem [ positive (q (f (constant "a"))) ] retained) "the unit was retired";
        check (List.mem [ positive (p [ constant "a" ]) ] retained) "the consequence was not added";
        equal e.contraction.literal_rewritten 0 "the derive variant rewrote a unit" );
    ( "every clause an equivalence retires follows from smaller live clauses (random sets)",
      fun () ->
        (* Random small clause sets: equivalence pairs (a two-literal side and its complement), lone
           implications and units over a few symbols, and random targets, most of them holding an
           instance of a side literal's complement. For every binary rewrite of a target l | R
           into r | R, checked independently of Contraction's own test: the side and the inverse
           it names are live and have the instances ~l | r and l | ~r, so the target follows from
           the result and l | ~r; and at random ground instances of the rigid target, both r | R
           and l | ~r are smaller than l | R in the multiset extension of the literal order. A
           unit deletion leaves a proper subclause. The legacy rule, on the same sets and
           targets, offers rewrites that fail the order check (units among them), so the checks
           have teeth. *)
        let rng = Random.State.make [| 8; 2026; 11; 17 |] in
        let int n = Random.State.int rng n in
        let pick xs = List.nth xs (int (List.length xs)) in
        let fn s xs = Fn (Original s, xs) in
        let rec term vars depth =
          if depth = 0 || int 3 = 0 then
            if vars > 0 && Random.State.bool rng then V (0, int vars)
            else constant (pick [ "a"; "b" ])
          else
            match int 3 with
            | 0 -> fn "f" [ term vars (depth - 1) ]
            | 1 -> fn "g" [ term vars (depth - 1) ]
            | _ -> fn "h" [ term vars (depth - 1); term vars (depth - 1) ]
        in
        let atom vars =
          match int 6 with
          | 0 -> E (term vars 2, term vars 2)
          | 1 -> P ("r", [ term vars 1; term vars 1 ])
          | 2 -> P ("s", [])
          | 3 -> P ("p", [ term vars 2 ])
          | _ -> P ("q", [ term vars 2 ])
        in
        let literal vars = { positive = Random.State.bool rng; atom = atom vars } in
        let rec ground depth =
          if depth = 0 || int 2 = 0 then constant (pick [ "a"; "b" ])
          else fn (pick [ "f"; "g" ]) [ ground (depth - 1) ]
        in
        let instantiate (l : literal) =
          let theta = List.init 3 (fun i -> ((0, i), term 3 1)) in
          Clause.map_literal (Clause.map_vars (fun x -> List.assoc x theta)) l
        in
        let order = Ordering.standard in
        (* E (s, t) and E (t, s) are one literal. *)
        let canon (l : literal) =
          match l.atom with E (x, y) when compare x y > 0 -> { l with atom = E (y, x) } | _ -> l
        in
        let rec minus xs = function
          | [] -> xs
          | y :: ys -> (
              match List.find_index (( = ) y) xs with
              | Some i -> minus (List.filteri (fun k _ -> k <> i) xs) ys
              | None -> minus xs ys)
        in
        (* Dershowitz-Manna: xs < ys iff they differ and every literal of xs - ys is exceeded by a
           literal of ys - xs. *)
        let smaller xs ys =
          let xs = List.map canon xs and ys = List.map canon ys in
          let a = minus xs ys and b = minus ys xs in
          (a <> [] || b <> [])
          && List.for_all (fun x -> List.exists (fun y -> Ordering.literal_greater ~order y x) b) a
        in
        let flip (l : literal) = { l with positive = not l.positive } in
        (* Does the stored two-literal clause have the instance {x, y}? *)
        let instance (pattern : clause) (x : literal) (y : literal) =
          let matches env (a : literal) (b : literal) =
            if a.positive <> b.positive then []
            else
              let attempt target =
                try [ Subsumption.atom env a.atom target ] with Subsumption.No_match -> []
              in
              attempt b.atom @ match b.atom with E (s, u) -> attempt (E (u, s)) | _ -> []
          in
          match pattern with
          | [ a; b ] ->
              let both a b = List.exists (fun env -> matches env b y <> []) (matches [] a x) in
              both a b || both b a
          | _ -> false
        in
        let checked = ref 0 and units_deleted = ref 0 and legacy_bad = ref 0 in
        let legacy_units = ref 0 in
        for round = 1 to 400 do
          let redundant = Contraction.create ~equivalence:Contraction.Redundant () in
          let legacy = Contraction.create ~equivalence:Contraction.Legacy () in
          let add s =
            Contraction.add redundant s;
            Contraction.add legacy s
          in
          let id = ref 0 in
          let fresh clause =
            incr id;
            step !id clause
          in
          let sides =
            List.init
              (1 + int 3)
              (fun _ ->
                let vars = int 3 in
                let side = fresh [ literal vars; literal vars ] in
                add side;
                add (fresh (Contraction.complement side.clause));
                side.clause)
          in
          List.iter
            (fun _ -> add (fresh [ literal (int 3); literal (int 3) ]))
            (List.init (int 2) Fun.id);
          List.iter (fun _ -> add (fresh [ literal (int 2) ])) (List.init (int 3) Fun.id);
          for k = 1 to 20 do
            let others = List.init (int 3) (fun _ -> literal (int 3)) in
            let clause =
              if int 10 < 7 then flip (instantiate (pick (pick sides))) :: others
              else literal (int 3) :: others
            in
            let target = step (1000 + (100 * round) + k) clause in
            let ys = Clause.scope 2 target.clause in
            let verify (t : Contraction.t) (result : Contraction.result) =
              match (result.rule, result.using) with
              | Resolve (_, _, _, _, _), [ _ ] ->
                  equal
                    (List.length result.clause + 1)
                    (List.length ys) "a unit deletion did not leave a proper subclause";
                  incr units_deleted;
                  true
              | Resolve (side, _, _, j, _), [ side'; inverse ] ->
                  equal side side' "the rewrite names another side";
                  check
                    (Tbl.Int.mem t.steps side && Tbl.Int.mem t.steps inverse)
                    "a premise of the rewrite is not live";
                  let l = List.nth ys j and r = List.nth result.clause j in
                  let rest = Clause.remove j ys in
                  check
                    (instance (Tbl.Int.find t.steps side).clause (flip l) r)
                    "the side has no instance ~l | r";
                  check
                    (instance (Tbl.Int.find t.steps inverse).clause l (flip r))
                    "the inverse has no instance l | ~r";
                  equal (Clause.remove j result.clause) rest "the rewrite changed another literal";
                  if List.length ys = 1 then
                    if t.equivalence = Contraction.Legacy then incr legacy_units
                    else failwith "a unit target was rewritten";
                  List.for_all
                    (fun _ ->
                      let theta = List.map (fun x -> (x, ground 2)) (Wire.variables (r :: ys)) in
                      let g = Clause.map_literal (Clause.map_vars (fun x -> List.assoc x theta)) in
                      let target = List.map g ys in
                      smaller (List.map g (r :: rest)) target && smaller [ g l; g (flip r) ] target)
                    (List.init 4 Fun.id)
              | _ -> failwith "an unexpected contraction"
            in
            (match find redundant target with
            | Some result ->
                check (verify redundant result) "a retired clause is not smaller-redundant";
                incr checked
            | None -> ());
            match find legacy target with
            | Some result -> if not (verify legacy result) then incr legacy_bad
            | None -> ()
          done
        done;
        check (!checked - !units_deleted > 200) "too few rewrites were checked";
        check (!units_deleted > 50) "too few unit deletions were checked";
        check (!legacy_bad > 20 && !legacy_units > 10) "the legacy rule passed the redundancy check"
    );
    ( "inverse matching preserves shared variables and cannot invent RHS variables",
      fun () ->
        let t = Contraction.create () in
        Contraction.add t
          (step 0 [ positive (P ("p", [ v 0; v 1 ])); negative (P ("q", [ f (v 0); v 1 ])) ]);
        Contraction.add t
          (step 1 [ negative (P ("p", [ v 0; v 1 ])); positive (P ("q", [ f (v 1); v 0 ])) ]);
        (* The targets' second literal exceeds every replacement's complement, so only the
           checks under test can refuse the rewrites. *)
        let large = positive (P ("s", [ f (f (f (constant "a"))) ])) in
        equal
          (find t (step 2 [ positive (P ("q", [ f (constant "a"); constant "b" ])); large ]))
          None "an independently renamed literal was mistaken for an equivalence";
        let t = Contraction.create () in
        let side = [ positive (p [ v 1 ]); negative (q (f (v 0))) ] in
        Contraction.add t (step 0 side);
        Contraction.add t (step 1 (Contraction.complement side));
        equal
          (find t (step 2 [ positive (q (f (constant "a"))); large ]))
          None "rewrite introduced a variable absent from its pivot" );
    ( "contraction budget exhaustion and cancellation are harmless",
      fun () ->
        let t = Contraction.create () in
        Contraction.add t (step 0 [ negative (p [ v 0 ]) ]);
        let target = step 1 [ positive (p [ constant "a" ]) ] in
        equal (Contraction.find ~budget:0 ~guard t target) None "zero budget did work";
        equal t.exhausted 1 "exhaustion missing";
        let exception Cancelled in
        let cancelled =
          try
            ignore (Contraction.find ~guard:(fun () -> raise Cancelled) t target);
            false
          with Cancelled -> true
        in
        check cancelled "cancellation was swallowed";
        check (Option.is_some (find t target)) "cancelled query damaged the index" );
    ( "admission contraction produces a checked proof before any given-clause selection",
      fun () ->
        let _, engine, cert = prove (text "") in
        equal engine.metrics.given 0 "simplification waited for Active";
        check (engine.contraction.literal_rewritten > 0) "equivalence rewriting was not exercised";
        check (engine.contraction.unit_deleted >= 2) "known conditions were not deleted";
        check
          (List.exists (fun s -> match s.rule with Resolve _ -> true | _ -> false) cert.steps)
          "contraction did not emit ordinary proof rules" );
    ( "renaming and reversing inputs preserve contraction refutations",
      fun () ->
        List.iter
          (fun prefix ->
            let statements =
              String.split_on_char '.' (text prefix) |> List.filter (fun s -> String.trim s <> "")
            in
            List.iter
              (fun statements -> ignore (prove (String.concat "." statements ^ ".")))
              [ statements; List.rev statements ])
          [ "alpha_"; "renamed_" ] );
    ( "under the legacy rule, rewriting a unit to its complement closes before retirement and \
       duplicate elimination",
      fun () ->
        let _, e, cert =
          prove ~equivalence:Contraction.Legacy
            "cnf(d1,axiom,(~p(X,X)|p(X,a))). cnf(d2,axiom,(~p(X,a)|p(X,X))). \
             cnf(pos,axiom,(p(X,X)|p(X,b))). cnf(neg,axiom,(~p(X,X)|~p(X,b)))."
        in
        equal e.metrics.given 0 "a direct complementary rewrite waited for saturation";
        equal (List.length cert.axioms) 2 "unrelated equivalence entered the refutation";
        check (e.contraction.literal_rewritten > 0) "complementary rewrite was not exercised";
        check (e.contraction.literal_units > 0) "no unit was rewritten under the legacy rule" );
    ( "an equivalence never retires a unit, not even into its complement",
      fun () ->
        (* pos and neg make p(X,b) equivalent to ~p(X,X). The legacy rule rewrote the unit ~p(b,b)
           into p(b,b) and closed that pair through a special case, and it also rewrote the factor
           p(b,b) of pos into p(b,a) through d1/d2, deleting it. Neither unit is smaller than its
           inverse instance, so both stay; the kept factor p(b,b) then deletes the literal of the
           factor ~p(b,b) of neg, and the refutation still closes at admission. *)
        let pos = [ positive (P ("p", [ v 0; v 0 ])); positive (P ("p", [ v 0; constant "b" ])) ] in
        let t = Contraction.create ~equivalence:Contraction.Redundant () in
        Contraction.add t (step 0 pos);
        Contraction.add t (step 1 (Contraction.complement pos));
        equal
          (find t (step 2 [ negative (P ("p", [ constant "b"; constant "b" ])) ]))
          None "a unit was rewritten into its complement";
        let _, e, cert =
          prove
            "cnf(d1,axiom,(~p(X,X)|p(X,a))). cnf(d2,axiom,(~p(X,a)|p(X,X))). \
             cnf(pos,axiom,(p(X,X)|p(X,b))). cnf(neg,axiom,(~p(X,X)|~p(X,b)))."
        in
        equal e.metrics.given 0 "a direct complementary conflict waited for saturation";
        equal (List.length cert.axioms) 2 "unrelated equivalence entered the refutation";
        equal e.contraction.literal_rewritten 0 "a unit was retired by an equivalence" );
    ( "the legacy equivalence rule stays reachable only through its evaluation hook",
      fun () ->
        let hook value =
          (Eval.of_env (function "AXIOM_EQUIVALENCE" -> Some value | _ -> None)).config
            Scheduler.default_config
        in
        equal Scheduler.default_config.engine.equivalence Contraction.Derive
          "the default is not derive (it must retire only redundant targets and keep the others)";
        equal (Contraction.create ()).equivalence Contraction.Redundant
          "Contraction's default may retire non-redundant targets";
        equal (hook "redundant").engine.equivalence Contraction.Redundant
          "redundant was not selected";
        equal (hook " legacy ").engine.equivalence Contraction.Legacy "legacy was not selected";
        equal (hook "derive").engine.equivalence Contraction.Derive "derive was not selected";
        check (rejects (fun () -> ignore (hook "on"))) "an unknown rule was accepted";
        let side = [ positive (p [ v 0 ]); negative (q (f (v 0))) ] in
        let unit = step 2 [ positive (q (f (constant "a"))) ] in
        List.iter
          (fun (equivalence, expected) ->
            let t = Contraction.create ~equivalence () in
            Contraction.add t (step 0 side);
            Contraction.add t (step 1 (Contraction.complement side));
            equal (Option.is_some (find t unit)) expected "unit rewriting depends on the rule")
          [ (Contraction.Legacy, true); (Contraction.Redundant, false) ];
        (* Every worker and lane engine takes the rule from its configuration; a Vampire slice keeps
           Vampire's own condition (ForwardLiteralRewriting: the legacy one). *)
        let rule strategy equivalence =
          (Engine.create
             { Engine.default_config with strategy = Strategy.of_name strategy; equivalence })
            .contraction
            .equivalence
        in
        List.iter
          (fun name ->
            equal (rule name Contraction.Redundant) Contraction.Redundant (name ^ ": default rule");
            equal (rule name Contraction.Legacy) Contraction.Legacy (name ^ ": legacy hook"))
          [ "production"; "e208"; "calc:e"; "h042" ];
        equal
          (rule "v:flr4" Contraction.Redundant)
          Contraction.Legacy "a Vampire slice left Vampire's condition" );
    ( "admission keeps a unit that an equivalence would rewrite",
      fun () ->
        (* The legacy rule retired q(f(a)) in favour of p(a). Nothing smaller restores q(f(a)):
           the inverse ~p(Y) | q(f(Y)) has ~p(Y) selected, so it re-derives q(f(a)) from p(a) only
           for that to be rewritten again, and q(f(a)) never becomes a given clause (HWV006-1 at
           Passive phase 4 emptied Passive this way). *)
        let input =
          "cnf(forward,axiom,(p(X)|~q(f(X)))). cnf(inverse,axiom,(~p(Y)|q(f(Y)))). \
           cnf(unit,axiom,q(f(a)))."
        in
        let unit = [ positive (q (f (constant "a"))) ] in
        List.iter
          (fun (equivalence, kept) ->
            let theory = Tptp.parse input in
            let e = Engine.create { Engine.default_config with avatar = false; equivalence } in
            List.iter (Engine.add_axiom e) (Theory.fixed theory);
            let retained =
              Tbl.Int.fold
                (fun id _ clauses -> (Proof.get e.proof id).clause :: clauses)
                e.retained_index.live []
            in
            equal (List.mem unit retained) kept "the unit's retention depends on the rule";
            equal
              (List.mem [ positive (p [ constant "a" ]) ] retained)
              (not kept) "the rewritten unit appeared without the legacy rule")
          [ (Contraction.Redundant, true); (Contraction.Legacy, false) ] );
    ( "conditional equivalence locks include both directions and keep their proof roots",
      fun () ->
        let a = Avatar.create () in
        ignore (Avatar.remember a ~variants:true (step 0 [ positive (p [ constant "global" ]) ]));
        List.iter
          (fun id ->
            let clause = [ positive (p [ constant (string_of_int id) ]) ] in
            let component = Avatar.name a clause in
            let s = { (step id clause) with rule = Component component } in
            ignore (Avatar.remember a ~variants:true s))
          [ 1; 2; 3 ];
        a.model <- [| true; true; true |];
        check (Avatar.reduce_using a ~target:1 ~using:[ 2; 3 ]) "conditional target was not locked";
        equal (Tbl.Int.find a.entries 1).lock
          (Some ([ 1; 2 ], [ 2; 3 ]))
          "one direction's condition was lost";
        let roots = Avatar.roots a in
        List.iter
          (fun id ->
            check (List.mem id roots) "a reduction premise was not retained for collection")
          [ 1; 2; 3 ];
        check
          (not (Avatar.reduce_using a ~target:0 ~using:[ 2; 3 ]))
          "local equivalence hid global knowledge";
        a.model.(2) <- false;
        let entries = Avatar.affected_entries a ~guard [ 2 ] in
        Avatar.unlock a ~guard entries;
        equal (Tbl.Int.find a.entries 1).lock None "inverse condition did not release the target";
        check (Avatar.enabled a (Tbl.Int.find a.entries 1)) "target failed to resume" );
    ( "lookahead can choose maximal positive inference while keeping ordering eligibility",
      fun () ->
        let index = Index.create () in
        let clause = [ negative (p [ v 0 ]); positive (q (f (v 0))) ] in
        let side = step 1 [ negative (q (f (constant "a"))) ] in
        Index.add index side;
        let choice, work, _ = Index.lookahead index ~budget:16 clause in
        equal choice (Some [ 0; 1 ]) "unique maximal positive direction was excluded";
        check (work <= 16) "positive candidate exceeded the common budget";
        let calc = Calculus.create ~ordered:true (Term.create ()) in
        let given = { id = 3; clause; rule = Input (3, 0) } in
        Tbl.Int.replace calc.selected given.id choice;
        let results = ref [] in
        Calculus.resolve calc given side (fun c _ -> results := Clause.normalize c :: !results);
        check
          (List.mem [ negative (p [ constant "a" ]) ] !results)
          "positive direction never generated its resolvent";
        check
          (Calculus.eligible calc choice (Clause.scope 1 clause) 0 Fun.id)
          "adding a positive pivot discarded the original negative direction";
        check
          (not (Calculus.eligible calc None (Clause.scope 1 clause) 0 Fun.id))
          "no-selection mode disabled maximality checking";
        Index.add index (step 2 [ positive (p [ constant "a" ]) ]);
        let choice, _, _ = Index.lookahead index ~budget:16 clause in
        equal choice (Some [ 0 ]) "extra positive work displaced an available negative direction" );
    ( "lookahead does not hide a productive unknown direction behind an empty positive bucket",
      fun () ->
        let index = Index.create () in
        for id = 0 to 30 do
          Index.add index (step id [ positive (p [ constant (string_of_int id) ]) ])
        done;
        let choice, work, exhausted =
          Index.lookahead index ~budget:8 [ negative (p [ v 0 ]); positive (q (f (v 0))) ]
        in
        equal choice (Some [ 0 ]) "empty positive bucket blocked the rule";
        check (work <= 8 && exhausted > 0) "bounded unknown estimate was not reported";
        let choice, _, _ =
          Index.lookahead (Index.create ()) ~budget:8
            [ negative (p [ v 0 ]); positive (q (f (v 0))) ]
        in
        equal choice (Some [ 0 ]) "an unconnected positive direction displaced the fallback" );
    ( "protected clause classes survive a continuous supply of cheap negative goals",
      fun () ->
        List.iter
          (fun ratio ->
            let q = Passive.create ~ratio () in
            Passive.add ~kind:Passive.One_positive q 10000 1000;
            Passive.add ~kind:Passive.Many_positive q 10001 1000;
            let chosen = ref [] in
            for i = 2 to 33 do
              Passive.add ~kind:Passive.Negative q i 1;
              if i = 6 then Passive.rebuild q;
              Option.iter (fun id -> chosen := id :: !chosen) (Passive.take q)
            done;
            List.iter
              (fun id -> check (List.mem id !chosen) "a clause class was starved")
              [ 10000; 10001 ];
            check
              (q.kind_wait_max.(1) <= 16 && q.kind_wait_max.(2) <= 16)
              "class quota was not bounded";
            Passive.add ~kind:Passive.Many_positive q 99 1;
            Passive.invalidate q 99;
            Passive.rebuild q;
            while Passive.length q > 0 do
              check (Passive.take q <> Some 99) "rebuild revived a retired class member"
            done)
          [ 3; 10; 100000 ] );
    ( "a quiet goal collection keeps and drops the same goals as a full scan",
      fun () ->
        (* Quiet means nothing alive at the previous collection died since; goals added since
           may still be dead and must go exactly as in a full scan. *)
        let run quiet =
          let t = Goal.create () in
          let note id =
            Goal.note t ~guard ~support:[] (id, 0)
              (step id [ negative (P ("p" ^ string_of_int id, [ v 0 ])) ])
          in
          for i = 0 to 9 do
            note i
          done;
          Goal.collect ~quiet t ~alive:(fun _ -> true);
          for i = 10 to 19 do
            note i
          done;
          Goal.collect ~quiet t ~alive:(fun (id, _) -> id < 10 || id mod 4 <> 1);
          let first = Tbl.Int.length t.states in
          for i = 20 to 23 do
            note i
          done;
          Goal.collect ~quiet t ~alive:(fun (id, _) -> id < 10 || id mod 4 <> 1);
          ( first,
            List.sort compare (Tbl.Int.fold (fun id _ acc -> id :: acc) t.states []),
            List.sort compare (Tbl.Pair.fold (fun k _ acc -> k :: acc) t.roots []),
            List.of_seq (Queue.to_seq t.ready),
            List.of_seq (Queue.to_seq t.continuing),
            List.map (fun (r : Goal.root) -> r.owner) (List.of_seq (Queue.to_seq t.revisits)),
            t.metrics.invalidated )
        in
        let ((_, states, roots, _, _, _, _) as quiet) = run true in
        equal quiet (run false) "a quiet collection differs from a full one";
        check (not (List.mem (13, 0) roots)) "a dead root added since survived";
        check (List.mem (12, 0) roots) "a live root was dropped";
        check (List.exists (fun (id, _) -> id >= 20) roots) "the last roots were dropped";
        check (states <> []) "no goal state was exercised" );
    ( "the logged goal collection forgets and drops what the full scan does",
      fun () ->
        (* The engine's protocol: a retained ticket dies only by a removal (Goal.remove) or a new
           generation (Goal.supersede), and is never alive again; [quiet] is "no removal since
           the last collection". Random notes, removals, supersessions and collections on two
           tables, one collected by the logs and one by full scans, must keep the same states,
           roots and queues. *)
        let rng = Random.State.make [| 9; 2026; 18 |] in
        for _ = 1 to 300 do
          let fast = Goal.create () and full = Goal.create () in
          let live = Hashtbl.create 64 and next_generation = ref 0 and removed = ref false in
          let alive (id, g) = Hashtbl.find_opt live id = Some g in
          let view (t : Goal.t) =
            ( List.sort compare (Tbl.Int.fold (fun id _ acc -> id :: acc) t.states []),
              List.sort compare (Tbl.Pair.fold (fun k _ acc -> k :: acc) t.roots []),
              List.of_seq (Queue.to_seq t.ready),
              List.of_seq (Queue.to_seq t.continuing),
              List.map (fun (r : Goal.root) -> r.owner) (List.of_seq (Queue.to_seq t.revisits)),
              List.map (fun (r : Goal.root) -> r.owner) (List.of_seq (Queue.to_seq t.refresh_order)),
              t.metrics.invalidated,
              t.dropped )
          in
          for round = 1 to 300 do
            let id = Random.State.int rng 40 in
            match Random.State.int rng 6 with
            | 0 | 1 ->
                (* A retained clause is noted with its new ticket. *)
                if Hashtbl.mem live id then (
                  Goal.supersede fast id;
                  Goal.supersede full id;
                  removed := true);
                incr next_generation;
                Hashtbl.replace live id !next_generation;
                let s =
                  step id
                    [ negative (P ("p" ^ string_of_int (id mod 7), [ v 0 ])); positive (q (v 0)) ]
                in
                Goal.note fast ~guard ~support:[] (id, !next_generation) s;
                Goal.note full ~guard ~support:[] (id, !next_generation) s
            | 2 ->
                if Hashtbl.mem live id then removed := true;
                Hashtbl.remove live id;
                Goal.remove fast id;
                Goal.remove full id
            | 3 ->
                let quiet = not !removed in
                removed := false;
                Goal.collect ~quiet fast ~alive;
                Goal.collect ~quiet ~exhaustive:true full ~alive;
                equal (view fast) (view full)
                  (Printf.sprintf "the logged collection differs (round %d)" round)
            | _ ->
                if Random.State.bool rng then (
                  Goal.widen fast ~guard ~alive;
                  Goal.widen full ~guard ~alive)
                else (
                  Goal.root_queue fast (id, Option.value ~default:0 (Hashtbl.find_opt live id));
                  Goal.root_queue full (id, Option.value ~default:0 (Hashtbl.find_opt live id)))
          done
        done );
    ( "continuation and widening slots remain available under a flood of fresh roots",
      fun () ->
        let t = Goal.create () in
        let note id =
          Goal.note t ~guard ~support:[] (id, 0)
            (step id [ negative (P ("p" ^ string_of_int id, [ v 0 ])) ])
        in
        note 0;
        Goal.advance ~attempts:1 t ~guard
          ~alive:(fun _ -> true)
          ~record:(fun _ _ -> assert false)
          ~emit:(fun _ _ -> assert false)
          ~redundant:(fun _ _ -> false)
          ~demand:(fun ~guard:_ _ -> ());
        Goal.root_queue t (0, 0);
        for i = 1 to 100 do
          note i
        done;
        let resumed = Option.get (Goal.take t) in
        equal resumed.proof.step.id 0 "new roots displaced the existing cursor";
        Goal.widen t ~guard ~alive:(fun _ -> true);
        Goal.widen t ~guard ~alive:(fun _ -> true);
        check
          (t.metrics.widened > 0 && t.metrics.depth_max >= 3)
          "new roots displaced a deeper contour";
        Goal.collect t ~alive:(fun (id, _) -> id <> 0);
        check (not (Tbl.Int.mem t.states 0)) "collection kept an invalid continuation" );
    ( "read-only proof-path observation leaves search choices and certificates unchanged",
      fun () ->
        let seen = Hashtbl.create 8 in
        let observe stage support _ = Hashtbl.replace seen (stage, support) () in
        let _, _, plain = prove (text "") in
        let _, _, observed = prove ~on_clause:observe (text "") in
        equal plain observed "observer changed the proof";
        List.iter
          (fun stage -> check (Hashtbl.mem seen (stage, [])) "missing unconditional observation")
          [ "derived"; "retained" ] );
    ( "a scope-0 unit pivot matched unscoped gives the scoped copy's bindings and ticks",
      fun () ->
        let rng = Random.State.make [| 6; 2026 |] in
        let pick xs = List.nth xs (Random.State.int rng (List.length xs)) in
        let rec term scope depth =
          if depth = 0 || Random.State.int rng 3 = 0 then
            if Random.State.bool rng then V (scope, Random.State.int rng 3)
            else Fn (pick [ Original "a"; Original "b" ], [])
          else
            Fn
              ( pick [ Original "f"; Original "g" ],
                List.init (1 + Random.State.int rng 2) (fun _ -> term scope (depth - 1)) )
        in
        let atom scope =
          if Random.State.bool rng then E (term scope 3, term scope 3)
          else P ("p", List.init 2 (fun _ -> term scope 3))
        in
        let attempt pattern target =
          let ticks = ref 0 in
          let guard () = incr ticks in
          let env =
            try Some (Subsumption.atom ~guard [] pattern target) with Subsumption.No_match -> None
          in
          (env, !ticks)
        in
        let matched = ref 0 in
        for _ = 1 to 20000 do
          let pattern = atom 0 in
          (* targets share variable numbers with the pattern in another scope, as in [find] *)
          let target =
            if Random.State.bool rng then atom 2
            else Clause.map_atom (Clause.map_vars (fun (_, i) -> V (2, i))) pattern
          in
          let scoped = (List.hd (Clause.scope 1 [ { positive = true; atom = pattern } ])).atom in
          let env, ticks = attempt scoped target in
          let env', ticks' = attempt pattern target in
          let moved = Option.map (List.map (fun (((_, i) : variable), u) -> ((1, i), u))) env' in
          equal moved env "bindings differ";
          equal ticks' ticks "ticks differ";
          if env <> None then incr matched
        done;
        check (!matched > 1000) "too few matches exercised";
        (* A unit side with variables outside scope 0 still takes the scoped copy. *)
        let t = Contraction.create () in
        let unscoped =
          {
            id = 0;
            clause = [ { positive = true; atom = P ("q", [ V (3, 0) ]) } ];
            rule = Input (0, 0);
          }
        in
        Contraction.add t unscoped;
        Contraction.add t (step 1 [ positive (P ("r", [ v 0 ])) ]);
        match find t (step 2 [ negative (q (f (constant "a"))); positive (P ("s", [])) ]) with
        | Some { rule = Resolve (0, 0, 2, 0, sigma); _ } ->
            equal sigma [ ((1, 0), f (constant "a")) ] "the copy path bound another variable"
        | _ -> failwith "the scope-3 unit did not contract its target" );
  ]

let () =
  match Array.to_list Sys.argv with
  | [ _; "--export-rocq"; path ] -> (
      let theory, _, cert = prove (text "") in
      match Kernel.rocq_document theory cert with
      | Ok document -> Sexp.write_file path document
      | Error e -> failwith e)
  | _ -> Test_support.run tests
