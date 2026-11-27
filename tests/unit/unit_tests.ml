open Axiom_fuzzer
open Test_support
open Wire

let joint_fixture clauses =
  let focus = Focus.create () in
  let steps =
    List.mapi
      (fun id clause -> { id; clause = Clause.normalize clause; rule = Input (id, 0) })
      clauses
  in
  List.iter (fun (s : step) -> Focus.note focus ~guard:(fun () -> ()) (s.id, 1) s) steps;
  (focus, steps)

let replay_plan steps (plan : Focus.plan) =
  let proof = ref steps and parent = ref 0 in
  List.iter
    (fun (edge : Focus.resolution) ->
      let rule = Resolve (!parent, edge.pivot, fst edge.using, 0, edge.sigma) in
      let clause = Clause.normalize edge.conclusion in
      equal
        (Kernel.derive ~inputs:[] ~steps:!proof rule)
        (Ok clause) "joint plan differs from independent binary resolution";
      let id = List.length !proof in
      proof := { id; clause; rule } :: !proof;
      parent := id)
    (List.rev plan.reverse);
  equal (List.find (fun (s : step) -> s.id = !parent) !proof).clause plan.residual
    "plan residual differs from its proof"

let tests =
  [
    ( "focus collection drops the same entries as the full filter, in the same table order",
      fun () ->
        (* The engine's invariant: an id leaves the retained set only through [Focus.remove]
           (a deactivation); it may come back later (a reactivation) without a new entry. *)
        let rng = Random.State.make [| 811 |] in
        for _ = 1 to 200 do
          let quick = Focus.create () and full = Focus.create () in
          let retained = Hashtbl.create 64 in
          let keep id = Hashtbl.mem retained id in
          let next = ref 0 in
          for _ = 1 to 1 + Random.State.int rng 12 do
            (* [quiet] as the engine computes it: no retained id was removed since. *)
            let quiet = ref true in
            for _ = 1 to Random.State.int rng 30 do
              match Random.State.int rng 4 with
              | 0 | 1 ->
                  let id = !next in
                  incr next;
                  Focus.register quick id;
                  Focus.register full id;
                  if Random.State.int rng 3 > 0 then (
                    Hashtbl.replace retained id ();
                    (* The engine notes a clause right after retaining it. *)
                    if Random.State.bool rng then (
                      let c = constant (string_of_int (id mod 5)) in
                      let clause =
                        if Random.State.bool rng then [ positive (p [ c ]) ]
                        else [ negative (p [ c ]); negative (P ("q", [ c ])) ]
                      in
                      let step = { id; clause; rule = Input (id, 0) } in
                      Focus.note quick ~guard:(fun () -> ()) (id, 1) step;
                      Focus.note full ~guard:(fun () -> ()) (id, 1) step))
              | 2 when !next > 0 ->
                  let id = Random.State.int rng !next in
                  if keep id then quiet := false;
                  Hashtbl.remove retained id;
                  Focus.remove quick id;
                  Focus.remove full id
              | _ when !next > 0 -> Hashtbl.replace retained (Random.State.int rng !next) ()
              | _ -> ()
            done;
            let quiet = !quiet in
            Focus.collect ~quiet quick ~keep ~alive:(fun _ -> true);
            Focus.collect ~quiet ~exhaustive:true full ~keep ~alive:(fun _ -> true);
            let order f = Tbl.Int.fold (fun id _ ids -> id :: ids) f.Focus.entries [] in
            equal (order quick) (order full) "incremental focus collection changed the entries";
            let ids (i : Index.t) =
              List.sort compare (Tbl.Int.fold (fun id _ ids -> id :: ids) i.live [])
            in
            equal
              (ids quick.units, ids quick.goals, quick.units.size, quick.goals.size)
              (ids full.units, ids full.goals, full.units.size, full.goals.size)
              "incremental focus collection changed the units or goals";
            check (List.for_all keep (order quick)) "a dropped id kept its entry"
          done
        done );
    ( "saved joint witnesses leave a fresh search for alternative substitutions",
      fun () ->
        let goal = List.map (fun name -> negative (P (name, [ v 0 ]))) [ "p"; "q"; "r" ] in
        let focus, initial = joint_fixture [ goal; [ positive (p [ constant "a" ]) ] ] in
        let seed =
          Focus.plan focus ~guard:(fun () -> ()) ~alive:(fun _ -> true) (List.hd initial)
        in
        equal (List.length seed.residual) 2 "fixture has no unfinished witness";
        let retained =
          Focus.plan ~budget:0 ~seed focus
            ~guard:(fun () -> ())
            ~alive:(fun _ -> true)
            (List.hd initial)
        in
        equal retained seed "zero fresh budget discarded an already valid partial proof";
        let extra =
          List.mapi
            (fun i name ->
              {
                id = i + 2;
                clause = [ positive (P (name, [ constant "b" ])) ];
                rule = Input (i + 2, 0);
              })
            [ "p"; "q"; "r" ]
        in
        List.iter (fun (s : step) -> Focus.note focus ~guard:(fun () -> ()) (s.id, 1) s) extra;
        let result =
          Focus.plan ~seed focus ~guard:(fun () -> ()) ~alive:(fun _ -> true) (List.hd initial)
        in
        equal result.residual [] "saved witness starved a new compatible substitution";
        check
          (not (List.exists (fun (edge : Focus.resolution) -> fst edge.using = 1) result.reverse))
          "incompatible witnesses were combined";
        replay_plan (initial @ extra) result );
    ( "joint priority favors covered conditions while reserving an age turn",
      fun () ->
        let goal names = List.map (fun name -> negative (P (name, [ v 0 ]))) names in
        let focus, steps =
          joint_fixture
            [
              goal [ "missing"; "p" ];
              goal [ "p"; "q" ];
              [ positive (p [ constant "a" ]) ];
              [ positive (P ("q", [ constant "a" ])) ];
            ]
        in
        let take () =
          Focus.take_goal focus
            ~guard:(fun () -> ())
            ~alive:(fun _ -> true)
            ~get:(fun id -> List.find (fun (s : step) -> s.id = id) steps)
        in
        for _ = 1 to 3 do
          equal (take ()) (1, 1) "uncovered old condition displaced a covered goal";
          Focus.enqueue focus (1, 1)
        done;
        equal (take ()) (0, 1) "priority starved the oldest queued goal" );
    ( "closure feedback distinguishes a joint consequence from mere shortening",
      fun () ->
        let focus = Focus.create () in
        Focus.register focus 0;
        focus.committing <- true;
        Focus.register focus 1;
        focus.committing <- false;
        let get id =
          { id; clause = []; rule = (if id = 0 then Input (0, 0) else Factor (0, 0, 1, [])) }
        in
        let reward closed = Focus.reward ~closed focus ~get ~promote:(fun _ _ -> ()) [ 1 ] 8 in
        reward false;
        equal focus.plan_useful 0 "shortening was counted as a closed proof";
        equal (Tbl.Int.find focus.entries 0).closed_credit 0 "shortening earned closure credit";
        Focus.collect focus ~keep:(fun _ -> true) ~alive:(fun _ -> false);
        reward true;
        reward true;
        equal focus.plan_useful 1 "one used consequence was counted repeatedly";
        check
          ((Tbl.Int.find focus.entries 0).closed_credit > 0)
          "closed proof did not credit its goal" );
    ( "small joint plans agree with an independent witness oracle after symbol renaming",
      fun () ->
        List.iter
          (fun (left, right) ->
            for mask = 0 to 15 do
              let present bit = mask land (1 lsl bit) <> 0 in
              List.iter
                (fun shared ->
                  let goal =
                    [
                      negative (P (left, [ v 0 ]));
                      negative (P (right, [ v (if shared then 0 else 1) ]));
                    ]
                  in
                  let units =
                    List.init 4 (fun bit -> bit)
                    |> List.filter present
                    |> List.map (fun bit ->
                        [
                          positive
                            (P
                               ( (if bit < 2 then left else right),
                                 [ constant (if bit mod 2 = 0 then "a" else "b") ] ));
                        ])
                  in
                  let focus, steps = joint_fixture (goal :: units) in
                  let result =
                    Focus.plan focus ~guard:(fun () -> ()) ~alive:(fun _ -> true) (List.hd steps)
                  in
                  let expected =
                    if shared then (present 0 && present 2) || (present 1 && present 3)
                    else (present 0 || present 1) && (present 2 || present 3)
                  in
                  equal (result.residual = []) expected
                    "joint witness disagrees with the finite oracle";
                  replay_plan steps result)
                [ true; false ]
            done)
          [ ("p", "q"); ("renamed_z", "renamed_a") ] );
    ( "joint resolution rejects incompatible witnesses and cyclic joint substitutions",
      fun () ->
        let q xs = P ("q", xs) and f x = Fn (Original "f", [ x ]) in
        List.iter
          (fun clauses ->
            let focus, steps = joint_fixture clauses in
            let result =
              Focus.plan focus ~guard:(fun () -> ()) ~alive:(fun _ -> true) (List.hd steps)
            in
            check (result.residual <> []) "separate witnesses were combined into a refutation";
            replay_plan steps result)
          [
            [
              [ negative (p [ v 0 ]); negative (q [ v 0 ]) ];
              [ positive (p [ constant "a" ]) ];
              [ positive (q [ constant "b" ]) ];
            ];
            [
              [ negative (p [ v 0; v 1 ]); negative (q [ v 0; v 1 ]) ];
              [ positive (p [ v 0; f (v 0) ]) ];
              [ positive (q [ f (v 0); v 0 ]) ];
            ];
          ] );
    ( "joint resolution backtracks and freshly scopes each use of a universal unit",
      fun () ->
        let q xs = P ("q", xs) in
        let focus, steps =
          joint_fixture
            [
              [ negative (p [ v 0 ]); negative (q [ v 0 ]) ];
              [ positive (p [ constant "a" ]) ];
              [ positive (p [ constant "b" ]) ];
              [ positive (q [ constant "a" ]) ];
              [ positive (q [ constant "c" ]) ];
            ]
        in
        let result =
          Focus.plan focus ~guard:(fun () -> ()) ~alive:(fun _ -> true) (List.hd steps)
        in
        equal result.residual [] "a compatible joint witness was missed";
        check
          (focus.plan_trials > List.length result.reverse)
          "failed alternatives were not exercised";
        replay_plan steps result;
        let focus, steps =
          joint_fixture
            [
              [ negative (p [ constant "a" ]); negative (p [ constant "b" ]) ];
              [ positive (p [ v 0 ]) ];
            ]
        in
        let result =
          Focus.plan focus ~guard:(fun () -> ()) ~alive:(fun _ -> true) (List.hd steps)
        in
        equal result.residual [] "one universal unit could not be used with two substitutions";
        equal
          (List.map (fun (edge : Focus.resolution) -> fst edge.using) result.reverse)
          [ 1; 1 ] "fixture stopped reusing the same premise";
        replay_plan steps result );
    ( "partial joint plans propagate a substitution through all remaining conditions",
      fun () ->
        let focus, steps =
          joint_fixture
            [
              [
                negative (p [ v 0 ]); negative (P ("q", [ v 0; v 1 ])); negative (P ("r", [ v 1 ]));
              ];
              [ positive (p [ constant "a" ]) ];
            ]
        in
        let result =
          Focus.plan focus ~guard:(fun () -> ()) ~alive:(fun _ -> true) (List.hd steps)
        in
        equal result.residual
          (Clause.normalize
             [ negative (P ("q", [ constant "a"; v 0 ])); negative (P ("r", [ v 0 ])) ])
          "shared variable or instantiated argument was lost";
        replay_plan steps result;
        check
          (List.for_all (fun l -> l.positive) (Focus.wanted result.residual))
          "remaining conditions have wrong polarity" );
    ( "joint plans obey budgets, cancellation, and premise generations",
      fun () ->
        let focus, steps =
          joint_fixture
            [
              [ negative (p [ v 0 ]); negative (P ("q", [ v 0 ])) ];
              [ positive (p [ constant "a" ]) ];
              [ positive (P ("q", [ constant "a" ])) ];
            ]
        in
        let target = List.hd steps in
        let result =
          Focus.plan ~budget:0 focus ~guard:(fun () -> ()) ~alive:(fun _ -> true) target
        in
        equal result.reverse [] "zero budget performed work";
        equal focus.plan_exhausted 1 "budget exhaustion not reported";
        let result =
          Focus.plan focus ~guard:(fun () -> ()) ~alive:(fun (id, _) -> id <> 2) target
        in
        check (result.residual <> []) "a stale unit completed a plan";
        let exception Cancelled in
        check
          (try
             ignore
               (Focus.plan focus ~guard:(fun () -> raise Cancelled) ~alive:(fun _ -> true) target);
             false
           with Cancelled -> true)
          "planner swallowed cancellation";
        Focus.remove focus 2;
        Focus.collect focus ~keep:(fun id -> id <> 2) ~alive:(fun (id, _) -> id <> 2);
        check (not (Index.mem focus.units 2)) "reclaimed unit stayed in the plan index" );
    ( "joint commit rechecks support after delivering a partial demand",
      fun () ->
        let focus, steps =
          joint_fixture
            [
              [ negative (p [ v 0 ]); negative (P ("q", [ v 0 ])); negative (P ("r", [ v 0 ])) ];
              [ positive (p [ constant "a" ]) ];
              [ positive (P ("q", [ constant "a" ])) ];
            ]
        in
        let valid = ref true in
        Focus.advance focus
          ~guard:(fun () -> ())
          ~alive:(fun _ -> !valid)
          ~get:(fun id -> List.find (fun (s : step) -> s.id = id) steps)
          ~record:(fun _ _ -> failwith "stale plan recorded a premise")
          ~emit:(fun _ _ -> failwith "stale plan emitted a consequence")
          ~demand:(fun ~guard:_ _ -> valid := false);
        equal focus.plan_stale 1 "lost support was not detected";
        equal focus.plan_steps 0 "stale work was counted as committed" );
    ( "known joint consequences do not allocate unused intermediate proofs",
      fun () ->
        let focus, steps =
          joint_fixture
            [
              [ negative (p [ v 0 ]); negative (P ("q", [ v 0 ])); positive (P ("r", [ v 0 ])) ];
              [ positive (p [ constant "a" ]) ];
              [ positive (P ("q", [ constant "a" ])) ];
              [ positive (P ("r", [ constant "a" ])) ];
            ]
        in
        Focus.advance focus
          ~guard:(fun () -> ())
          ~alive:(fun _ -> true)
          ~get:(fun id -> List.find (fun (s : step) -> s.id = id) steps)
          ~redundant:(fun parents clause ->
            check (List.sort_uniq compare parents = [ 0; 1; 2 ]) "redundancy check lost support";
            clause = [ positive (P ("r", [ constant "a" ])) ])
          ~record:(fun _ _ -> failwith "known consequence allocated a proof intermediate")
          ~emit:(fun _ _ -> failwith "known consequence was re-emitted")
          ~demand:(fun ~guard:_ _ -> ());
        equal focus.plan_redundant 1 "known plan was not skipped" );
    ( "joint goal watches and queues remain bounded and collectible",
      fun () ->
        let focus = Focus.create () in
        for id = 0 to 399 do
          let step =
            {
              id;
              clause = [ negative (p [ constant (string_of_int id) ]); negative (P ("q", [])) ];
              rule = Input (id, 0);
            }
          in
          Focus.note focus ~guard:(fun () -> ()) (id, 1) step
        done;
        check
          (Tbl.Int.length focus.goals.live <= 256 && Queue.length focus.pending <= 128)
          "goal storage exceeded its bounds";
        check (focus.plan_dropped > 0) "overflow fixture did not evict pending goals";
        Focus.collect focus ~keep:(fun _ -> false) ~alive:(fun _ -> false);
        check (not (Focus.has_work focus)) "collection kept dead goals";
        equal (Tbl.Int.length focus.goals.live) 0 "dead goal postings survived" );
    ( "subsumption resolution preserves rigid targets and a shared substitution",
      fun () ->
        let step id clause = { id; clause; rule = Input (id, 0) } in
        let q xs = P ("q", xs) in
        let check_result side target expected =
          let side = step 0 side and target = step 1 target in
          let result, rule = Option.get (Subsumption.resolve side target) in
          equal (Clause.normalize result) (Clause.normalize expected) "wrong shortened target";
          equal
            (Kernel.derive ~inputs:[] ~steps:[ side; target ] rule)
            (Ok (Clause.normalize expected))
            "ordinary resolution cannot replay shortening";
          check
            (List.for_all (fun ((scope, _), _) -> scope = 1) (Wire.rule_substitution rule))
            "target variable was bound"
        in
        check_result
          [ positive (p [ v 0 ]); positive (q [ v 0; v 1 ]) ]
          [ negative (p [ constant "a" ]); positive (q [ constant "a"; v 3 ]) ]
          [ positive (q [ constant "a"; v 3 ]) ];
        check_result
          [ positive (p [ v 0 ]); positive (q [ v 0 ]); positive (q [ v 1 ]) ]
          [ negative (p [ constant "a" ]); positive (q [ constant "a" ]) ]
          [ positive (q [ constant "a" ]) ];
        let reject side target =
          equal
            (Subsumption.resolve (step 0 side) (step 1 target))
            None "invalid target contraction"
        in
        reject [ positive (p [ constant "a" ]) ] [ negative (p [ v 0 ]); positive (q [ v 0 ]) ];
        reject
          [ positive (p [ v 0 ]); positive (q [ v 0 ]) ]
          [ negative (p [ constant "a" ]); positive (q [ constant "b" ]) ];
        (* Multiple complementary literals need an explicit factoring step. *)
        reject
          [ positive (p [ v 0 ]); positive (p [ v 1 ]); positive (q [ v 0 ]) ]
          [ negative (p [ constant "a" ]); positive (q [ constant "a" ]) ];
        check_result
          [ positive (E (constant "a", constant "b")) ]
          [ negative (E (constant "b", constant "a")); positive (q []) ]
          [ positive (q []) ];
        reject
          [ positive (p [ v 0 ]); positive (E (constant "a", constant "b")) ]
          [ negative (p [ constant "a" ]); positive (E (constant "b", constant "a")) ] );
    ( "subsumption resolution obeys work limits and cancellation",
      fun () ->
        let side = { id = 0; clause = [ positive (p [ v 0 ]) ]; rule = Input (0, 0) }
        and target = { id = 1; clause = [ negative (p [ constant "a" ]) ]; rule = Input (1, 0) } in
        let exhausted = ref false in
        equal
          (Subsumption.resolve ~budget:0 ~on_exhausted:(fun () -> exhausted := true) side target)
          None "zero work budget was ignored";
        check !exhausted "budget exhaustion was not reported";
        let exception Cancelled in
        check
          (try
             ignore (Subsumption.resolve ~guard:(fun () -> raise Cancelled) side target);
             false
           with Cancelled -> true)
          "cancellation was swallowed" );
    ( "focus matches real obligations and expires stale generations",
      fun () ->
        let focus = Focus.create () in
        ignore (Focus.request focus (0, 7) [ negative (p [ v 0; v 0 ]) ]);
        let pressure = Focus.pressure focus ~guard:(fun () -> ()) ~alive:(( = ) (0, 7)) in
        equal
          (pressure [ positive (p [ constant "a"; constant "b" ]) ])
          0 "predicate overlap mistaken for unification";
        check
          (pressure [ positive (p [ constant "a"; constant "a" ]) ] > 0)
          "matching obligation ignored";
        equal (pressure [ negative (p [ v 1; v 1 ]) ]) 0 "wrong polarity matched";
        equal
          (Focus.pressure focus
             ~guard:(fun () -> ())
             ~alive:(( = ) (0, 8))
             [ positive (p [ constant "a"; constant "a" ]) ])
          0 "old generation survived reactivation";
        Focus.collect focus ~keep:(fun _ -> false) ~alive:(fun _ -> false);
        equal (Queue.length focus.requests) 0 "stale obligation retained";
        for id = 1 to 200 do
          ignore (Focus.request focus (id, 0) [ negative (P ("renamed", [ v id ])) ])
        done;
        equal (Queue.length focus.requests) 128 "obligation memory is unbounded";
        check
          (Focus.pressure focus
             ~guard:(fun () -> ())
             ~alive:(fun _ -> true)
             [ positive (P ("renamed", [ constant "renamed_constant" ])) ]
          > 0)
          "renamed symbols lost generic guidance" );
    ( "focus credits bounded ancestors and charges actual work",
      fun () ->
        let focus = Focus.create () in
        let get id =
          { id; clause = []; rule = (if id = 0 then Input (0, 0) else Factor (id - 1, 0, 1, [])) }
        in
        for id = 0 to 8 do
          Focus.register focus id
        done;
        let promotions = ref [] in
        Focus.reward focus ~get
          ~promote:(fun id score -> promotions := (id, score) :: !promotions)
          [ 8; 8 ] 16;
        equal (List.sort compare !promotions)
          [ (5, 2); (6, 4); (7, 8); (8, 16) ]
          "ancestor reward was duplicated or traversed too far";
        let before = Focus.rank focus 8 in
        Focus.observe_batch focus 8 ~seconds:0.1 ~generated:1000;
        check (Focus.rank focus 8 < before) "costly work kept the same preference";
        for _ = 1 to 20 do
          Focus.reward focus ~get ~promote:(fun _ _ -> ()) [ 8 ] 32
        done;
        equal (Focus.credit focus 8) 64 "credit did not saturate";
        Focus.collect focus ~keep:(( = ) 8) ~alive:(fun _ -> false);
        equal (Tbl.Int.length focus.entries) 1 "dead feedback survived collection" );
    ( "preferred selection preserves cheap, general, and age turns",
      fun () ->
        let q = Passive.create ~ratio:10 () in
        Passive.add q 0 1000;
        Passive.add q 1 100;
        Passive.prefer q 1 64;
        Passive.add q 2 2;
        Passive.prefer q 2 8;
        Passive.add q 3 1;
        equal (Passive.take q) (Some 3) "general turn was displaced";
        Passive.rebuild q;
        equal (Passive.take q) (Some 2) "large preferred clause displaced a cheap obligation";
        for id = 4 to 11 do
          Passive.add q id 1;
          Passive.prefer q id 8;
          ignore (Passive.take q)
        done;
        equal (Passive.take q) (Some 0) "preferred layer starved the oldest clause";
        Passive.invalidate q 1;
        Passive.rebuild q;
        check (not (Tbl.Int.mem q.preference 1)) "retired preference was resurrected" );
    ( "demodulation matches without instantiating the target",
      fun () ->
        let rewriter = Demodulation.create () in
        Demodulation.add rewriter
          {
            id = 0;
            rule = Input (0, 0);
            clause = [ positive (E (Fn (Original "f", [ constant "a" ]), constant "b")) ];
          };
        let target =
          { id = 1; rule = Input (1, 0); clause = [ positive (p [ Fn (Original "f", [ v 0 ]) ]) ] }
        in
        check (Demodulation.rewrite_once rewriter target = None) "target variable was instantiated";
        let concrete =
          { target with clause = [ positive (p [ Fn (Original "f", [ constant "a" ]) ]) ] }
        in
        check (Demodulation.rewrite_once rewriter concrete <> None) "matching rewrite missed";
        Demodulation.remove rewriter 0;
        check
          (Demodulation.rewrite_once rewriter concrete = None)
          "retired rewrite rule still applied" );
    ( "the lean rewrite search finds rewrite_once's rewrite, and skipping normal forms keeps it",
      fun () ->
        (* Random unit equations over f/2, g/1, h/2 and constants, oriented by KBO or, for ordered
           rewriting, kept in both directions; random targets with shared subterms. *)
        let rng = Random.State.make [| 20261115 |] in
        let rec term depth vars =
          if depth = 0 || Random.State.int rng 3 = 0 then
            if vars > 0 && Random.State.bool rng then V (0, Random.State.int rng vars)
            else constant (if Random.State.bool rng then "a" else "b")
          else
            match Random.State.int rng 3 with
            | 0 -> Fn (Original "f", [ term (depth - 1) vars; term (depth - 1) vars ])
            | 1 -> Fn (Original "g", [ term (depth - 1) vars ])
            | _ -> Fn (Original "h", [ term (depth - 1) vars; term (depth - 1) vars ])
        in
        let compared = ref 0 and rewritten = ref 0 in
        for round = 1 to 60 do
          let ordered_rewriting = round mod 2 = 0 in
          let rewriter = Demodulation.create ~ordered_rewriting () in
          let rules = 1 + Random.State.int rng 8 in
          for id = 0 to rules - 1 do
            Demodulation.add rewriter
              {
                id;
                rule = Input (id, 0);
                clause = Clause.normalize [ positive (E (term 3 2, term 2 2)) ];
              }
          done;
          (* A removed rule must no longer be used, also from the cache. *)
          if Random.State.bool rng then Demodulation.remove rewriter 0;
          let normal = ref [] in
          let skip t = List.memq t !normal and irreducible t = normal := t :: !normal in
          for k = 0 to 20 do
            let shared = term 2 2 in
            let lit () =
              if Random.State.bool rng then
                positive (E (Fn (Original "f", [ shared; term 2 2 ]), term 2 2))
              else negative (p [ Fn (Original "h", [ term 2 2; shared ]) ])
            in
            let target =
              {
                id = 100 + k;
                rule = Input (100 + k, 0);
                clause = Clause.normalize [ lit (); lit () ];
              }
            in
            let expected = Demodulation.rewrite_once rewriter target in
            equal
              (Demodulation.rewrite_first rewriter target)
              expected "the lean search found another rewrite";
            (* Subterms reported in normal form (also of earlier targets) stay skippable while no
               rule is added. *)
            equal
              (Demodulation.rewrite_first ~skip ~irreducible rewriter target)
              expected "skipping normal forms changed the rewrite";
            incr compared;
            if expected <> None then incr rewritten
          done
        done;
        check
          (!rewritten > 50 && !rewritten < !compared)
          "the fixture rewrites too rarely or always" );
    ( "the lean rewrite search follows rule changes interleaved with its queries",
      fun () ->
        (* The per-head discrimination trees and the liveness cells must follow every change of
           the rule set made after the trees were filled: additions (also of a live parent with a
           new clause, which supersedes its rules), removals and compactions (both paths, which
           delete the dropped rules from the trees), in random order between queries. Each query
           compares rewrite_once and rewrite_first, the latter without and with a normal-form memo
           kept as the engine keeps it (emptied when a rule is added, kept across removals and
           compactions, which never make a term reducible), with [uncached] below. Both rewriters
           read the trees, so only a reference that filters a head's live rules from [rules] at
           every position, oldest first, as rewrite_once did before any cache, can see a stale
           tree or a wrong order. Every fourth round also rewrites with instances of extra
           variables. *)
        let uncached (t : Demodulation.t) (target : step) =
          let rec scope = function
            | V (_, i) -> V (2, i)
            | Fn (f, args) -> Fn (f, List.map scope args)
          in
          let clause = List.map (Clause.map_literal scope) target.clause in
          let rec apply sigma = function
            | V v as term -> Option.value ~default:term (List.assoc_opt v sigma)
            | Fn (f, args) -> Fn (f, List.map (apply sigma) args)
          in
          let rec literals i = function
            | [] -> None
            | literal :: rest ->
                let rec positions = function
                  | [] -> literals (i + 1) rest
                  | (_, V _) :: more -> positions more
                  | (reverse_path, (Fn (f, args) as subterm)) :: pending ->
                      let more =
                        List.mapi (fun j term -> (j :: reverse_path, term)) args @ pending
                      in
                      let rec rules = function
                        | [] -> positions more
                        | (rule : Demodulation.rewrite) :: others -> (
                            if rule.parent = target.id || not (Tbl.Int.mem t.live rule.parent) then
                              rules others
                            else
                              match Subsumption.term [] rule.lhs subterm with
                              | exception Subsumption.No_match -> rules others
                              | sigma ->
                                  let sigma = Demodulation.complete t rule sigma in
                                  let replacement = apply sigma rule.rhs in
                                  if not (Ordering.greater ~order:t.order subterm replacement) then
                                    rules others
                                  else
                                    let path = List.rev reverse_path in
                                    Some
                                      ( Clause.replace i (Clause.put literal path replacement) clause,
                                        Paramodulate
                                          (rule.parent, 0, rule.reverse, target.id, i, path, sigma)
                                      ))
                      in
                      rules
                        (Option.value ~default:[] (Tbl.Head.find_opt t.rules (f, List.length args))
                        |> List.filter_map (fun (r : Demodulation.indexed_rewrite) ->
                            if r.cell.Index.alive then Some r.rewrite else None)
                        |> List.rev)
                in
                positions (List.mapi (fun j term -> ([ j ], term)) (Clause.atom_terms literal.atom))
          in
          literals 0 clause
        in
        let rng = Random.State.make [| 20261116 |] in
        let rec term depth vars =
          if depth = 0 || Random.State.int rng 4 = 0 then
            if vars > 0 && Random.State.bool rng then V (0, Random.State.int rng vars)
            else constant (if Random.State.bool rng then "a" else "b")
          else
            match Random.State.int rng 3 with
            | 0 -> Fn (Original "f", [ term (depth - 1) vars; term (depth - 1) vars ])
            | 1 -> Fn (Original "g", [ term (depth - 1) vars ])
            | _ -> Fn (Original "h", [ term (depth - 1) vars; term (depth - 1) vars ])
        in
        let queries = ref 0 and rewritten = ref 0 and removed = ref 0 and superseded = ref 0 in
        for round = 1 to 120 do
          let ordered_rewriting = round mod 2 = 0 and instances = round mod 4 = 0 in
          let rewriter = Demodulation.create ~ordered_rewriting ~instances () in
          if instances then Demodulation.set_minimal rewriter [ constant "a"; constant "b" ];
          let memo = ref [] and generation = ref (-1) in
          for _ = 1 to 200 do
            match Random.State.int rng 10 with
            | 0 | 1 | 2 ->
                let id = Random.State.int rng 12 in
                if Tbl.Int.mem rewriter.Demodulation.live id && Tbl.Head.length rewriter.trees > 0
                then incr superseded;
                Demodulation.add rewriter
                  {
                    id;
                    rule = Input (id, 0);
                    clause = Clause.normalize [ positive (E (term 3 2, term 2 2)) ];
                  }
            | 3 ->
                let id = Random.State.int rng 12 in
                if Tbl.Int.mem rewriter.live id && Tbl.Head.length rewriter.trees > 0 then
                  incr removed;
                Demodulation.remove rewriter id
            | 4 ->
                if Random.State.bool rng then Demodulation.compact rewriter
                else Demodulation.compact_all rewriter
            | _ ->
                if !generation <> rewriter.generation then (
                  memo := [];
                  generation := rewriter.generation);
                let skip t = List.memq t !memo and irreducible t = memo := t :: !memo in
                (* Targets share subterms across queries, as hash-consing makes them. *)
                let shared = term 2 2 in
                let lit () =
                  if Random.State.bool rng then
                    positive (E (Fn (Original "f", [ shared; term 2 2 ]), term 2 2))
                  else negative (p [ Fn (Original "h", [ term 2 2; shared ]) ])
                in
                let id = 100 + Random.State.int rng 1000 in
                let target =
                  { id; rule = Input (id, 0); clause = Clause.normalize [ lit (); lit () ] }
                in
                let expected = uncached rewriter target in
                equal
                  (Demodulation.rewrite_once rewriter target)
                  expected "rewrite_once's cache missed a change of the rules";
                (* A target whose variables are not all (0, i) is copied into scope 2 before the
                   search (its first literal in scope 1 here, so scopes may collide). *)
                let scoped =
                  {
                    target with
                    clause =
                      List.mapi
                        (fun k l ->
                          if k = 0 then
                            Clause.map_literal (Clause.map_vars (fun (_, i) -> V (1, i))) l
                          else l)
                        target.clause;
                  }
                in
                equal
                  (Demodulation.rewrite_once rewriter scoped)
                  (uncached rewriter scoped) "rewrite_once on a target outside scope 0";
                equal
                  (Demodulation.rewrite_first rewriter target)
                  expected "the cached search missed a change of the rules";
                equal
                  (Demodulation.rewrite_first ~skip ~irreducible rewriter target)
                  expected "the normal-form memo missed a change of the rules";
                incr queries;
                if expected <> None then incr rewritten
          done
        done;
        check
          (!removed > 500 && !superseded > 500)
          (Printf.sprintf "too few changes of a filled cache: %d removed, %d superseded" !removed
             !superseded);
        check
          (10 * !rewritten > !queries && !rewritten < !queries)
          "the fixture rewrites too rarely or always" );
    ( "literal selection and ordering are checked after substitution",
      fun () ->
        let clause = [ negative (p [ v 0 ]); positive (P ("q", [ Fn (Original "f", [ v 0 ]) ])) ] in
        check (Ordering.eligible clause 0 Fun.id) "selected negative literal ignored";
        check (not (Ordering.eligible clause 1 Fun.id)) "positive pivot bypassed selection";
        let clause = [ positive (p [ v 0 ]); positive (p [ Fn (Original "f", [ v 1 ]) ]) ] in
        check (Ordering.eligible clause 0 Fun.id) "incomparable literal removed prematurely";
        let app =
          Clause.map_vars (fun (_, i) ->
              if i = 0 then constant "a" else Fn (Original "f", [ constant "a" ]))
        in
        check (not (Ordering.eligible clause 0 app)) "ordering ignored the unifier" );
    ( "alpha variants require a bijective renaming",
      fun () ->
        let a = [ positive (p [ v 0; v 0 ]); positive (p [ v 1; v 0 ]) ] in
        let b = [ positive (p [ v 1; v 1 ]); positive (p [ v 0; v 1 ]) ] in
        check
          (Clause.normalize a <> Clause.normalize b)
          "variant regression no longer exercises different normal forms";
        check (Variant_index.variants a b) "renamed clause missed";
        let index = Variant_index.create () in
        Variant_index.add index (Clause.normalize a);
        check (Variant_index.mem index (Clause.normalize b)) "variant bucket lost a renaming";
        check
          (not (Variant_index.variants [ positive (p [ v 0; v 0 ]) ] [ positive (p [ v 0; v 1 ]) ]))
          "nonbijective renaming accepted";
        check
          (not (Variant_index.variants [ positive (p [ v 0 ]) ] [ positive (p [ constant "a" ]) ]))
          "matching mistaken for renaming";
        check
          (Variant_index.variants
             [ positive (E (v 0, constant "a")); negative (p [ v 0 ]) ]
             [ negative (p [ v 7 ]); positive (E (constant "a", v 7)) ])
          "symmetric equality or literal permutation missed" );
    ( "typed arenas and hash-consing",
      fun () ->
        let a = Source.create Signature.sets and b = Source.create Signature.sets in
        let x = Source.free a 0 in
        equal x (Source.free a 0) "term not shared";
        let f = Source.member a x x in
        equal f (Source.member a x x) "formula not shared";
        check
          (rejects (fun () -> ignore (Source.member a x (Source.free b 0))))
          "foreign arena accepted";
        check
          (rejects (fun () -> ignore (Source.apply a "sk_1_0" [])))
          "Skolem leaked into ZF source";
        check
          (rejects (fun () -> ignore (Source.pred a "member" [ x ])))
          "predicate arity unchecked" );
    ( "De Bruijn scope and capture avoidance",
      fun () ->
        let a = Source.create Signature.sets in
        let b0 = Source.bound a 0 and b1 = Source.bound a 1 and x = Source.free a 0 in
        let body = Source.member a b1 b0 in
        check (rejects (fun () -> ignore (Source.forall a ~depth:0 body))) "dangling index accepted";
        let f = Source.forall a ~depth:0 (Source.exists a ~depth:1 body) in
        check (Source.is_closed a f) "nested scope rejected";
        let f = Source.forall a ~depth:0 (Source.member a x b0) in
        let f = Source.subst_free a 0 b0 f in
        equal (Wire.export a f)
          (All (Pred ("member", [ B 1; B 0 ])))
          "substitution captured bound variable";
        check (Source.well_scoped a ~depth:1 f) "shift failed";
        check
          (rejects (fun () -> ignore (Source.shift_term a ~delta:(-1) ~cutoff:0 b0)))
          "invalid negative shift accepted" );
    ( "theory closure and replacement premise",
      fun () ->
        let t = Theory.create "zf" in
        let a = Theory.arena t in
        List.iter
          (fun ax -> check (Theory.validate_axiom t ax) ("invalid fixed axiom: " ^ ax.name))
          (Theory.fixed t);
        let phi = Source.eq a (Source.free a 0) (Source.free a 1) in
        let ax = Theory.instantiate t ~id:20 Replacement phi in
        check (Theory.validate_axiom t ax) "replacement instance rejected";
        check (Source.is_closed a (Wire.import a ax.formula)) "replacement not closed";
        let bad = { ax with formula = Ex (All (Pred ("member", [ B 0; B 1 ]))) } in
        check (not (Theory.validate_axiom t bad)) "replacement premise can be removed" );
    ( "occurs check and trail rollback",
      fun () ->
        let arena = Term.create () in
        let u = Unify.create arena in
        let x = v 0 and y = v 1 in
        let fx = Fn (Original "f", [ x ]) in
        let called = ref false in
        Unify.solve u [ (x, y); (y, fx) ] (fun _ _ -> called := true);
        check (not !called) "cyclic unification accepted";
        equal (Unify.mark u) 0 "failed unification left bindings";
        Unify.solve u
          [ (x, constant "a") ]
          (fun s _ -> equal s [ ((0, 0), constant "a") ] "unexpected substitution");
        equal (Unify.mark u) 0 "success left bindings";
        (try Unify.solve u [ (x, y) ] (fun _ _ -> raise Exit) with Exit -> ());
        equal (Unify.mark u) 0 "exception left bindings";
        let nested = ref false in
        Unify.solve u
          [ (x, constant "a") ]
          (fun _ outer_apply ->
            Unify.solve u
              [ (x, constant "b") ]
              (fun _ inner_apply ->
                nested := true;
                equal (inner_apply x) (constant "b") "outer inference contaminated nested factoring");
            equal (outer_apply x) (constant "a") "nested inference changed substitution snapshot");
        check !nested "nested unification inherited outer bindings" );
    ( "unification filters restore state before emitting and on rejection",
      fun () ->
        let arena = Term.create () in
        let u = Unify.create arena in
        let x = v 0 and y = v 1 in
        let equations = [ (x, y); (y, constant "a") ] in
        let accepted = ref false in
        Unify.solve u equations
          ~accept:(fun apply ->
            equal (apply x) (constant "a") "live bindings were not dereferenced";
            false)
          (fun _ _ -> accepted := true);
        check (not !accepted) "rejected solution emitted";
        equal (Unify.mark u) 0 "filter rejection leaked bindings";
        (try Unify.solve u equations ~accept:(fun _ -> raise Exit) (fun _ _ -> assert false)
         with Exit -> ());
        equal (Unify.mark u) 0 "filter exception leaked bindings";
        Unify.solve u equations
          ~accept:(fun apply -> apply x = constant "a")
          (fun sigma apply ->
            equal (Unify.mark u) 0 "emitter ran before rollback";
            equal sigma
              [ ((0, 0), constant "a"); ((0, 1), constant "a") ]
              "filter changed the captured substitution";
            Unify.solve u
              [ (x, constant "b") ]
              (fun _ nested ->
                equal (nested x) (constant "b") "filter contaminated nested inference");
            equal (apply x) (constant "a") "nested inference changed the accepted snapshot";
            accepted := true);
        check !accepted "accepted solution not emitted";
        let nodes = Term.count arena in
        Unify.solve u
          [ (Fn (Original "f", [ constant "new" ]), Fn (Original "g", [ x ])) ]
          ~accept:(fun _ -> failwith "incompatible terms reached the filter")
          (fun _ _ -> assert false);
        equal (Term.count arena) nodes "incompatible candidate interned terms" );
    ( "bounded lookahead counts work and keeps exhausted estimates unknown",
      fun () ->
        let index = Index.create () in
        List.iter (Index.add index)
          (List.init 20 (fun id ->
               { id; clause = [ positive (P ("p", [ constant "a" ])) ]; rule = Input (id, 0) }));
        Index.add index
          { id = 20; clause = [ positive (P ("q", [ constant "a" ])) ]; rule = Input (20, 0) };
        let clause = [ negative (P ("p", [ v 0 ])); negative (P ("q", [ v 0 ])) ] in
        let chosen, work, exhausted = Index.lookahead index ~budget:16 clause in
        equal chosen (Some [ 1 ]) "lookahead did not prefer the smaller candidate set";
        check (work <= 16 && exhausted = 1) "lookahead exceeded work budget";
        equal
          (Index.lookahead index ~budget:0 clause)
          (Some [ 0 ], 0, 0) "zero budget changed selection";
        let _, work, _ = Index.lookahead index ~budget:3 (clause @ clause @ clause) in
        check (work <= 3) "many literals multiplied the work budget";
        let calc = Calculus.create ~ordered:true (Term.create ()) in
        let step = { id = 30; clause; rule = Input (30, 0) } in
        Tbl.Int.replace calc.selected 30 (Some [ 1 ]);
        equal (Calculus.selected calc step) (Some [ 1 ]) "selected literal not retained";
        let fp = Index.Fingerprint.term in
        check
          (Index.Fingerprint.compatible
             (fp (Fn (Original "f", [ v 0 ])))
             (fp (Fn (Original "f", [ Fn (Original "g", [ constant "a"; constant "b" ]) ]))))
          "variable descendants became absent positions" );
    ( "inference selection does not hide backward rewrite targets",
      fun () ->
        let index = Equality_index.create () in
        let lhs = Fn (Original "f", [ constant "a" ]) in
        let step =
          {
            id = 0;
            rule = Input (0, 0);
            clause = [ negative (P ("q", [ v 0 ])); positive (p [ lhs ]) ];
          }
        in
        Equality_index.add ~eligible:(fun i -> i = 0) index step;
        equal
          (List.map (fun (s : step) -> s.id) (Equality_index.rewrite_targets index lhs))
          [ 0 ] "unselected literal was hidden from rewriting";
        let candidates =
          Equality_index.matches index ~variables:false [ positive (E (lhs, constant "b")) ]
        in
        check
          (List.for_all
             (fun (_, outgoing, _) -> List.for_all (fun (_, _, literal, _) -> literal = 0) outgoing)
             candidates)
          "unselected literal entered inference positions" );
    ( "weight alternatives retain age fairness and select distinct priorities",
      fun () ->
        List.iter
          (fun policy ->
            let q = Passive.create ~policy ~ratio:3 () in
            Passive.add ~unit_weight:1000 q 0 1000;
            for i = 1 to 3 do
              Passive.add ~unit_weight:1 q i 1;
              equal (Passive.take q) (Some i) "weight selection lost live clause"
            done;
            Passive.add ~unit_weight:1 q 4 1;
            equal (Passive.take q) (Some 0) "alternative weights starved age slot";
            Passive.invalidate q 4;
            Passive.rebuild q;
            equal (Passive.take q) None "alternative heap retained deleted clause")
          [ Passive.Size; Passive.Unit; Passive.Mixed ];
        let q = Passive.create ~policy:Passive.Mixed ~ratio:10 () in
        Passive.add ~unit_weight:100 q 0 1;
        Passive.add ~unit_weight:10 q 1 2;
        Passive.add ~unit_weight:3 q 2 3;
        equal (Passive.take q) (Some 0) "mixed queue did not start with size";
        equal (Passive.take q) (Some 2) "mixed queue did not switch to unit preference";
        let q = Passive.create ~policy:Passive.Mixed ~ratio:1 () in
        List.iter
          (fun (id, size, weight) -> Passive.add ~unit_weight:weight q id size)
          [ (0, 1, 100); (1, 100, 100); (2, 2, 100); (3, 3, 1) ];
        equal
          (List.init 3 (fun _ -> Passive.take q))
          [ Some 0; Some 1; Some 3 ] "age slots changed the alternating weight sequence" );
    ( "tautologies do not populate the term arena",
      fun () ->
        let engine = Engine.create config.engine in
        let atom = p [ Fn (Original "f", [ constant "unused" ]) ] in
        Engine.emit engine [ positive atom; negative atom ] (Input (0, 0));
        equal (Term.count engine.terms) 0 "tautology populated the arena";
        equal engine.metrics.tautologies 1 "tautology was not rejected";
        equal (Proof.stored engine.proof) 0 "discarded clause entered proof storage" );
    ( "standardizing parents apart",
      fun () ->
        let calc = Calculus.create (Term.create ()) in
        let left =
          {
            id = 0;
            clause = [ positive (p [ v 0 ]); positive (P ("q", [ v 0 ])) ];
            rule = Input (0, 0);
          }
        in
        let right =
          { id = 1; clause = [ negative (p [ Fn (Original "f", [ v 0 ]) ]) ]; rule = Input (1, 0) }
        in
        let found = ref [] in
        Calculus.resolve calc left right (fun c _ -> found := c :: !found);
        check (!found <> []) "same local number in separate clauses caused occurs failure" );
    ( "tautology and one-way subsumption",
      fun () ->
        check (Clause.tautology [ positive (p [ v 0 ]); negative (p [ v 0 ]) ]) "tautology missed";
        check
          (not (Clause.tautology [ positive (p [ v 0 ]); negative (p [ constant "a" ]) ]))
          "merely unifiable literals discarded";
        check
          (Subsumption.subsumes [ positive (p [ v 0 ]) ] [ positive (p [ constant "a" ]) ])
          "matching subsumption failed";
        check
          (not (Subsumption.subsumes [ positive (p [ constant "a" ]) ] [ positive (p [ v 0 ]) ]))
          "target variable was bound";
        check
          (not
             (Subsumption.subsumes
                [ positive (p [ v 0; v 0 ]) ]
                [ positive (p [ constant "a"; constant "b" ]) ]))
          "nonlinear match ignored" );
    ( "subsumption keeps target variables rigid without copying their scope",
      fun () ->
        check
          (Subsumption.subsumes
             [ positive (p [ v 0; v 1 ]) ]
             [ positive (p [ Fn (Original "f", [ v 0 ]); v 0 ]) ])
          "a target variable was mistaken for a pattern variable";
        check
          (not
             (Subsumption.subsumes
                [ positive (p [ v 0; v 0 ]) ]
                [ positive (p [ Fn (Original "f", [ v 0 ]); v 0 ]) ]))
          "a nonlinear match substituted a rigid target";
        (* Multiset subsumption: p(X) | p(Y) must not delete its own factor
           instance p(a); the factor is not redundant. *)
        check
          (not
             (Subsumption.subsumes
                [ positive (p [ v 0 ]); positive (p [ v 1 ]) ]
                [ positive (p [ constant "a" ]) ]))
          "two pattern literals collapsed onto one target literal";
        check
          (not
             (Subsumption.subsumes
                [ positive (Wire.E (v 0, constant "a")); positive (Wire.E (v 1, constant "a")) ]
                [ positive (Wire.E (v 0, constant "a")); negative (p [ constant "c" ]) ]))
          "an unorientable equation pair subsumed a clause containing its factor";
        check
          (Subsumption.subsumes
             [ positive (p [ v 0 ]); positive (p [ v 1 ]) ]
             [ positive (p [ constant "a" ]); positive (p [ constant "b" ]) ])
          "distinct target literals were not matched";
        check
          (Subsumption.subsumes
             [ positive (p [ v 0 ]) ]
             [ positive (p [ v 0 ]); positive (p [ v 1 ]) ])
          "a factor did not subsume its parent";
        let exhausted = ref 0 in
        check
          (not
             (Subsumption.subsumes ~budget:0
                ~on_exhausted:(fun () -> incr exhausted)
                [ positive (p [ v 0 ]) ]
                [ positive (p [ constant "a" ]) ]))
          "zero budget accepted a nontrivial match";
        equal !exhausted 1 "budget exhaustion was not reported exactly once";
        let exception Cancelled in
        let nested =
          List.fold_left (fun t _ -> Fn (Original "f", [ t ])) (v 0) (List.init 256 Fun.id)
        in
        let calls = ref 0 in
        check
          (try
             ignore
               (Subsumption.subsumes
                  ~guard:(fun () ->
                    incr calls;
                    if !calls = 2 then raise Cancelled)
                  [ positive (p [ nested ]) ]
                  [ positive (p [ nested ]) ]);
             false
           with Cancelled -> true)
          "a deep match ignored cancellation" );
    ( "age queue prevents starvation",
      fun () ->
        let q = Passive.create ~ratio:10 () in
        Passive.add q 0 1000;
        for i = 1 to 10 do
          Passive.add q i 1;
          equal (Passive.take q) (Some i) "weight selection"
        done;
        Passive.add q 11 1;
        equal (Passive.take q) (Some 0) "old heavy clause starved";
        Passive.invalidate q 11;
        equal (Passive.take q) None "lazy deletion failed";
        for i = 12 to 300 do
          Passive.add q i i;
          Passive.invalidate q i
        done;
        equal (Passive.take q) None "heap rebuild resurrected invalid entry" );
    ( "TPTP parser rejects unsupported semantics",
      fun () ->
        List.iter
          (fun s -> check (rejects (fun () -> ignore (Tptp.parse s))) ("accepted: " ^ s))
          [
            "include('other.p').";
            "fof(a,axiom,p(X)).";
            "fof(a,conjecture,p).";
            "fof(a,axiom,$less(1,2)).";
            "fof(a,axiom,(p & q | r)).";
            "cnf(a,axiom,(p & q)).";
            "fof(a,axiom,(p(a) & p(a,b))).";
            "fof(a,axiom,(![X,X]:p(X))).";
          ];
        let deep =
          "fof(a,axiom,p("
          ^ String.concat "" (List.init 300 (fun _ -> "f("))
          ^ "a" ^ String.make 300 ')' ^ "))."
        in
        check (rejects (fun () -> ignore (Tptp.parse deep))) "deep function nesting was not bounded";
        let t = Tptp.parse "cnf(a,axiom,(p(X) | ~p(f(X))))." in
        check (List.length (Theory.fixed t) = 1) "CNF import failed" );
    ( "TPTP binder shadowing and quoted symbols",
      fun () ->
        let t = Tptp.parse "fof('scope',axiom,(![X]: ('p'(X) & (?[X]: 'p'(X)))))." in
        let a = List.hd (Theory.fixed t) in
        check (Theory.validate_axiom t a) "shadowing failed";
        ignore (Tptp.parse (Tptp.problem (Theory.fixed t))) );
    ( "S-expression input is strict data",
      fun () ->
        let data = Sexp.List [ Sexp.Atom "a\"b\\c\n"; Sexp.List [] ] in
        equal (Sexp.parse (Sexp.to_string data)) data "string roundtrip";
        List.iter
          (fun s -> check (rejects (fun () -> ignore (Sexp.parse s))) "malformed data accepted")
          [ "("; "a b"; "\"\\z\""; String.make 600 '(' ] );
    ( "S-expression size limit is 32 MiB for text and files",
      fun () ->
        equal Sexp.max_file_bytes (32 * 1024 * 1024) "size limit";
        (* 20 MiB was over the old 16 MiB limit; it must now round-trip through text and a file. *)
        let data = Sexp.List [ Sexp.Atom (String.make (20 * 1024 * 1024) 'a') ] in
        let text = Sexp.to_string data in
        check (String.length text > 16 * 1024 * 1024) "text is not above the old limit";
        equal (Sexp.parse text) data "20 MiB text";
        let path = Filename.temp_file "axf-sexp-limit" ".sexp" in
        Fun.protect
          ~finally:(fun () -> Sys.remove path)
          (fun () ->
            let write n =
              let oc = open_out_bin path in
              Fun.protect
                ~finally:(fun () -> close_out oc)
                (fun () -> output_string oc (String.sub (text ^ String.make n ' ') 0 n))
            in
            write (String.length text);
            equal (Sexp.parse (Sexp.read_file path)) data "20 MiB file";
            (* A bare atom is valid data of any length, so only the size limit can reject it. *)
            let atom n = String.make n 'a' in
            let error f = match f () with _ -> "accepted" | exception Sexp.Error m -> m in
            let write_atom n =
              let oc = open_out_bin path in
              Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc (atom n))
            in
            write_atom Sexp.max_file_bytes;
            equal
              (Sexp.parse (Sexp.read_file path))
              (Sexp.Atom (atom Sexp.max_file_bytes))
              "file at the limit";
            write_atom (Sexp.max_file_bytes + 1);
            equal (error (fun () -> Sexp.read_file path)) "file size limit" "file over the limit");
        let at_limit = String.make Sexp.max_file_bytes 'a' in
        equal (Sexp.parse at_limit) (Sexp.Atom at_limit) "text at the limit";
        equal
          (match Sexp.parse (at_limit ^ "a") with _ -> "accepted" | exception Sexp.Error m -> m)
          "certificate size limit" "text over the limit" );
    ( "search limits validated",
      fun () ->
        check
          (rejects (fun () ->
               ignore
                 (Engine.create
                    {
                      Engine.default_config with
                      limits = { Engine.default_limits with seconds = nan };
                    })))
          "NaN time budget accepted";
        check
          (rejects (fun () -> ignore (Passive.create ~ratio:max_int ())))
          "overflowing ratio accepted" );
    ( "compaction filters like List.filter and keeps unchanged suffixes shared",
      fun () ->
        let rng = Random.State.make [| 16 |] in
        for _ = 1 to 2000 do
          let xs = List.init (Random.State.int rng 40) (fun _ -> Random.State.int rng 6) in
          let k = Random.State.int rng 8 in
          let keep x = x <> k in
          equal (Shared.filter keep xs) (List.filter keep xs) "Shared.filter changed the list"
        done;
        let xs = [ 1; 2; 3; 4; 5 ] in
        check (Shared.filter (fun _ -> true) xs == xs) "unchanged list was copied";
        let ys = Shared.filter (fun x -> x <> 2) xs in
        equal ys [ 1; 3; 4; 5 ] "wrong filtered list";
        check (List.tl ys == List.tl (List.tl xs)) "suffix after the last removal was copied";
        check (Shared.filter (fun x -> x <> 5) xs = [ 1; 2; 3; 4 ]) "tail removal lost";
        let index = Index.create () in
        let step id =
          {
            id;
            clause = [ positive (p [ constant ("c" ^ string_of_int id) ]) ];
            rule = Input (id, 0);
          }
        in
        List.iter (fun id -> Index.add index (step id)) [ 0; 1; 2; 3 ];
        let key = Clause.key (positive (p [ constant "c0" ])) in
        let before = Tbl.Feature.find index.buckets key in
        Index.compact index;
        check
          (Tbl.Feature.find index.buckets key == before)
          "compaction copied a bucket without deaths";
        (* Postings are newest first: removing the newest keeps every older cell. *)
        Index.remove index 3;
        Index.compact index;
        let after = Tbl.Feature.find index.buckets key in
        equal
          (List.map (fun (q : Index.posting) -> q.step.id) after)
          [ 2; 1; 0 ] "dead posting kept";
        check (after == List.tl before) "older live postings were copied" );
    ( "the start-up minor heap yields to an explicit runtime setting",
      fun () ->
        let env pairs name = List.assoc_opt name pairs in
        check (not (Minor_heap.set_by_environment (env []))) "no setting was taken for one";
        check (Minor_heap.set_by_environment (env [ ("OCAMLRUNPARAM", "s=4M") ])) "s=4M missed";
        check
          (Minor_heap.set_by_environment (env [ ("OCAMLRUNPARAM", "b,v=0x400,s=1M") ]))
          "a later s= was missed";
        check
          (not (Minor_heap.set_by_environment (env [ ("OCAMLRUNPARAM", "b,o=200") ])))
          "another option was taken for s";
        check
          (Minor_heap.set_by_environment (env [ ("CAMLRUNPARAM", "s=512k") ]))
          "CAMLRUNPARAM was ignored";
        check
          (not
             (Minor_heap.set_by_environment
                (env [ ("OCAMLRUNPARAM", "o=90"); ("CAMLRUNPARAM", "s=512k") ])))
          "CAMLRUNPARAM was read although OCAMLRUNPARAM is set";
        let before = (Gc.get ()).minor_heap_size in
        Minor_heap.apply ~getenv:(env [ ("OCAMLRUNPARAM", "s=64k") ]) ~words:(4 * before) ();
        equal (Gc.get ()).minor_heap_size before "an explicit setting was overridden";
        Minor_heap.apply ~getenv:(env []) ~words:(2 * before) ();
        equal (Gc.get ()).minor_heap_size (2 * before) "the start-up size was not applied";
        Minor_heap.apply ~getenv:(env []) ~words:before ();
        equal (Gc.get ()).minor_heap_size (2 * before) "a smaller size shrank the nursery";
        Gc.set { (Gc.get ()) with minor_heap_size = before } );
    ( "liveness cells agree with the generation table on random add/remove sequences",
      fun () ->
        (* Negative ids are synthetic steps (Goal); ids are re-added and removed repeatedly. *)
        let rng = Random.State.make [| 41 |] in
        let index = Index.create ()
        and equalities = Equality_index.create ()
        and rewriter = Demodulation.create () in
        let a = constant "a" and b = constant "b" in
        let g x = Fn (Original "g", [ x ]) in
        let clause id =
          match (id + 1000) mod 3 with
          | 0 -> [ positive (E (g (constant ("c" ^ string_of_int (abs id mod 4))), a)) ]
          | 1 -> [ positive (p [ g a ]); negative (E (g b, b)) ]
          | _ -> [ negative (p [ v 0 ]); positive (E (g (v 0), v 0)) ]
        in
        let agree () =
          Tbl.Feature.iter
            (fun _ xs ->
              List.iter
                (fun (q : Index.posting) ->
                  equal (Index.live q)
                    (Index.current index q.step.id q.generation)
                    "index cell disagrees with the generation table")
                xs)
            index.buckets;
          let table_current (q : Equality_index.posting) =
            match Tbl.Int.find_opt equalities.live q.step.id with
            | Some generation -> generation = q.generation
            | None -> false
          in
          List.iter
            (fun table ->
              Tbl.Head_opt.iter
                (fun _ xs ->
                  List.iter
                    (fun q ->
                      equal
                        (Equality_index.current equalities q)
                        (table_current q) "equality cell disagrees with the generation table")
                    xs)
                table)
            [ equalities.sources; equalities.targets ];
          Tbl.Head.iter
            (fun _ rules ->
              List.iter
                (fun (r : Demodulation.indexed_rewrite) ->
                  equal (Demodulation.current rewriter r)
                    (Tbl.Int.find_opt rewriter.live r.rewrite.parent = Some r.generation)
                    "rewrite cell disagrees with the generation table")
                rules)
            rewriter.rules;
          equal (Tbl.Int.length index.cells) (Tbl.Int.length index.live) "index cells leaked";
          equal (Tbl.Int.length equalities.cells) (Tbl.Int.length equalities.live)
            "equality cells leaked";
          equal (Tbl.Int.length rewriter.cells) (Tbl.Int.length rewriter.live)
            "rewrite cells leaked"
        in
        for _ = 1 to 3000 do
          let id = Random.State.int rng 40 - 12 in
          let s = { id; clause = Clause.normalize (clause id); rule = Input (abs id, 0) } in
          (match Random.State.int rng 7 with
          | 0 | 1 | 2 ->
              Index.add index s;
              Equality_index.add equalities s;
              Demodulation.add rewriter s
          | 3 | 4 ->
              Index.remove index id;
              Equality_index.remove equalities id;
              Demodulation.remove rewriter id
          | 5 ->
              Index.compact index;
              Equality_index.compact equalities;
              Demodulation.compact rewriter;
              let postings = Tbl.Feature.fold (fun _ xs n -> n + List.length xs) index.buckets 0 in
              equal index.size postings "compaction miscounted the postings"
          | _ ->
              let live =
                List.sort_uniq compare (List.map (fun (s : step) -> s.id) (Index.all index))
              in
              equal live
                (List.sort compare (Tbl.Int.fold (fun id _ ids -> id :: ids) index.live []))
                "Index.all disagrees with the live table");
          agree ()
        done );
    ( "dirty-bucket compaction leaves the same bucket lists as filtering every bucket",
      fun () ->
        (* Two copies get the same operations; one compacts only its dirty buckets, the other
           filters every bucket as compaction did before. Tables must agree entry by entry, in
           iteration order, after every step. *)
        let rng = Random.State.make [| 43 |] in
        let make () =
          (Index.create (), Equality_index.create (), Demodulation.create (), Contraction.create ())
        in
        let ((i1, e1, d1, c1) as one) = make () and ((i2, e2, d2, c2) as two) = make () in
        let a = constant "a" and b = constant "b" in
        let g x = Fn (Original "g", [ x ]) and h x = Fn (Original "h", [ x ]) in
        let clause id =
          let c = constant ("c" ^ string_of_int (abs id mod 5)) in
          match (id + 1000) mod 5 with
          | 0 -> [ positive (E (g c, a)) ]
          | 1 -> [ positive (p [ g a ]); negative (E (h c, b)) ]
          | 2 -> [ negative (p [ v 0 ]); positive (E (g (v 0), v 0)) ]
          | 3 -> [ positive (P ("q", [ h (v 1) ])); negative (P ("q", [ c ])) ]
          | _ -> [ negative (P ("r", [ c; v 0 ])) ]
        in
        let index_view (t : Index.t) =
          ( Tbl.Feature.fold
              (fun k xs acc ->
                (k, List.map (fun (q : Index.posting) -> (q.step.id, q.generation, q.literal)) xs)
                :: acc)
              t.buckets [],
            t.size,
            List.map (fun ((s : step), (c : Index.cell)) -> (s.id, c.alive)) t.all,
            List.map (fun (s : step) -> s.id) (Index.all t) )
        in
        let equality_view (t : Equality_index.t) =
          List.map
            (fun table ->
              Tbl.Head_opt.fold
                (fun k xs acc ->
                  (k, List.map (fun (q : Equality_index.posting) -> (q.step.id, q.generation)) xs)
                  :: acc)
                table [])
            [ t.sources; t.targets ]
        in
        let rewrite_view (t : Demodulation.t) =
          Tbl.Head.fold
            (fun k xs acc ->
              ( k,
                List.map
                  (fun (r : Demodulation.indexed_rewrite) ->
                    (r.rewrite.parent, r.rewrite.reverse, r.generation))
                  xs )
              :: acc)
            t.rules []
        in
        let contraction_view (t : Contraction.t) =
          ( index_view t.units,
            index_view t.binary,
            Contraction.Keys.fold
              (fun k (c : Contraction.klass) acc ->
                if c.ids = [] then acc else (k.value, c.ids) :: acc)
              t.classes []
            |> List.sort compare )
        in
        let agree () =
          equal (index_view i1) (index_view i2) "index compaction differs";
          equal (equality_view e1) (equality_view e2) "equality compaction differs";
          equal (rewrite_view d1) (rewrite_view d2) "rewrite compaction differs";
          equal (contraction_view c1) (contraction_view c2) "contraction compaction differs"
        in
        let both f =
          f one;
          f two
        in
        let partial = ref 0 and full = ref 0 in
        for _ = 1 to 4000 do
          let id = Random.State.int rng 30 - 8 in
          let s = { id; clause = Clause.normalize (clause id); rule = Input (abs id, 0) } in
          match Random.State.int rng 8 with
          | 0 | 1 | 2 ->
              both (fun (i, e, d, c) ->
                  Index.add i s;
                  Equality_index.add e s;
                  Demodulation.add d s;
                  Contraction.add c s)
          | 3 | 4 ->
              both (fun (i, e, d, c) ->
                  Index.remove i id;
                  Equality_index.remove e id;
                  Demodulation.remove d id;
                  Contraction.remove c id)
          | 5 | 6 ->
              if i1.stale > 0 then
                if List.compare_length_with i1.dirty (Tbl.Feature.length i1.buckets) < 0 then
                  incr partial
                else incr full;
              Index.compact i1;
              Equality_index.compact e1;
              Demodulation.compact d1;
              Contraction.compact c1;
              Index.compact_all i2;
              Equality_index.compact_all e2;
              Demodulation.compact_all d2;
              Contraction.compact_all c2;
              agree ()
          | _ ->
              (* A compaction of an index without deaths changes nothing, physically. *)
              let before = Tbl.Feature.fold (fun k xs acc -> (k, xs) :: acc) i1.buckets [] in
              let clean = i1.stale = 0 in
              Index.compact i1;
              Index.compact_all i2;
              if clean then
                List.iter
                  (fun (k, xs) ->
                    check (Tbl.Feature.find i1.buckets k == xs) "a clean bucket was copied")
                  before;
              agree ()
        done;
        (* Both compaction paths ran: the dirty buckets only, and the full sweep. *)
        check (!partial > 50 && !full > 50) "a compaction path was not exercised" );
    ( "a cursor rebuilt from its mark continues the dropped scan exactly",
      fun () ->
        (* 400 trials with seed 29 in the suite; AXIOM_MARK_TRIALS and AXIOM_MARK_SEED (test-only)
           run the same property as a stress test, e.g. 20,000 trials after a merge. *)
        let env name default =
          Option.value ~default (Option.bind (Sys.getenv_opt name) int_of_string_opt)
        in
        let rng = Random.State.make [| env "AXIOM_MARK_SEED" 29 |] in
        let pick xs = List.nth xs (Random.State.int rng (List.length xs)) in
        let rec term depth =
          match Random.State.int rng (if depth = 0 then 3 else 5) with
          | 0 -> v (Random.State.int rng 2)
          | 1 | 2 -> constant (pick [ "a"; "b" ])
          | 3 -> Fn (Original "f", [ term (depth - 1) ])
          | _ -> Fn (Original "g", [ term (depth - 1); term (depth - 1) ])
        in
        let literal () =
          let atom =
            if Random.State.int rng 3 = 0 then P (pick [ "p"; "q" ], [ term 2 ])
            else E (term 2, term 2)
          in
          { positive = Random.State.bool rng; atom }
        in
        let rec drop n s =
          if n = 0 then s
          else match s () with Seq.Nil -> Seq.empty | Seq.Cons (_, r) -> drop (n - 1) r
        in
        for _ = 1 to env "AXIOM_MARK_TRIALS" 400 do
          let index = Index.create () and equalities = Equality_index.create () in
          let next = ref 0 in
          let add () =
            incr next;
            let s =
              { id = !next; clause = List.init 2 (fun _ -> literal ()); rule = Input (!next, 0) }
            in
            Index.add index s;
            Equality_index.add equalities s;
            s
          in
          let steps = List.init (Random.State.int rng 40) (fun _ -> add ()) in
          let query = List.init 3 (fun _ -> literal ()) in
          let since = if Random.State.bool rng then 0 else Random.State.int rng (1 + !next) in
          let variables = Random.State.bool rng in
          let upto = index.generation and upto_equality = equalities.generation in
          let mark = Index.mark () and taken = ref 0 in
          let emark = Equality_index.mark () and etaken = ref 0 in
          let resolution ?from ?upto ~resumes mark taken =
            Index.cursor ~since ?upto ?from ~mark index query
            |> Index.follow ~resumes
                 ~visits:(fun () -> mark.Index.visits)
                 ~position:(fun () -> Index.position mark)
                 ~taken
          in
          let equality ?from ?upto ~resumes mark taken =
            Equality_index.cursor ~since ?upto ?from ~mark equalities ~variables query
            |> Index.follow ~resumes
                 ~visits:(fun () -> mark.Equality_index.visits)
                 ~position:(fun () -> Equality_index.position mark)
                 ~taken
          in
          let rest = drop (Random.State.int rng 25) (resolution ~resumes:false mark taken)
          and erest = drop (Random.State.int rng 60) (equality ~resumes:false emark etaken) in
          (* What a drop keeps: copies, since running the old streams moves the marks. *)
          let kept = { mark with needle = mark.needle } and kept_taken = ref !taken in
          let ekept = { emark with query = emark.query } and ekept_taken = ref !etaken in
          if Random.State.bool rng then Equality_index.detach ekept;
          List.iter
            (fun (s : step) ->
              if Random.State.int rng 3 = 0 then (
                Index.remove index s.id;
                Equality_index.remove equalities s.id))
            steps;
          if Random.State.bool rng then (
            Index.compact index;
            Equality_index.compact equalities);
          for _ = 1 to Random.State.int rng 8 do
            ignore (add ())
          done;
          if Random.State.bool rng then (
            Index.compact index;
            Equality_index.compact equalities);
          let hits stream = List.of_seq (Seq.filter_map Fun.id stream) in
          let ids xs = List.map (fun ((s : step), position) -> (s.id, position)) xs in
          let eids xs =
            List.map (fun ((s : step), outgoing, position) -> (s.id, outgoing, position)) xs
          in
          equal
            (ids (hits (resolution ~from:kept ~upto ~resumes:true kept kept_taken)))
            (ids (hits rest))
            "rebuilt resolution scan differs from the dropped one";
          equal
            (eids (hits (equality ~from:ekept ~upto:upto_equality ~resumes:true ekept ekept_taken)))
            (eids (hits erest))
            "rebuilt equality scan differs from the dropped one"
        done );
  ]

let () = run tests
