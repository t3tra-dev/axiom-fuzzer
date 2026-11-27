open Axiom_fuzzer
open Test_support
open Wire

let tests =
  [
    ( "subsumption resolution agrees with independent replay and its candidate index",
      fun () ->
        let rng = Random.State.make [| 20261104; 203 |] in
        let term () =
          match Random.State.int rng 4 with
          | 0 -> v 0
          | 1 -> v 1
          | 2 -> constant "a"
          | _ -> constant "b"
        in
        let literal () =
          let atom =
            match Random.State.int rng 4 with
            | 0 -> p [ term (); term () ]
            | 1 -> P ("q", [ term () ])
            | 2 -> E (term (), term ())
            | _ -> D ((0, 0), [ term () ])
          in
          { positive = Random.State.bool rng; atom }
        in
        let entries =
          List.init 70 (fun id ->
              {
                id;
                clause =
                  Clause.normalize (List.init (1 + Random.State.int rng 4) (fun _ -> literal ()));
                rule = Input (id, 0);
              })
        in
        let index = Subsumption_index.create () in
        List.iter (Subsumption_index.add index) entries;
        let successes = ref 0 in
        let compare deleted =
          List.iter
            (fun target ->
              let candidates = Subsumption_index.resolution ~budget:100000 index target.clause in
              List.iter
                (fun (s : step) -> check (not (deleted s.id)) "removed candidate revived")
                candidates;
              List.iter
                (fun side ->
                  if not (deleted side.id) then
                    match Subsumption.resolve ~budget:100000 side target with
                    | None -> ()
                    | Some (clause, rule) ->
                        incr successes;
                        check
                          (List.exists (fun (s : step) -> s.id = side.id) candidates)
                          "resolution index missed a valid shortening";
                        check
                          (List.length clause < List.length target.clause)
                          "target did not shrink";
                        equal
                          (Kernel.derive ~inputs:[] ~steps:[ side; target ] rule)
                          (Ok (Clause.normalize clause))
                          "shortening disagreed with replay")
                entries)
            entries
        in
        compare (fun _ -> false);
        List.iter
          (fun (s : step) -> if s.id mod 3 = 0 then Subsumption_index.remove index s.id)
          entries;
        compare (fun id -> id mod 3 = 0);
        check (!successes > 30) "random fixture exercised too few contractions" );
    ( "occurrence and fingerprint indices preserve ordered inference outputs",
      fun () ->
        let rng = Random.State.make [| 20261104; 73 |] in
        let rec term depth =
          if depth = 0 then
            if Random.State.bool rng then v (Random.State.int rng 3) else constant "a"
          else
            match Random.State.int rng 4 with
            | 0 -> v (Random.State.int rng 3)
            | 1 -> constant "b"
            | _ ->
                Fn
                  ( Original (if Random.State.bool rng then "f" else "g"),
                    List.init (1 + Random.State.int rng 2) (fun _ -> term (depth - 1)) )
        in
        let literal () =
          let atom =
            match Random.State.int rng 3 with
            | 0 -> P ("p", [ term 2; term 1 ])
            | 1 -> E (term 2, term 1)
            | _ -> D ((1, 0), [ term 1 ])
          in
          { positive = Random.State.bool rng; atom }
        in
        let clauses =
          [
            [ positive (E (v 0, Fn (Original "f", [ v 1 ]))); negative (p [ v 0 ]) ];
            [ positive (p [ Fn (Original "f", [ v 0 ]) ]); negative (p [ v 1 ]) ];
            [
              positive (E (constant "a", constant "b")); positive (p [ constant "a"; constant "a" ]);
            ];
            [ negative (E (constant "b", constant "a")) ];
          ]
          @ List.init 24 (fun _ -> List.init (1 + Random.State.int rng 4) (fun _ -> literal ()))
        in
        let entries = List.mapi (fun id clause -> { id; clause; rule = Input (id, 0) }) clauses in
        List.iter
          (fun fingerprint ->
            let index = Index.create ~fingerprint () in
            let equality = Equality_index.create ~fingerprint () in
            List.iter
              (fun s ->
                Index.add index s;
                Equality_index.add equality s)
              entries;
            List.iter
              (fun (ordered, variables) ->
                let calc =
                  Calculus.create ~ordered ~variable_positions:variables (Term.create ())
                in
                List.iter
                  (fun (s : step) ->
                    (* Exercise both an explicit no-selection choice and fixed
                       choices other than the first negative literal. *)
                    if s.id mod 3 = 0 then Tbl.Int.replace calc.selected s.id None
                    else
                      List.iteri
                        (fun i l ->
                          if not l.positive then Tbl.Int.replace calc.selected s.id (Some [ i ]))
                        s.clause)
                  entries;
                let index = Index.create ~fingerprint () in
                let equality = Equality_index.create ~fingerprint () in
                List.iter
                  (fun given ->
                    let eligible = Calculus.potential calc (Calculus.selected calc given) in
                    Index.add ~eligible index given;
                    Equality_index.add ~eligible equality given)
                  entries;
                let collect f =
                  let xs = ref [] in
                  f (fun clause rule -> xs := (clause, rule) :: !xs);
                  List.rev !xs
                in
                let resumed cursor =
                  let xs = ref [] in
                  Seq.iter
                    (fun attempt ->
                      equal (Unify.mark calc.unifier) 0 "cursor retained a live unifier trail";
                      Term.clear calc.unifier.arena;
                      attempt (fun clause rule -> xs := (clause, rule) :: !xs);
                      equal (Unify.mark calc.unifier) 0 "attempt did not roll back")
                    cursor;
                  List.rev !xs
                in
                List.iter
                  (fun given ->
                    equal
                      (resumed (Calculus.equality_factor_cursor calc given))
                      (collect (Calculus.equality_factor calc given))
                      "equality factoring cursor changed after arena collection";
                    let eligible = Calculus.potential calc (Calculus.selected calc given) in
                    let res = Index.matches ~eligible index given.clause in
                    let eq = Equality_index.matches ~eligible equality ~variables given.clause in
                    let streamed =
                      Index.cursor ~eligible index given.clause
                      |> Seq.filter_map Fun.id |> List.of_seq
                      |> List.map (fun ((s : step), position) -> (s.id, position))
                      |> List.sort_uniq compare
                    in
                    equal streamed
                      (List.concat_map
                         (fun ((s : step), positions) -> List.map (fun p -> (s.id, p)) positions)
                         res
                      |> List.sort_uniq compare)
                      "incremental resolution scan changed its positions";
                    let streamed =
                      Equality_index.cursor ~eligible equality ~variables given.clause
                      |> Seq.filter_map Fun.id |> List.of_seq
                      |> List.map (fun ((s : step), out_, position) -> (s.id, out_, position))
                      |> List.sort_uniq compare
                    in
                    equal streamed
                      (List.concat_map
                         (fun ((s : step), out_, in_) ->
                           List.map (fun p -> (s.id, true, p)) out_
                           @ List.map (fun p -> (s.id, false, p)) in_)
                         eq
                      |> List.sort_uniq compare)
                      "incremental equality scan changed its positions";
                    List.iter
                      (fun other ->
                        let pairs =
                          match List.find_opt (fun ((s : step), _) -> s.id = other.id) res with
                          | None -> []
                          | Some (_, pairs) -> pairs
                        in
                        equal
                          (collect (Calculus.resolve ~positions:pairs calc given other))
                          (collect (Calculus.resolve calc given other))
                          "resolution occurrence mismatch";
                        equal
                          (resumed (Calculus.resolve_cursor ~positions:pairs calc given other))
                          (collect (Calculus.resolve ~positions:pairs calc given other))
                          "resolution cursor changed after arena collection";
                        let out_, in_ =
                          match List.find_opt (fun ((s : step), _, _) -> s.id = other.id) eq with
                          | None -> ([], [])
                          | Some (_, out_, in_) -> (out_, in_)
                        in
                        equal
                          (collect (Calculus.paramodulate ~positions:out_ calc given other))
                          (collect (Calculus.paramodulate calc given other))
                          "outgoing position/side mismatch";
                        equal
                          (resumed (Calculus.paramodulate_cursor ~positions:out_ calc given other))
                          (collect (Calculus.paramodulate ~positions:out_ calc given other))
                          "superposition cursor changed after arena collection";
                        equal
                          (collect (Calculus.paramodulate ~positions:in_ calc other given))
                          (collect (Calculus.paramodulate calc other given))
                          "incoming position/side mismatch")
                      entries)
                  entries)
              [ (false, true); (true, false) ];
            List.iter
              (fun (s : step) ->
                if s.id mod 2 = 0 then (
                  Index.remove index s.id;
                  Equality_index.remove equality s.id))
              entries;
            Index.compact index;
            Equality_index.compact equality;
            List.iter
              (fun given ->
                check
                  (List.for_all
                     (fun ((s : step), _) -> s.id mod 2 = 1)
                     (Index.matches index given.clause))
                  "compacted resolution posting resurrected a clause";
                check
                  (List.for_all
                     (fun ((s : step), _, _) -> s.id mod 2 = 1)
                     (Equality_index.matches equality ~variables:true given.clause))
                  "compacted equality posting resurrected a clause")
              entries)
          [ false; true ] );
    ( "sorted tautology detection agrees with pairwise comparison",
      fun () ->
        let atoms =
          [
            p [ v 0 ];
            p [ v 1 ];
            p [ constant "a" ];
            E (v 0, v 0);
            E (v 0, v 1);
            E (v 1, v 0);
            D ((1, 2), [ v 0 ]);
          ]
        in
        let literals = List.concat_map (fun atom -> [ positive atom; negative atom ]) atoms in
        let check_clause clause =
          equal
            (Clause.tautology_sorted (List.sort compare clause))
            (Clause.tautology clause) "sorted complement scan changed tautology detection"
        in
        check_clause [];
        List.iter
          (fun l ->
            check_clause [ l ];
            List.iter
              (fun r ->
                check_clause [ l; r ];
                List.iter (fun s -> check_clause [ l; r; s ]) literals)
              literals)
          literals;
        let rng = Random.State.make [| 20261104; 31 |] in
        for _ = 1 to 500 do
          check_clause
            (List.init (Random.State.int rng 100) (fun _ ->
                 List.nth literals (Random.State.int rng (List.length literals))))
        done );
    ( "filtered unification agrees with direct trail unification",
      fun () ->
        let rng = Random.State.make [| 20261104; 17 |] in
        let rec term depth =
          if depth = 0 || Random.State.int rng 3 = 0 then
            if Random.State.bool rng then V (Random.State.int rng 3, Random.State.int rng 4)
            else constant (if Random.State.bool rng then "a" else "b")
          else
            Fn
              ( (if Random.State.bool rng then Original "f" else Skolem (2, 1)),
                List.init (1 + Random.State.int rng 2) (fun _ -> term (depth - 1)) )
        in
        let reference = Unify.create (Term.create ()) in
        let filtered = Unify.create (Term.create ()) in
        let select apply =
          apply (Fn (Original "f", [ v 0; v 1 ]))
          <> Fn (Original "f", [ constant "a"; constant "b" ])
        in
        for _ = 1 to 1000 do
          let equations = List.init (Random.State.int rng 4) (fun _ -> (term 2, term 2)) in
          let expected =
            Fun.protect
              ~finally:(fun () -> Unify.rollback reference 0)
              (fun () ->
                if
                  List.for_all
                    (fun (s, t) ->
                      Unify.unify reference (Term.of_wire reference.arena s)
                        (Term.of_wire reference.arena t))
                    equations
                then Some (Unify.capture reference)
                else None)
          in
          let expected =
            Option.bind expected (fun sigma ->
                let apply =
                  Clause.map_vars (fun v -> Option.value ~default:(V v) (List.assoc_opt v sigma))
                in
                if select apply then Some sigma else None)
          in
          let actual = ref None in
          Unify.solve filtered equations ~accept:select (fun sigma _ -> actual := Some sigma);
          equal !actual expected "prefilter or live acceptance changed the solution";
          equal (Unify.mark filtered) 0 "filtered trial leaked bindings"
        done );
    ( "lazy literal eligibility agrees with eager substitution",
      fun () ->
        let rng = Random.State.make [| 20261104; 23 |] in
        let term () =
          match Random.State.int rng 4 with
          | 0 -> constant "a"
          | 1 -> v 0
          | 2 -> v 1
          | _ -> Fn (Original "f", [ v 0; v 1 ])
        in
        let literal () =
          let atom =
            match Random.State.int rng 3 with
            | 0 -> E (term (), term ())
            | 1 -> P ("p", [ term (); term () ])
            | _ -> D ((2, 3), [ term () ])
          in
          { positive = Random.State.bool rng; atom }
        in
        for _ = 1 to 300 do
          let clause = List.init (1 + Random.State.int rng 6) (fun _ -> literal ()) in
          let replacements = [ term (); term () ] in
          let apply = Clause.map_vars (fun (_, i) -> List.nth replacements i) in
          List.iter
            (fun selection ->
              List.iter
                (fun strict ->
                  List.iteri
                    (fun index _ ->
                      let selected =
                        if selection then
                          List.find_opt
                            (fun (_, l) -> not l.positive)
                            (List.mapi (fun i l -> (i, l)) clause)
                        else None
                      in
                      let expected =
                        match selected with
                        | Some (i, _) -> i = index
                        | None ->
                            let literals = List.map (Clause.map_literal apply) clause in
                            let pivot = List.nth literals index in
                            List.for_all
                              (fun (j, l) ->
                                j = index
                                || not
                                     (Ordering.literal_greater l pivot
                                     || (strict && Ordering.literal_equal l pivot)))
                              (List.mapi (fun i l -> (i, l)) literals)
                      in
                      equal
                        (Ordering.eligible ~selection ~strict clause index apply)
                        expected "lazy ordering changed eligible literals")
                    clause)
                [ false; true ])
            [ false; true ]
        done );
    ( "ordered ground equality agrees with finite model enumeration",
      fun () ->
        let rng = Random.State.make [| 320614 |] in
        let names = [| "a"; "b"; "c" |] in
        let st i = App (names.(i), []) in
        let atoms =
          [
            Eq (st 0, st 1);
            Eq (st 0, st 2);
            Eq (st 1, st 2);
            Pred ("p", [ st 0 ]);
            Pred ("p", [ st 1 ]);
            Pred ("p", [ st 2 ]);
          ]
        in
        let models =
          List.concat_map
            (fun assignment -> List.init 8 (fun mask -> (assignment, mask)))
            [ [| 0; 0; 0 |]; [| 0; 0; 1 |]; [| 0; 1; 0 |]; [| 0; 1; 1 |]; [| 0; 1; 2 |] ]
        in
        let truth (assignment, mask) formula =
          let value = function
            | App (s, []) -> assignment.(if s = "a" then 0 else if s = "b" then 1 else 2)
            | _ -> assert false
          in
          let atom = function
            | Eq (s, t) -> value s = value t
            | Pred ("p", [ s ]) -> mask land (1 lsl value s) <> 0
            | _ -> assert false
          in
          match formula with Neg a -> not (atom a) | a -> atom a
        in
        for trial = 0 to 39 do
          let clauses =
            List.init
              (4 + Random.State.int rng 5)
              (fun _ ->
                List.init
                  (1 + Random.State.int rng 3)
                  (fun _ ->
                    let atom = List.nth atoms (Random.State.int rng 6) in
                    if Random.State.bool rng then atom else Neg atom))
          in
          let satisfiable =
            List.exists (fun model -> List.for_all (List.exists (truth model)) clauses) models
          in
          List.iter
            (fun (ordered, selection, demodulation, backward_demodulation, lookahead) ->
              let theory =
                Theory.custom ~name:"ground-models"
                  (Signature.make
                     ~functions:[ ("a", 0); ("b", 0); ("c", 0) ]
                     ~predicates:[ ("p", 1) ])
                  (List.mapi (fun i c -> (string_of_int i, Disj c)) clauses)
              in
              let result =
                Scheduler.run
                  {
                    config with
                    engine =
                      {
                        config.engine with
                        ordered;
                        selection;
                        demodulation;
                        backward_demodulation;
                        lookahead;
                        clause_weight = (if lookahead = 0 then Passive.Size else Passive.Mixed);
                        limits =
                          {
                            config.engine.limits with
                            max_given = 2000;
                            max_generated = 20000;
                            max_retained = 15000;
                          };
                      };
                  }
                  theory
              in
              equal
                (Option.is_none result.certificate)
                satisfiable
                (Printf.sprintf "ground model disagreement, trial=%d ordered=%b selection=%b" trial
                   ordered selection))
            [
              (false, false, false, false, 0);
              (true, false, false, false, 0);
              (true, true, true, false, 0);
              (true, true, true, true, 0);
              (true, true, true, true, 32);
            ]
        done );
    ( "ordered inference preserves benchmark refutations",
      fun () ->
        List.iter
          (fun name ->
            List.iter
              (fun selection ->
                let ordered =
                  {
                    config with
                    engine =
                      {
                        config.engine with
                        ordered = true;
                        selection;
                        demodulation = true;
                        limits =
                          {
                            config.engine.limits with
                            max_generated = 15000;
                            max_retained = 12000;
                            max_given = 300;
                          };
                      };
                  }
                in
                let t, c, _ = prove ~config:ordered name in
                check (Result.is_ok (Kernel.check t c)) "ordered proof failed independent replay")
              [ false; true ])
          [ "naive"; "separation-universal"; "foundation-self"; "mutated-separation" ] );
    ( "backward demodulation index agrees with scan and preserves matching targets",
      fun () ->
        let rules =
          [
            Fn (Original "f", [ v 0 ]);
            Fn (Original "f", [ constant "a" ]);
            Fn (Original "g", [ v 0; v 0 ]);
          ]
        in
        let terms =
          [
            v 0;
            constant "a";
            Fn (Original "f", [ v 1 ]);
            Fn (Original "f", [ constant "a" ]);
            Fn (Original "g", [ constant "a"; constant "b" ]);
            Fn (Original "g", [ v 1; v 1 ]);
            Fn (Original "h", [ Fn (Original "f", [ constant "a" ]) ]);
          ]
        in
        let entries =
          List.mapi
            (fun id term -> { id; rule = Input (id, 0); clause = [ positive (p [ term ]) ] })
            terms
        in
        let index = Equality_index.create () in
        List.iter (Equality_index.add index) entries;
        List.iter
          (fun lhs ->
            let rw =
              { id = 100; rule = Input (100, 0); clause = [ positive (E (lhs, constant "a")) ] }
            in
            let rewriter = Demodulation.create () in
            Demodulation.add rewriter rw;
            let candidates =
              Equality_index.rewrite_targets index lhs |> List.map (fun (s : step) -> s.id)
            in
            List.iter
              (fun (s : step) ->
                if Demodulation.rewrite_once rewriter s <> None then
                  check (List.mem s.id candidates) "backward index lost a real match")
              entries)
          rules;
        Equality_index.remove index 3;
        check
          (not
             (List.exists
                (fun (s : step) -> s.id = 3)
                (Equality_index.rewrite_targets index (List.hd rules))))
          "retired rewrite target returned";
        let input =
          "fof(old,axiom,(p(f(a)) | ~q(a))). fof(rule,axiom,(![X]:f(X)=X)). fof(q,axiom,q(a)). \
           fof(n,axiom,~p(a))."
        in
        let cfg =
          {
            config with
            engine =
              {
                config.engine with
                ordered = true;
                demodulation = true;
                backward_demodulation = true;
                weight_ratio = 0;
              };
          }
        in
        let a = Scheduler.run cfg (Tptp.parse input) in
        let b =
          Scheduler.run
            { cfg with engine = { cfg.engine with equality_indexed = false } }
            (Tptp.parse input)
        in
        equal a.certificate b.certificate "backward index changed the proof";
        equal
          ( a.engine.metrics.generated,
            a.engine.metrics.retained,
            a.engine.metrics.backward_demodulated )
          ( b.engine.metrics.generated,
            b.engine.metrics.retained,
            b.engine.metrics.backward_demodulated )
          "backward index changed search work" );
    ( "equality postings preserve every paramodulation direction",
      fun () ->
        let terms =
          [
            v 0;
            v 1;
            constant "a";
            constant "b";
            Fn (Original "f", [ v 0 ]);
            Fn (Original "f", [ Fn (Original "g", [ constant "a" ]) ]);
          ]
        in
        let clauses =
          List.concat_map
            (fun x ->
              List.concat_map
                (fun y ->
                  [
                    [ positive (E (x, y)); negative (p [ x ]) ];
                    [ positive (p [ Fn (Original "f", [ x ]) ]); negative (E (x, y)) ];
                  ])
                terms)
            terms
        in
        let entries = List.mapi (fun id clause -> { id; clause; rule = Input (id, 0) }) clauses in
        let index = Equality_index.create () in
        List.iter (Equality_index.add index) entries;
        List.iter
          (fun variables ->
            let calculus = Calculus.create ~variable_positions:variables (Term.create ()) in
            List.iter
              (fun (given : step) ->
                let candidates = Equality_index.partners index ~variables given.clause in
                List.iter
                  (fun (other : step) ->
                    let outgoing = ref false and incoming = ref false in
                    Calculus.paramodulate calculus given other (fun _ _ -> outgoing := true);
                    Calculus.paramodulate calculus other given (fun _ _ -> incoming := true);
                    if !outgoing || !incoming then (
                      let _, out_, in_ =
                        List.find (fun ((s : step), _, _) -> s.id = other.id) candidates
                      in
                      check ((not !outgoing) || out_) "outgoing paramodulation lost";
                      check ((not !incoming) || in_) "incoming paramodulation lost"))
                  entries)
              entries)
          [ false; true ];
        List.iter
          (fun (s : step) -> if s.id mod 2 = 0 then Equality_index.remove index s.id)
          entries;
        List.iter
          (fun (s : step) ->
            check
              (List.for_all
                 (fun ((p : step), _, _) -> p.id mod 2 <> 0)
                 (Equality_index.partners index ~variables:true s.clause))
              "retired equality partner returned")
          entries );
    ( "subsumption and its trie agree with scoped exhaustive matching after deletion",
      fun () ->
        (* Multiset subsumption: each pattern literal consumes its own target. *)
        let reference c d =
          let rec search env targets = function
            | [] -> true
            | p :: rest ->
                List.exists
                  (fun (j, target) ->
                    let remaining = List.filter (fun (k, _) -> k <> j) targets in
                    let attempt atom =
                      try search (Subsumption.atom env p.atom atom) remaining rest
                      with Subsumption.No_match -> false
                    in
                    p.positive = target.positive
                    && (attempt target.atom
                       || match target.atom with E (a, b) -> attempt (E (b, a)) | _ -> false))
                  targets
          in
          search [] (List.mapi (fun j l -> (j, l)) d) c
        in
        let rng = Random.State.make [| 7341 |] in
        let rec term depth =
          match Random.State.int rng (if depth = 0 then 3 else 4) with
          | 0 -> v (Random.State.int rng 3)
          | 1 -> constant "a"
          | 2 -> constant "b"
          | _ -> Fn (Original "f", [ term (depth - 1); term (depth - 1) ])
        in
        let literal () =
          let a = term 2 and b = term 2 in
          let atom =
            match Random.State.int rng 4 with
            | 0 -> P ("p", [ a ])
            | 1 -> P ("q", [ a; b ])
            | 2 -> E (a, b)
            | _ -> D ((0, 0), [ a ])
          in
          { positive = Random.State.bool rng; atom }
        in
        let clauses =
          [ []; [ positive (p [ v 0 ]); positive (p [ v 1 ]) ]; [ positive (p [ constant "a" ]) ] ]
          @ List.init 90 (fun _ ->
              Clause.normalize (List.init (1 + Random.State.int rng 4) (fun _ -> literal ())))
        in
        let expanded =
          List.map
            (fun c ->
              List.map
                (Clause.map_literal
                   (Clause.map_vars (fun (_, i) -> Fn (Original "f", [ v i; constant "a" ]))))
                c)
            clauses
        in
        let clauses = clauses @ expanded in
        let entries = List.mapi (fun id clause -> { id; clause; rule = Input (id, 0) }) clauses in
        let index = Subsumption_index.create () in
        List.iter (Subsumption_index.add index) entries;
        let validate live =
          List.iter
            (fun query ->
              let forwards =
                Subsumption_index.forward index query |> List.map (fun (s : step) -> s.id)
              in
              let backwards =
                Subsumption_index.backward index query |> List.map (fun (s : step) -> s.id)
              in
              equal forwards (List.sort_uniq compare forwards)
                "candidate order or uniqueness changed";
              List.iter
                (fun (s : step) ->
                  if live s.id then (
                    equal
                      (Subsumption.subsumes ~budget:100000 s.clause query)
                      (reference (Clause.scope 1 s.clause) (Clause.scope 2 query))
                      "rigid matching disagrees with the scoped exhaustive oracle";
                    if Subsumption.subsumes s.clause query then
                      check (List.mem s.id forwards) "forward index lost a subsumer";
                    if Subsumption.subsumes query s.clause then
                      check (List.mem s.id backwards) "backward index lost a subsumed clause")
                  else
                    check
                      (not (List.mem s.id forwards || List.mem s.id backwards))
                      "index resurrected retired clause")
                entries)
            clauses
        in
        validate (fun _ -> true);
        List.iter
          (fun (s : step) -> if s.id mod 3 = 0 then Subsumption_index.remove index s.id)
          entries;
        validate (fun id -> id mod 3 <> 0) );
    ( "subsumption indexing preserves checked bounded refutations",
      fun () ->
        List.iter
          (fun name ->
            let bounded =
              {
                config with
                max_instances = 8;
                engine =
                  {
                    config.engine with
                    variants = false;
                    limits = { config.engine.limits with max_given = 30 };
                  };
              }
            in
            let a = Scheduler.run bounded (Theory.create name) in
            let b =
              Scheduler.run
                { bounded with engine = { bounded.engine with subsumption_indexed = false } }
                (Theory.create name)
            in
            (* Bounded contraction and measured work can change scheduling; the
               index's exhaustive candidate contract is tested separately. *)
            equal (Option.is_some a.certificate) (Option.is_some b.certificate)
              "index lost a bounded refutation";
            List.iter
              (fun result ->
                Option.iter
                  (fun proof ->
                    check
                      (Result.is_ok (Kernel.check (Theory.create name) proof))
                      "indexed or scanned refutation failed replay")
                  result.Scheduler.certificate)
              [ a; b ])
          [ "naive"; "separation"; "zf" ] );
    ( "index has no false negatives against brute-force unification",
      fun () ->
        let terms =
          [
            v 0;
            v 1;
            constant "a";
            constant "b";
            Fn (Original "f", [ v 0 ]);
            Fn (Original "f", [ constant "a" ]);
          ]
        in
        let atoms =
          List.concat_map
            (fun x -> List.concat_map (fun y -> [ P ("p", [ x; y ]); E (x, y) ]) terms)
            terms
        in
        let index = Index.create () in
        List.iteri
          (fun id atom -> Index.add index { id; clause = [ negative atom ]; rule = Input (id, 0) })
          atoms;
        let unifier = Unify.create (Term.create ()) in
        List.iter
          (fun atom ->
            let candidates =
              Index.partners index [ positive atom ] |> List.map (fun (s : step) -> s.id)
            in
            List.iteri
              (fun id other ->
                let possible = ref false in
                List.iter
                  (fun equations -> Unify.solve unifier equations (fun _ _ -> possible := true))
                  (Calculus.equations atom other);
                if !possible then
                  check (List.mem id candidates) "index removed a unifiable candidate")
              atoms)
          atoms );
    ( "indexed and brute-force engines find the same benchmark refutations",
      fun () ->
        (* Work-based scheduling interleaves the brute-force scan differently.
           This checks replay/core agreement, not a tight performance budget. *)
        let config =
          {
            config with
            engine =
              {
                config.engine with
                limits =
                  {
                    Engine.seconds = 10.;
                    max_given = 500;
                    max_generated = 20000;
                    max_retained = 15000;
                  };
              };
          }
        in
        List.iter
          (fun name ->
            let theory, a, _ = prove ~config name in
            let brute = { config with engine = { config.engine with indexed = false } } in
            let t, b, _ = prove ~config:brute name in
            check (Result.is_ok (Kernel.check theory a)) "indexed proof failed";
            check (Result.is_ok (Kernel.check t b)) "brute force proof failed";
            (* Work-based scheduling may inject different instances of the same schema. *)
            let sources c =
              List.map
                (fun (a : axiom) ->
                  match a.origin with
                  | Instance (schema, _) -> Wire.schema_name schema
                  | _ -> a.name)
                c.axioms
              |> List.sort_uniq compare
            in
            equal (sources a) (sources b) "index changed the benchmark core")
          [ "naive"; "separation-universal"; "foundation-self" ] );
    ( "Rocq checker rejects false first-order derivations",
      fun () ->
        let module R = Rocq_checker in
        let p = R.Pred (0, [ R.Var 0 ]) in
        check
          (not (R.check [ [ (true, p) ] ] [ (R.Input 0, []) ]))
          "unchecked input could assert bottom";
        check
          (not
             (R.check
                [ [ (true, p) ]; [ (false, R.Pred (1, [ R.Var 0 ])) ] ]
                [
                  (R.Input 0, [ (true, p) ]);
                  (R.Input 1, [ (false, R.Pred (1, [ R.Var 0 ])) ]);
                  (R.Resolve (0, 0, 1, 0), []);
                ]))
          "different predicates resolved";
        check
          (R.check
             [ [ (true, p) ]; [ (false, p) ] ]
             [
               (R.Input 0, [ (true, p) ]); (R.Input 1, [ (false, p) ]); (R.Resolve (0, 0, 1, 0), []);
             ])
          "valid primitive proof rejected" );
  ]

let () = run tests
