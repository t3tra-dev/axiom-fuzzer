(* Vampire slice members (Vampire, Heuristic.of_vampire): slice parsing, precedence and weights,
   literal order and selection, preprocessing, clause selection and the LRS limits, and
   kernel-checked refutations of the members. *)
open Axiom_fuzzer
open Wire
open Test_support

let fn name args = Fn (Original name, args)
let c name = fn name []
let x = V (0, 0)
let y = V (0, 1)
let pos atom = { positive = true; atom }
let neg atom = { positive = false; atom }
let p name args = P (name, args)

let installed v ?goals ?counted ?ids clauses =
  let order = Ordering.create () in
  Vampire.install ?goals ?counted ?ids v order clauses;
  order

let tests =
  [
    ( "a slice string parses into Vampire's options",
      fun () ->
        let v =
          Vampire.parse
            "lrs+21_1_fde=unused:sos=on:random_seed=1621186814:s2pl=no:kws=arity_squared:av=off_1"
        in
        equal v.saturation Vampire.Lrs "saturation";
        equal v.selection 21 "selection";
        equal (v.age_ratio, v.weight_ratio) (1, 1) "ratio";
        check v.sos "sos";
        check (not v.avatar) "av=off";
        equal v.kbo_weights Vampire.Arity_squared "kws";
        equal v.s2pl Vampire.S2pl_no "s2pl";
        equal v.fde Vampire.Fde_unused "fde";
        equal v.deciseconds 1 "time";
        equal v.nongoal_weight (10, 1) "Vampire 5.1's default nwc is 10";
        let w = Vampire.parse "lrs-34_4_fs=off:lcm=predicate:fd=off:aac=none:fsr=off_2" in
        equal w.selection (-34) "negative selection";
        equal (w.age_ratio, w.weight_ratio) (1, 4) "a single number n is 1:n";
        check
          ((not w.forward_subsumption) && (not w.subsumption_resolution)
         && not w.forward_demodulation)
          "fs, fsr, fd off";
        equal w.lcm Vampire.Predicate "lcm";
        equal w.unported [ "aac=none" ] "unported options are listed";
        let d = Vampire.parse "dis+10_8:1_nwc=0.5:to=lpo:sp=occurrence_3" in
        equal d.saturation Vampire.Discount "discount";
        equal (d.age_ratio, d.weight_ratio) (8, 1) "a:w";
        equal d.nongoal_weight (50, 100) "nwc=x is (100x, 100)";
        check d.lpo "lpo";
        equal d.precedence Vampire.Occurrence "sp";
        check (Vampire.lookahead (Vampire.parse "lrs+1011_1_2")) "lookahead selection";
        check
          (rejects (fun () -> ignore (Vampire.parse "lrs+666_1_2")))
          "random selection is not ported" );
    ( "the age:weight balance selects as AWPassiveClauseContainer::popSelected",
      fun () ->
        let q = Passive.create ~mix:[ 1; 4 ] ~balance:(1, 4) ~ratio:10 () in
        (* Clause i: age i, weight 100 - i, so the two queues disagree on every pick. *)
        for i = 1 to 12 do
          Passive.add ~evals:[| (i, float_of_int (100 - i)); (100 - i, float_of_int i) |] q i 0
        done;
        let picks = List.init 12 (fun _ -> Option.get (Passive.take q)) in
        (* W A W W W W A W W W W A: by weight first (1 <= 4), then age, then four by weight. *)
        equal picks [ 12; 1; 11; 10; 9; 8; 2; 7; 6; 5; 4; 3 ] "balance order";
        let r = Passive.create ~mix:[ 8; 1 ] ~balance:(8, 1) ~ratio:10 () in
        for i = 1 to 6 do
          Passive.add ~evals:[| (i, 0.); (100 - i, 0.) |] r i 0
        done;
        let picks = List.init 6 (fun _ -> Option.get (Passive.take r)) in
        equal picks [ 1; 6; 2; 3; 4; 5 ] "8:1 starts by age, then one by weight" );
    ( "plsq: Vampire's split containers pick their queue by weighted round robin",
      fun () ->
        let v = Vampire.parse "lrs+4_2:3_plsq=on:plsqr=4,31:sac=on:to=lpo_3" in
        check v.positive_split "plsq";
        equal v.plsqr [ 4; 31 ] "plsqr";
        equal v.plsqc [ 0. ] "plsqc default: one cutoff at 0";
        check (not v.plsql) "plsql default off (tammet arrangement)";
        check v.split_at_activation "sac";
        let split =
          [ { Passive.split_feature = 0; ratios = [ 4; 31 ]; cutoffs = [ 0. ]; layered = false } ]
        in
        let q = Passive.create ~mix:[ 1; 1 ] ~balance:(1, 1) ~split ~ratio:10 () in
        (* Clauses 1..3 have no positive literal (queue 0), 10..19 one (queue 1); each leaf's
           queues order by id. *)
        let add id positives =
          Passive.add ~features:[| positives |] ~evals:[| (0, float_of_int id); (id, 0.) |] q id 0
        in
        List.iter (fun id -> add id 0) [ 1; 2; 3 ];
        List.iter (fun id -> add id 1) (List.init 10 (fun i -> 10 + i));
        let picks = List.init 10 (fun _ -> Option.get (Passive.take q)) in
        (* Inverted ratios 31:4 from equal balances: queue 0, eight times queue 1, queue 0 (the
           PLA031-1.005 slice's input clause neq1 at activation 10). *)
        equal picks [ 1; 10; 11; 12; 13; 14; 15; 16; 17; 2 ] "round robin";
        let r = Passive.create ~mix:[ 1; 1 ] ~balance:(1, 1) ~split ~ratio:10 () in
        Passive.add ~features:[| 1 |] ~evals:[| (0, 5.); (5, 0.) |] r 5 0;
        equal (Passive.take r) (Some 5) "an empty queue passes its turn to the next one";
        equal (Passive.take r) None "empty" );
    ( "the LRS simulation reads the limits where the queues stand",
      fun () ->
        let q = Passive.create ~mix:[ 1; 1 ] ~balance:(1, 1) ~ratio:10 () in
        List.iter
          (fun (id, age, w) ->
            Passive.add
              ~evals:[| (age, float_of_int ((2 * w) + 1)); (w, float_of_int ((2 * age) + 1)) |]
              q id 0)
          [ (1, 0, 9); (2, 1, 3); (3, 2, 5); (4, 3, 1); (5, 4, 7) ];
        match Passive.simulate_balance q ~count:2 with
        | None -> failwith "no simulation"
        | Some evals ->
            (* W (id 4), A (id 1): the age queue stands at id 2 (age 1, weight 3), the weight
               queue at id 2 (weight 3). *)
            let l = Vampire.limits_of evals in
            equal (l.max_age, l.max_age_weight, l.max_weight) (1, 3, 3) "limits";
            check (Vampire.exceeds_all_limits l ~age:2 ~weight:4) "older and heavier";
            check (not (Vampire.exceeds_all_limits l ~age:0 ~weight:50)) "young enough";
            check (not (Vampire.exceeds_all_limits l ~age:9 ~weight:3)) "light enough";
            check (Vampire.exceeds_all_limits l ~age:1 ~weight:4) "the age limit's weight";
            equal (Passive.length q) 5 "the simulation leaves the queues as they were";
            equal
              (Vampire.reachable ~activations:100 ~elapsed:10 ~since_first:10 ~budget:1000)
              None "no estimate before 5 % of the budget";
            equal
              (Vampire.reachable ~activations:100 ~elapsed:500 ~since_first:400 ~budget:1000)
              (Some 125) "activations times left over spent" );
    ( "symbol numbers follow Vampire's parser: postorder functions, predicates in order",
      fun () ->
        let text =
          "cnf(a,axiom,(~ q(f(g(b),X)) | p(X,c))).\ncnf(b,negated_conjecture,(f(c,b) != g(d))).\n"
        in
        match Vampire.parse_order_of_text text with
        | None -> failwith "unread"
        | Some ids ->
            let id head arity = Hashtbl.find ids (head, arity) in
            let f name arity = id (Ordering.Function (Original name)) arity in
            equal
              (f "b" 0, f "g" 1, f "f" 2, f "c" 0, f "d" 0)
              (0, 1, 2, 3, 4) "functions complete in postorder";
            equal (id (Ordering.Predicate "q") 1, id (Ordering.Predicate "p") 2) (0, 1) "predicates"
    );
    ( "frequency precedence, occurrence tie breaks and arity_squared weights",
      fun () ->
        let v = Vampire.parse "lrs+10_1_kws=arity_squared_1" in
        let clauses =
          [
            [ pos (p "p" [ fn "f" [ c "a"; c "b" ] ]) ];
            [ neg (p "p" [ fn "f" [ c "a"; fn "g" [ c "a" ] ] ]) ];
          ]
        in
        let tbl, _, _ = Vampire.table v clauses in
        let rank name arity = fst (Hashtbl.find tbl (Ordering.Function (Original name), arity)) in
        let weight name arity = snd (Hashtbl.find tbl (Ordering.Function (Original name), arity)) in
        (* a occurs 3 times (smallest), f twice, b and g once: rare is large, ties by number. *)
        check (rank "a" 0 < rank "f" 2) "frequent is small";
        check (rank "f" 2 < rank "b" 0 && rank "b" 0 < rank "g" 1) "ties by occurrence";
        equal (weight "a" 0, weight "g" 1, weight "f" 2) (1, 2, 5) "arity^2 + 1" );
    ( "Vampire's literal order: levels, equations by their sides, polarity only for complements",
      fun () ->
        let v = Vampire.parse "lrs+10_1_1" in
        let a = c "a" and b = c "b" in
        let order = installed v [ [ pos (p "q" [ a ]) ]; [ pos (E (fn "f" [ a ], b)) ] ] in
        let gt l r = Ordering.literal_greater ~order l r in
        check (gt (pos (p "q" [ a ])) (pos (E (fn "f" [ fn "f" [ a ] ], b)))) "equality is lowest";
        check (gt (pos (p "q" [ a ])) (neg (p "q" [ a ]))) "the negative complement is smaller";
        check
          (gt (neg (E (fn "f" [ a ], b))) (pos (E (a, b))))
          "equations compare by their sides, whatever the sign" );
    ( "selection functions 21, 10, -34 and 1",
      fun () ->
        let a = c "a" in
        let sel slice clause =
          let v = Vampire.parse slice in
          let order = installed v [ clause ] in
          let xs = Array.of_list clause in
          Vampire.select v
            ~id:(fun _ -> 0)
            ~greater:(fun i j -> Ordering.literal_greater ~order xs.(i) xs.(j))
            clause
        in
        (* ~r(X) | ~r(f(f(X))) | q(Y): two maximal literals (the last two); 21 takes the heaviest
           negative literal, 20 every maximal one. *)
        let clause =
          [ neg (p "r" [ x ]); neg (p "r" [ fn "f" [ fn "f" [ x ] ] ]); pos (p "q" [ y ]) ]
        in
        equal (sel "lrs+21_1_1" clause) [ 1 ] "21: heaviest negative";
        equal (sel "lrs+20_1_1" clause) [ 1; 2 ] "20: every maximal literal";
        equal (sel "lrs+10_1_1" clause) [ 1 ] "10: best negative by size";
        (* -34: reversed polarity, so a ground positive predicate literal is selected. *)
        let ground = [ pos (p "q" [ a ]); neg (p "r" [ x ]) ] in
        equal (sel "lrs-34_1_1" ground) [ 0 ] "-34: ground literal, reversed polarity";
        equal (sel "lrs+1_1_1" clause) [ 1 ] "1: a maximal negative literal" );
    ( "function definition elimination: unused definitions go, all are unfolded",
      fun () ->
        let a = c "a" in
        let clauses =
          [
            [ pos (E (fn "h" [ x ], fn "g" [ x; x ])) ];
            (* unused: only in its definition *)
            [ pos (E (fn "k" [ x ], fn "g" [ x; a ])) ];
            [ pos (p "q" [ fn "k" [ a ] ]) ];
            [ neg (p "q" [ fn "g" [ a; a ] ]) ];
          ]
        in
        let unused = Vampire.preprocess (Vampire.parse "lrs+10_1_fde=unused_1") clauses in
        (match unused.plan with
        | Some plan -> equal (List.map fst plan.removed) [ 0 ] "the unused definition"
        | None -> failwith "nothing removed");
        equal unused.order [ 1; 2; 3 ] "the kept definition comes first";
        let all = Vampire.preprocess (Vampire.parse "lrs+10_1_1") clauses in
        (match all.plan with
        | Some plan ->
            equal (List.sort compare (List.map fst plan.removed)) [ 0; 1 ] "both definitions";
            check (plan.clauses.(2) = [ pos (p "q" [ fn "g" [ a; a ] ]) ]) "k(a) unfolded to g(a,a)"
        | None -> failwith "nothing unfolded");
        equal
          (Vampire.eq_res_with_deletion [ neg (E (x, a)); pos (p "q" [ x ]) ])
          [ pos (p "q" [ a ]) ]
          "equality resolution with deletion" );
    ( "Vampire slice members refute problems with kernel-checked certificates",
      fun () ->
        let problem =
          (* s1, s2, s3 and d1 are the clauses subclass_members, not_subclass_members1,
             not_subclass_members2 and equal_implies_subclass1 of TPTP Axioms/SET004-0.ax,
             selected and renamed from the verbatim TPTP v10.0.0 file (attribution and terms:
             THIRD-PARTY.md); the goals are written for this test. *)
          Test_support.tptp_problem
            ~only:
              [
                "subclass_members";
                "not_subclass_members1";
                "not_subclass_members2";
                "equal_implies_subclass1";
              ]
            ~rename:
              [
                ("subclass_members", "s1");
                ("not_subclass_members1", "s2");
                ("not_subclass_members2", "s3");
                ("equal_implies_subclass1", "d1");
              ]
            "Axioms/SET004-0.ax"
          ^ "\n\
             cnf(g1,negated_conjecture,(subclass(a,b))).\n\
             cnf(g2,negated_conjecture,(subclass(b,c))).\n\
             cnf(g3,negated_conjecture,(~ subclass(a,c)))."
        in
        let t = Tptp.parse problem in
        List.iter
          (fun name ->
            let config =
              {
                Scheduler.default_config with
                reference = false;
                portfolio = Strategy.Uniform;
                engine =
                  {
                    Engine.default_config with
                    strategy = Strategy.of_name name;
                    goal_names = [ "g1"; "g2"; "g3" ];
                    vampire_symbols = Vampire.parse_order_of_text problem;
                    limits = { Engine.default_limits with seconds = 30. };
                  };
              }
            in
            let r = Scheduler.run config t in
            match r.certificate with
            | None -> failwith (name ^ ": " ^ r.reason)
            | Some cert -> check (Result.is_ok (Kernel.check t cert)) (name ^ ": kernel rejected"))
          (List.map fst Heuristic.vampire_slices) );
    ( "forward literal rewriting replaces a literal by an equivalent one through the kernel",
      fun () ->
        (* q(X) <=> p(X) from a two-literal clause and its complementary variant; the goal's
           ~r(f(a)) is rewritten with r(X) <=> p(X) only when that decreases the literal. *)
        let problem =
          "cnf(e1,axiom,(r(X) | ~ p(X))). cnf(e2,axiom,(~ r(X) | p(X))).\n\
           cnf(f1,axiom,(p(f(a)) | s(b))). cnf(f2,axiom,(~ s(b))).\n\
           cnf(g1,negated_conjecture,(~ r(f(a))))."
        in
        let t = Tptp.parse problem in
        let h = Heuristic.of_vampire "v:test" "lrs+10_1_flr=on:av=off_1" in
        let strategy =
          {
            Strategy.production with
            name = h.name;
            heuristic = Some h;
            maximal_candidates = true;
            ordered_rewriting = false;
            unfold = None;
          }
        in
        let config =
          {
            Scheduler.default_config with
            reference = false;
            portfolio = Strategy.Uniform;
            engine =
              {
                Engine.default_config with
                strategy;
                goal_names = [ "g1" ];
                vampire_symbols = Vampire.parse_order_of_text problem;
                limits = { Engine.default_limits with seconds = 30. };
              };
          }
        in
        let r = Scheduler.run config t in
        match r.certificate with
        | None -> failwith ("no refutation: " ^ r.reason)
        | Some cert -> check (Result.is_ok (Kernel.check t cert)) "kernel rejected" );
    ( "unit resulting resolution certifies its result as a chain of binary resolutions",
      fun () ->
        (* ~p(X) | ~q(X) | r(X) with the units p(a), q(a) gives r(a) in one inference. *)
        let problem =
          "cnf(c1,axiom,(~ p(X) | ~ q(X) | r(X))). cnf(c2,axiom,(p(a))). cnf(c3,axiom,(q(a))).\n\
           cnf(g1,negated_conjecture,(~ r(a)))."
        in
        let t = Tptp.parse problem in
        let h = Heuristic.of_vampire "v:test" "lrs+10_1_urr=on:av=off:br=off_1" in
        let strategy =
          {
            Strategy.production with
            name = h.name;
            heuristic = Some h;
            maximal_candidates = true;
            ordered_rewriting = false;
            unfold = None;
          }
        in
        let config =
          {
            Scheduler.default_config with
            reference = false;
            portfolio = Strategy.Uniform;
            engine =
              {
                Engine.default_config with
                strategy;
                goal_names = [ "g1" ];
                vampire_symbols = Vampire.parse_order_of_text problem;
                limits = { Engine.default_limits with seconds = 30. };
              };
          }
        in
        let r = Scheduler.run config t in
        match r.certificate with
        | None -> failwith ("no refutation: " ^ r.reason)
        | Some cert -> check (Result.is_ok (Kernel.check t cert)) "kernel rejected" );
    ( "a listed resolution partner retired before its group is made is skipped",
      fun () ->
        (* A Vampire slice member lists its given's resolution partners when the work is prepared
           (in its substitution tree's order). A listed partner can leave the retained index
           before its group is made (between the work's quanta: an AVATAR model change disables
           it, or the given's own activation retires it): it then gets a stale ticket, and its
           group is cancelled, as the lazy cursor of the other members skips a dead posting. It
           used to raise Not_found (v:dis10 on three problems of the development corpus). *)
        let theory =
          Tptp.parse "cnf(g,axiom,(~ p(X) | r(X))). cnf(a,axiom,(p(a))). cnf(b,axiom,(p(b)))."
        in
        let h = Heuristic.of_vampire "v:test" "lrs+10_1_av=off_1" in
        let strategy =
          {
            Strategy.production with
            name = h.name;
            heuristic = Some h;
            maximal_candidates = true;
            ordered_rewriting = false;
            unfold = None;
          }
        in
        let e = Engine.create { Engine.default_config with strategy; avatar = false } in
        List.iter (Engine.add_axiom e) (Theory.fixed theory);
        let given = Proof.get e.proof 0 and a = Proof.get e.proof 1 and b = Proof.get e.proof 2 in
        Engine.activate e a;
        Engine.activate e b;
        let work = Engine.prepare_inferences e given in
        Engine.retire e a.id;
        let cancelled = e.metrics.inference_cancelled and generated = e.metrics.generated in
        check (Engine.advance_inference e work) "the given's work did not finish";
        check (e.metrics.inference_cancelled > cancelled) "the retired partner's group ran";
        equal (e.metrics.generated - generated) 1 "not exactly one resolvent";
        equal (Proof.get e.proof (Proof.length e.proof - 1)).clause
          [ pos (p "r" [ c "b" ]) ]
          ("the resolvent is not the live partner's (" ^ string_of_int b.id ^ ")") );
    ( "the E ports carry no Vampire slice",
      fun () ->
        List.iter
          (fun (h : Heuristic.t) ->
            let vampire = String.length h.name > 2 && String.sub h.name 0 2 = "v:" in
            check (vampire = (h.vampire <> None)) (h.name ^ ": vampire field"))
          Heuristic.named );
  ]

let () = run tests
