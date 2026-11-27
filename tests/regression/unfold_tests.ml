open Axiom_fuzzer
open Test_support
open Wire

(* Equational-definition unfolding (Unfold, Engine.add_initial_axioms). *)

let f name args = Fn (Original name, args)
let x = v 0
let y = v 1
let eq s t = [ positive (E (s, t)) ]

let defined = function
  | Some (d : Unfold.definition) -> Some (d.symbol, d.arity, d.reverse)
  | None -> None

let rec mentions name = function
  | V _ -> false
  | Fn (Original g, ts) -> g = name || List.exists (mentions name) ts
  | Fn (Skolem _, ts) -> List.exists (mentions name) ts

let clause_mentions name c =
  List.exists (fun (l : literal) -> List.exists (mentions name) (Clause.atom_terms l.atom)) c

let unfolding ?(limit = Unfold.default_limit) (s : Strategy.t) = { s with unfold = Some limit }

let engine_config strategy =
  {
    Engine.default_config with
    strategy;
    limits =
      { Engine.seconds = 10.; max_given = 5000; max_generated = 200000; max_retained = 200000 };
  }

(* Associator and commutator definitions as in RNG019-7, over a small ring fragment: assoc_def,
   comm_def, left_zero and inverse are the clauses associator, commutator, left_additive_identity
   and right_additive_inverse of Axioms/RNG003-0.ax, the include of TPTP RNG019-7, selected and
   renamed from the verbatim TPTP v10.0.0 files (attribution and terms: THIRD-PARTY.md);
   assoc_mult and goal are written for this test. *)
let ring () =
  tptp_problem
    ~only:[ "associator"; "commutator"; "left_additive_identity"; "right_additive_inverse" ]
    ~rename:
      [
        ("associator", "assoc_def");
        ("commutator", "comm_def");
        ("left_additive_identity", "left_zero");
        ("right_additive_inverse", "inverse");
      ]
    "Problems/RNG/RNG019-7.p"
  ^ "\n\
     cnf(assoc_mult,axiom,multiply(multiply(X,Y),Z) = multiply(X,multiply(Y,Z))).\n\
     cnf(goal,negated_conjecture,associator(a,b,c) != additive_identity)."

let problem_without_definitions =
  "cnf(a1,axiom,f(f(X)) = X). cnf(a2,axiom,(p(X) | q(f(X)))). cnf(a3,axiom,~q(X) | p(f(X))). \
   cnf(goal,negated_conjecture,~p(a))."

let run_engine config theory axioms =
  let e = Engine.create config in
  Engine.add_initial_axioms e axioms;
  Engine.finish e;
  (match Engine.certificate e ~theory:(Theory.name theory) with
  | Some cert -> ( match Kernel.check theory cert with Ok _ -> () | Error error -> failwith error)
  | None -> ());
  e

let tests =
  [
    ( "definitions follow E's EqnIsDefinition",
      fun () ->
        let fx = f "f" [ x ] and fxy = f "f" [ x; y ] and g ts = f "g" ts in
        equal
          (defined (Unfold.definition (eq fxy (g [ y; x ]))))
          (Some (Original "f", 2, false))
          "plain definition";
        equal
          (defined (Unfold.definition (eq (g [ x; y; x ]) fxy)))
          (Some (Original "f", 2, true))
          "defined term on the right";
        equal
          (defined (Unfold.definition (eq (g [ x ]) fx)))
          (Some (Original "g", 1, false))
          "left side first";
        equal (Unfold.definition (eq (f "f" [ x; x ]) (constant "c"))) None "repeated variable";
        equal
          (defined (Unfold.definition (eq (f "f" [ x; x ]) (g [ x ]))))
          (Some (Original "g", 1, true))
          "the other side can still be a definition";
        equal (Unfold.definition (eq fx (g [ y ]))) None "unbound right-hand variable";
        equal (Unfold.definition (eq fx (g [ fx ]))) None "recursive definition";
        equal (Unfold.definition (eq (constant "a") (constant "b"))) None "constant (arity 0)";
        equal
          (Unfold.definition (eq (f "f" [ constant "a" ]) (constant "b")))
          None "non-variable argument";
        equal
          (Unfold.definition [ negative (E (fx, g [ x ])) ])
          None "negative literal is not a definition";
        equal
          (Unfold.definition (positive (E (fx, g [ x ])) :: eq (g [ x ]) x))
          None "non-unit clause";
        equal (Unfold.standard_weight (f "f" [ x; constant "a" ])) 5 "E standard weight" );
    ( "the plan takes definitions in E's order, applies them in turn and honours the limit",
      fun () ->
        let k a = f "k" [ a ] and g a = f "g" [ a ] and h a b = f "h" [ a; b ] in
        let clauses =
          [
            eq (g x) (h (f "f" [ x ]) x);
            (* weight 9, second in E's order *)
            eq (f "f" [ x ]) (k x);
            (* weight 6, first *)
            [ negative (E (g (constant "a"), constant "b")) ];
          ]
        in
        match Unfold.plan ~limit:20 clauses with
        | None -> failwith "no plan"
        | Some plan ->
            equal (List.map fst plan.removed) [ 1; 0 ] "E's order (standard weight first)";
            check
              (not (clause_mentions "f" plan.clauses.(0)))
              "the later definition was not rewritten by the earlier one";
            check
              ((not (clause_mentions "g" plan.clauses.(2)))
              && not (clause_mentions "f" plan.clauses.(2)))
              "the goal still mentions a removed symbol";
            equal plan.rewritten 1 "rewritten clauses";
            equal plan.steps 2 "steps (one per occurrence: f in g's right side, g in the goal)";
            equal
              (Option.map (fun p -> List.length p.Unfold.removed) (Unfold.plan ~limit:2 clauses))
              (Some 1) "the limit keeps the heavier definition";
            equal (Unfold.plan ~limit:(-100) clauses) None "a negative limit unfolds nothing";
            equal
              (Unfold.plan ~limit:20 [ eq (constant "a") (constant "b") ])
              None "nothing to unfold" );
    ( "an unfolded refutation replays against the original input",
      fun () ->
        let theory = Tptp.parse (ring ()) in
        let fixed = Theory.fixed theory in
        List.iter
          (fun (s : Strategy.t) ->
            let e = run_engine (engine_config (unfolding s)) theory fixed in
            equal (List.length e.unfolded) 2 (s.name ^ ": both definitions removed");
            check (e.root <> None) (s.name ^ ": no refutation");
            let cert = Option.get (Engine.certificate e ~theory:(Theory.name theory)) in
            let definition_ids =
              List.filter_map
                (fun (a : axiom) -> if a.name = "assoc_def" then Some a.axiom_id else None)
                fixed
            in
            let inputs =
              List.filter_map
                (fun (st : step) ->
                  match st.rule with
                  | Input (a, _) when List.mem a definition_ids -> Some st.id
                  | _ -> None)
                cert.steps
            in
            check (inputs <> []) (s.name ^ ": proof does not use the definition's input clause");
            check
              (List.exists
                 (fun (st : step) ->
                   match st.rule with
                   | Paramodulate (p, _, _, _, _, _, _) -> List.mem p inputs
                   | _ -> false)
                 cert.steps)
              (s.name ^ ": no paramodulation from the definition");
            (* The search never saw a clause with a removed symbol. *)
            let hidden (st : step) =
              not (clause_mentions "associator" st.clause || clause_mentions "commutator" st.clause)
            in
            Tbl.Int.iter
              (fun id _ ->
                check (hidden (Proof.get e.proof id)) (s.name ^ ": a defined symbol reached Passive"))
              e.passive.live;
            check
              (List.for_all hidden (Index.all e.index))
              (s.name ^ ": a defined symbol reached Active"))
          [ Strategy.production; Strategy.of_name "e208"; Strategy.calc_e ] );
    ( "without a definition to remove the unfolding strategy runs the plain search",
      fun () ->
        let theory = Tptp.parse problem_without_definitions in
        let fixed = Theory.fixed theory in
        let stopped = !Engine.cost_clock in
        (Engine.cost_clock := fun () -> 0.);
        Fun.protect
          ~finally:(fun () -> Engine.cost_clock := stopped)
          (fun () ->
            List.iter
              (fun (s : Strategy.t) ->
                let limits =
                  {
                    Engine.seconds = 30.;
                    max_given = 60;
                    max_generated = 100000;
                    max_retained = 100000;
                  }
                in
                let plain = run_engine { (engine_config s) with limits } theory fixed in
                let unfolded =
                  run_engine { (engine_config (unfolding s)) with limits } theory fixed
                in
                equal unfolded.unfolded [] "a definition was found";
                equal
                  (unfolded.metrics.given, unfolded.metrics.generated, unfolded.metrics.retained)
                  (plain.metrics.given, plain.metrics.generated, plain.metrics.retained)
                  (s.name ^ ": search changed");
                equal (Proof.steps unfolded.proof) (Proof.steps plain.proof)
                  (s.name ^ ": proof changed"))
              [ Strategy.production; Strategy.of_name "e208" ]) );
    ( "axioms added after the initial ones are unfolded as well",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(def,axiom,double(X) = pair(X,X)). cnf(fact,axiom,pair(a,a) = b). \
             cnf(late,negated_conjecture,double(a) != b)."
        in
        match Theory.fixed theory with
        | [ def; fact; late ] ->
            let e = Engine.create (engine_config (unfolding Strategy.production)) in
            Engine.add_initial_axioms e [ def; fact ];
            equal (List.length e.unfolded) 1 "the definition was not removed";
            Engine.add_axiom e late;
            Engine.finish e;
            let cert = Option.get (Engine.certificate e ~theory:(Theory.name theory)) in
            (match Kernel.check theory cert with Ok _ -> () | Error error -> failwith error);
            check
              (List.exists
                 (fun (st : step) -> match st.rule with Paramodulate _ -> true | _ -> false)
                 cert.steps)
              "the late axiom was not rewritten"
        | _ -> failwith "fixture" );
    ( "the memory budget keeps unfolded input clauses as it keeps input clauses",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(def,axiom,double(X) = pair(X,X)). cnf(use,axiom,p(double(a))). \
             cnf(other,axiom,q(b) | r(double(b)))."
        in
        let e = Engine.create (engine_config (unfolding Strategy.production)) in
        Engine.add_initial_axioms e (Theory.fixed theory);
        let passive = Tbl.Int.fold (fun id _ ids -> id :: ids) e.passive.live [] in
        let rewritten =
          List.filter
            (fun id -> match (Proof.get e.proof id).rule with Paramodulate _ -> true | _ -> false)
            passive
        in
        equal (List.length rewritten) 2 "both rewritten clauses should be Passive";
        check
          (List.for_all (fun id -> Hashtbl.mem e.unfolded_inputs id) rewritten)
          "a rewritten input clause is not marked";
        check
          (List.for_all (fun (_, id) -> not (List.mem id rewritten)) (Engine.trimmable e))
          "the budget may discard an unfolded input clause" );
    ( "unfolding is on for the members that measured no loss",
      fun () ->
        let unfold name = (Strategy.of_name name).unfold in
        List.iter
          (fun name -> equal (unfold name) (Some Unfold.default_limit) (name ^ " should unfold"))
          [ "e208"; "sat001"; "y1346"; "x1276"; "calc:e"; "e208k"; "sat001k" ];
        (* y1346 unfolds on its E loop, and so does x1276 with E's loop details; the derived
           evaluation variants of y1346 keep the input. *)
        List.iter
          (fun name -> equal (unfold name) None (name ^ " should keep its input clauses"))
          [ "production"; "y1346k"; "y1346av"; "proto:e"; "proto:combo" ];
        let defaults workers =
          List.map
            (fun (c : Scheduler.config) -> c.engine.strategy.unfold)
            (Scheduler.worker_configs ~workers Scheduler.default_config)
        in
        equal (defaults 1) [ None ] "one default worker";
        equal (defaults 4) [ None; None; Some 20; Some 20 ] "four default workers" );
    ( "the internal override switches unfolding for every worker",
      fun () ->
        let over value =
          (Eval.of_env (function "AXIOM_EQ_UNFOLD" -> Some value | _ -> None)).config
            Scheduler.default_config
        in
        equal (over "off").unfold (Some None) "off";
        equal (over "on").unfold (Some (Some Unfold.default_limit)) "on";
        equal (over " 7 ").unfold (Some (Some 7)) "limit";
        check (rejects (fun () -> ignore (over "maybe"))) "bad value accepted";
        equal Scheduler.default_config.unfold None "default override";
        let strategies config workers =
          List.map
            (fun (c : Scheduler.config) -> (c.engine.strategy.name, c.engine.strategy.unfold))
            (Scheduler.worker_configs ~workers config)
        in
        equal
          (strategies (over "on") 4)
          [
            ("production", Some 20); ("production", Some 20); ("e208", Some 20); ("y1346", Some 20);
          ]
          "on did not reach every worker";
        check
          (List.for_all (fun (_, u) -> u = None) (strategies (over "off") 4))
          "off did not reach every worker" );
  ]

let () = run tests
