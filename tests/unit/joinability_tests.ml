open Axiom_fuzzer
open Test_support
open Wire

(* EQ-UNIT: instance rewriting of unorientable equations with extra right-side variables, KBO
   under a variable order, ground joinability and connectedness (Joinability), and end-to-end
   kernel-checked refutations of the ordered-rewriting worker with the tests on. *)

let fn name args = Fn (Original name, args)
let x = v 0
let y = v 1
let z = v 2
let a = constant "a"
let b = constant "b"
let step id clause = { id; rule = Input (id, 0); clause }
let unit_eq id l r = step id (Clause.normalize [ positive (E (l, r)) ])

(* A rule set with ordered rewriting on the standard order (unit weights, alphabetical). *)
let rules ?(instances = true) ?(constants = [ a; b ]) equations =
  let r = Demodulation.create ~ordered_rewriting:true ~instances () in
  Demodulation.set_minimal r constants;
  List.iteri (fun id (l, r') -> Demodulation.add r (unit_eq id l r')) equations;
  r

let random_term rng ~vars depth =
  let rec go d =
    if d = 0 || Random.State.int rng 3 = 0 then
      if vars > 0 && Random.State.int rng 3 > 0 then V (0, Random.State.int rng vars)
      else if Random.State.bool rng then a
      else b
    else
      match Random.State.int rng 3 with
      | 0 -> fn "f" [ go (d - 1); go (d - 1) ]
      | 1 -> fn "g" [ go (d - 1) ]
      | _ -> fn "h" [ go (d - 1) ]
  in
  go depth

let rec ground_term rng depth =
  if depth = 0 || Random.State.int rng 3 = 0 then if Random.State.bool rng then a else b
  else
    match Random.State.int rng 3 with
    | 0 -> fn "f" [ ground_term rng (depth - 1); ground_term rng (depth - 1) ]
    | 1 -> fn "g" [ ground_term rng (depth - 1) ]
    | _ -> fn "h" [ ground_term rng (depth - 1) ]

let rec substitute sigma = function
  | V v as t -> Option.value ~default:t (List.assoc_opt v sigma)
  | Fn (f, ts) -> Fn (f, List.map (substitute sigma) ts)

let tests =
  [
    ( "instance rewriting binds an extra right-side variable to the least constant, a checked step",
      fun () ->
        (* g(X) = f(Y): no direction is orientable (variables), g(X) -> f(a) decreases (equal
           weight, g above f), f(Y) -> g(a) does not. *)
        let off = rules ~instances:false [ (fn "g" [ x ], fn "f" [ y ]) ] in
        let on = rules [ (fn "g" [ x ], fn "f" [ y ]) ] in
        let target = step 5 [ positive (p [ fn "g" [ b ] ]) ] in
        check (Demodulation.rewrite_once off target = None) "rule used without instances";
        (match Demodulation.rewrite_once on target with
        | None -> failwith "instance rewrite missed"
        | Some (clause, rule) ->
            equal (Clause.normalize clause)
              (Clause.normalize [ positive (p [ fn "f" [ a ] ]) ])
              "the extra variable is not bound to the least constant a";
            equal
              (Kernel.derive ~inputs:[]
                 ~steps:[ unit_eq 0 (fn "g" [ x ]) (fn "f" [ y ]); target ]
                 rule)
              (Ok (Clause.normalize clause))
              "the kernel does not derive the instance rewrite";
            equal
              (Demodulation.rewrite_first on target)
              (Some (clause, rule))
              "rewrite_first and rewrite_once disagree");
        (* Without a constant no rule with an extra variable is indexed. *)
        let none = rules ~constants:[] [ (fn "g" [ x ], fn "f" [ y ]) ] in
        check (Demodulation.rewrite_once none target = None) "rule without a least constant";
        (* A direction whose right side lacks a left variable is an ordinary ordered rule:
           h(f(X,Y)) = g(g(g(g(X)))) is unorientable (weights 4 and 5, Y only on the left), and
           its instance h(f(b,g(g(a)))) -> g(g(g(g(b)))) decreases (weights 6 and 5). *)
        let g4 t = fn "g" [ fn "g" [ fn "g" [ fn "g" [ t ] ] ] ] in
        let equation = [ (fn "h" [ fn "f" [ x; y ] ], g4 x) ] in
        let target = step 6 [ positive (p [ fn "h" [ fn "f" [ b; fn "g" [ fn "g" [ a ] ] ] ] ]) ] in
        check
          (Demodulation.rewrite_once (rules ~instances:false equation) target = None)
          "a rule with different variable sets was used without instances";
        (match Demodulation.rewrite_once (rules equation) target with
        | None -> failwith "the left-extra direction was not used"
        | Some (clause, _) ->
            equal (Clause.normalize clause)
              (Clause.normalize [ positive (p [ g4 b ]) ])
              "wrong left-extra rewrite");
        equal
          (Demodulation.minimal_constant [ b; a ])
          (Some a) "least constant of the standard order" );
    ( "KBO under a variable order holds for every ground instance that respects the order",
      fun () ->
        let rng = Random.State.make [| 20261116 |] in
        let tables =
          (* The standard order and an installed one with nonuniform weights. *)
          let installed = Ordering.create () in
          Ordering.install installed ~weights:true
            [
              [ positive (E (fn "f" [ a; fn "g" [ b ] ], fn "h" [ fn "h" [ a ] ])) ];
              [ positive (E (fn "g" [ fn "g" [ a ] ], fn "g" [ b ])) ];
            ];
          [ Ordering.standard; installed ]
        in
        let proved = ref 0 and plain = ref 0 in
        List.iter
          (fun order ->
            let wmin = Joinability.least_weight order [ a; b ] in
            for _ = 1 to 3000 do
              let s = random_term rng ~vars:3 3 and t = random_term rng ~vars:3 3 in
              (* A random strict order of the three variables: a permutation. *)
              let perm = List.sort (fun _ _ -> Random.State.int rng 3 - 1) [ 0; 1; 2 ] in
              let rank (_, i) =
                let rec find k = function
                  | [] -> 0
                  | j :: rest -> if j = i then k else find (k + 1) rest
                in
                find 0 perm
              in
              let model = Joinability.greater_in order ~wmin rank s t in
              if Ordering.greater ~order s t then (
                incr plain;
                check model "the model order is weaker than the plain order");
              if model then (
                incr proved;
                for _ = 1 to 10 do
                  (* Three distinct ground terms, sorted, assigned in the model's order. *)
                  let rec distinct acc =
                    if List.length acc = 3 then acc
                    else
                      let g = ground_term rng 3 in
                      if List.mem g acc then distinct acc else distinct (g :: acc)
                  in
                  let sorted =
                    List.sort
                      (fun u w ->
                        if Ordering.greater ~order u w then 1
                        else if Ordering.greater ~order w u then -1
                        else compare u w)
                      (distinct [])
                  in
                  let sigma = List.mapi (fun k i -> ((0, i), List.nth sorted k)) perm in
                  check
                    (Ordering.greater ~order (substitute sigma s) (substitute sigma t))
                    "greater_in accepted a pair that a ground instance of its model refutes"
                done)
            done)
          tables;
        check (!proved > !plain && !plain > 0) "the property test compared too few pairs" );
    ( "ground joinability: AC permutations are joinable, other equations are not",
      fun () ->
        (* f is associative and commutative: assoc oriented, commutativity and the permutation
           f(X,f(Y,Z)) = f(Y,f(X,Z)) used by ordered rewriting. *)
        let ac =
          rules
            [
              (fn "f" [ fn "f" [ x; y ]; z ], fn "f" [ x; fn "f" [ y; z ] ]);
              (fn "f" [ x; y ], fn "f" [ y; x ]);
              (fn "f" [ x; fn "f" [ y; z ] ], fn "f" [ y; fn "f" [ x; z ] ]);
            ]
        in
        let order = Ordering.standard and stats = Joinability.stats () in
        let gj s t =
          Joinability.ground_joinable ~work:100000 ~steps:64 ~order ~wmin:1 stats ac s t
        in
        check
          (gj (fn "f" [ x; fn "f" [ y; z ] ]) (fn "f" [ z; fn "f" [ y; x ] ]))
          "an AC permutation is not ground joinable";
        check
          (gj (fn "g" [ fn "f" [ x; y ] ]) (fn "g" [ fn "f" [ y; x ] ]))
          "commutativity under g is not ground joinable";
        check (not (gj (fn "f" [ x; y ]) (fn "f" [ x; x ]))) "f(x,y) = f(x,x) was joined";
        check
          (not (gj (fn "f" [ x; fn "g" [ y ] ]) (fn "f" [ y; fn "g" [ x ] ])))
          "a non-AC equation was joined";
        check (stats.ground_joined = 2 && stats.ground_tests = 4) "counters" );
    ( "connectedness below the peak uses unorientable equations only under the peak",
      fun () ->
        let comm = rules [ (fn "f" [ x; y ], fn "f" [ y; x ]) ] in
        let order = Ordering.standard and stats = Joinability.stats () in
        let connected peak s t =
          Joinability.connected ~work:10000 ~steps:64 ~order ~wmin:1 stats comm ~peak s t
        in
        let fxy = fn "f" [ x; y ] and fyx = fn "f" [ y; x ] in
        check (not (Ordering.greater fxy fyx || Ordering.greater fyx fxy)) "fixture is orientable";
        check (connected (fn "h" [ fn "f" [ fxy; fyx ] ]) fyx fxy) "not connected below h(...)";
        (* The rewritten side must stay below the peak in every instance. *)
        check (not (connected fxy fyx fxy)) "connected through the peak itself" );
    ( "lean workers with EQ-UNIT find kernel-checked refutations (with and without ordered \
       rewriting)",
      fun () ->
        let problems =
          [
            ( "c5",
              "cnf(c1,axiom,(f(X,e) = X)). cnf(c2,axiom,(f(e,X) = X)). cnf(c3,axiom,(f(X,X) = e)).\n\
               cnf(c4,axiom,(f(f(X,Y),Z) = f(X,f(Y,Z)))).\n\
               cnf(c5,negated_conjecture,(f(a,b) != f(b,a)))." );
            (* Robbins-style: + is AC; an extra right-side variable in t(X) = t(Y). *)
            ( "g",
              "cnf(a1,axiom,(plus(X,Y) = plus(Y,X))). cnf(a2,axiom,(plus(plus(X,Y),Z) = \
               plus(X,plus(Y,Z)))).\n\
               cnf(a3,axiom,(plus(X,zero) = X)). cnf(a4,axiom,(plus(X,minus(X)) = zero)).\n\
               cnf(a5,axiom,(k(X,minus(X)) = k(Y,minus(Y)))).\n\
               cnf(g,negated_conjecture,(plus(plus(b,a),plus(minus(a),c)) != plus(c,b)))." );
          ]
        in
        List.iter
          (fun (goal, problem) ->
            let t = Tptp.parse problem in
            List.iter
              (fun (strategy, instances, ground, connected) ->
                let config =
                  {
                    Scheduler.default_config with
                    reference = false;
                    portfolio = Strategy.Workers [ Strategy.of_name strategy ];
                    engine =
                      {
                        Engine.default_config with
                        goal_names = [ goal ];
                        eq_instances = instances;
                        eq_ground_joinable = ground;
                        eq_connected = connected;
                        limits = { Engine.default_limits with seconds = 20. };
                      };
                  }
                in
                let r = Scheduler.portfolio ~workers:1 config (fun () -> Theory.copy t) in
                match r.certificate with
                | None -> failwith (goal ^ " " ^ strategy ^ ": no refutation: " ^ r.reason)
                | Some cert ->
                    check
                      (Result.is_ok (Kernel.check t cert))
                      (goal ^ " " ^ strategy ^ ": kernel rejected"))
              [
                ("e208", true, true, true);
                ("e208", true, false, false);
                ("e208", false, true, false);
                ("e208", false, false, true);
                (* No ordered rewriting: the tests read their own index of the active equations. *)
                ("sat001", false, true, true);
                ("y1346", false, true, true);
              ])
          problems;
        (* That index exists only where the tests need it. *)
        let engine strategy ground =
          Engine.create
            {
              Engine.default_config with
              strategy = Strategy.of_name strategy;
              eq_ground_joinable = ground;
            }
        in
        check ((engine "sat001" true).equations <> None) "sat001 has no test index";
        check ((engine "sat001" false).equations = None) "an unused test index";
        check ((engine "e208" true).equations = None) "e208 reads its own demodulator";
        check ((engine "production" true).equations = None) "production got a test index" );
  ]

let () = run tests
