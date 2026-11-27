open Axiom_fuzzer
open Test_support
open Wire

let boolean_proof left right =
  let step boolean_id boolean_clause boolean_rule = { boolean_id; boolean_clause; boolean_rule } in
  [
    step 0 [ 1; 2 ] (Split 0);
    step 1 [ -1 ] (Conflict left);
    step 2 [ 2 ] (Boolean_resolve (0, 0, 1));
    step 3 [ -2 ] (Conflict right);
    step 4 [] (Boolean_resolve (2, 1, 3));
  ]

let example ?(shared = false) ?(spare = false) () =
  let pred p x = Pred (p, [ x ]) in
  let choice =
    if shared then All (Disj [ pred "p" (B 0); pred "q" (B 0) ])
    else Disj [ All (pred "p" (B 0)); All (pred "q" (B 0)) ]
  in
  let signature =
    Signature.make ~functions:[ ("a", 0); ("b", 0) ] ~predicates:[ ("p", 1); ("q", 1); ("r", 0) ]
  in
  let theory =
    Theory.custom ~name:"avatar-proof-test" signature
      ([
         ("choice", choice);
         ("not-p", Neg (pred "p" (App ("a", []))));
         ("not-q", Neg (pred "q" (App ("b", []))));
       ]
      @ if spare then [ ("unused", Pred ("r", [])) ] else [])
  in
  let axioms = Theory.fixed theory in
  let inputs =
    List.map (fun (a : axiom) -> (a.axiom_id, Kernel.input_clauses ~mode:Distributive a)) axioms
  in
  let input id =
    { id; clause = Kernel.normalize (List.hd (List.assoc id inputs)); rule = Input (id, 0) }
  in
  let first = input 0 in
  let components = List.map (fun l -> [ l ]) first.clause in
  equal (List.length components) 2 "fixture did not split into two literals";
  let c3 = { id = 3; clause = Kernel.normalize (List.nth components 0); rule = Component 0 }
  and c4 = { id = 4; clause = Kernel.normalize (List.nth components 1); rule = Component 1 } in
  let steps = ref [ first; input 1; input 2; c3; c4 ] in
  let derive id rule =
    let clause =
      match Kernel.derive ~inputs ~steps:!steps rule with Ok c -> c | Error e -> failwith e
    in
    let s = { id; clause; rule } in
    steps := !steps @ [ s ];
    s
  in
  ignore (derive 5 (Resolve (3, 0, 1, 0, [ ((1, 0), constant "a") ])));
  ignore (derive 6 (Resolve (4, 0, 2, 0, [ ((1, 0), constant "b") ])));
  let components, splits, boolean_steps =
    if spare then (
      let unused = { (input 3) with id = 7 } in
      steps := !steps @ [ unused ];
      ( components @ [ unused.clause ],
        [ (0, [ 0; 1 ]); (7, [ 2 ]) ],
        boolean_proof 5 6 @ [ { boolean_id = 5; boolean_clause = [ 3 ]; boolean_rule = Split 1 } ]
      ))
    else (components, [ (0, [ 0; 1 ]) ], boolean_proof 5 6)
  in
  ( theory,
    {
      natural = None;
      avatar = Some { components; splits; boolean_steps; boolean_root = 4 };
      cnf_mode = Distributive;
      theory = Theory.name theory;
      axioms;
      steps = !steps;
      root = 0;
    } )

let accepts t c = match Kernel.check t c with Ok _ -> () | Error e -> failwith e

let rejects_certificate t c =
  check (Result.is_error (Kernel.check t c)) "invalid AVATAR proof accepted"

let change c f = { c with avatar = Option.map f c.avatar }

let contains text needle =
  let n = String.length needle in
  List.exists
    (fun i -> String.sub text i n = needle)
    (List.init (max 0 (String.length text - n + 1)) Fun.id)

let extracted shared =
  let module R = Rocq_checker in
  let module A = Avatar_checker in
  let p x = (true, R.Pred (0, [ x ])) and q x = (true, R.Pred (1, [ x ])) in
  let neg (s, a) = (not s, a) in
  let x = R.Var 0 and y = R.Var (if shared then 0 else 1) in
  let a = R.Fun (0, []) and b = R.Fun (1, []) in
  let inputs = [ [ p x; q y ]; [ neg (p a) ]; [ neg (q b) ] ] in
  let fo_steps =
    [
      (A.Ordinary (R.Input 0), List.nth inputs 0);
      (A.Component 0, [ p x ]);
      (A.Ordinary (R.Instance (1, [ (0, a) ])), [ p a ]);
      (A.Ordinary (R.Input 1), [ neg (p a) ]);
      (A.Ordinary (R.Resolve (2, 0, 3, 0)), []);
      (A.Component 1, [ q y ]);
      (A.Ordinary (R.Instance (5, [ ((if shared then 0 else 1), b) ])), [ q b ]);
      (A.Ordinary (R.Input 2), [ neg (q b) ]);
      (A.Ordinary (R.Resolve (6, 0, 7, 0)), []);
    ]
  in
  let boolean_steps =
    [
      (A.Split 0, [ (true, 0); (true, 1) ]);
      (A.Conflict 4, [ (false, 0) ]);
      (A.Boolean_resolve (0, 0, 1), [ (true, 1) ]);
      (A.Conflict 8, [ (false, 1) ]);
      (A.Boolean_resolve (2, 1, 3), []);
    ]
  in
  let proof : A.certificate =
    {
      components = [ [ p x ]; [ q y ] ];
      fo_steps;
      splits = [ (0, [ 0; 1 ]) ];
      boolean_steps;
      boolean_root = 4;
    }
  in
  (inputs, proof)

let tests =
  [
    ( "AVATAR non-ground Source refutation and portable roundtrip",
      fun () ->
        let t, c = example () in
        accepts t c;
        let decoded = Certificate_io.decode (Certificate_io.encode c) in
        equal decoded c "AVATAR serialization lost evidence";
        accepts t decoded );
    ( "AVATAR Engine certificates elaborate through the independent Source checker",
      fun () ->
        let t, _ = example () in
        let engine =
          Engine.create
            { config.engine with avatar = true; collect_every = 1; collect_adaptive = false }
        in
        List.iter (Engine.add_axiom engine) (Theory.fixed t);
        let avatar = engine.avatar in
        List.iter
          (fun (step : step) ->
            if List.length step.clause > 1 then (
              Avatar.offer_split avatar ~guard:(fun () -> ()) step;
              Engine.protect (fun () -> Engine.split_step engine avatar);
              Engine.deactivate engine step.id))
          (Proof.steps engine.proof);
        Engine.finish engine;
        let c =
          match Engine.certificate engine ~theory:(Theory.name t) with
          | Some c -> c
          | None -> failwith (Engine.reason engine)
        in
        check (Option.is_some c.avatar) "engine did not return a Boolean refutation";
        accepts t c;
        accepts t (Proof.prune c);
        accepts t (Certificate_io.decode (Certificate_io.encode c)) );
    ( "AVATAR rejects locally inconsistent branches as global refutations",
      fun () ->
        let t, c = example () in
        rejects_certificate t (change c (fun a -> { a with boolean_root = 1 }));
        rejects_certificate t
          (change c (fun a ->
               {
                 a with
                 boolean_steps =
                   [ { boolean_id = 0; boolean_clause = []; boolean_rule = Conflict 5 } ];
                 boolean_root = 0;
               }));
        rejects_certificate t { c with avatar = None; root = 5 } );
    ( "AVATAR rejects shared variables and invalid component coverage",
      fun () ->
        let t, c = example ~shared:true () in
        rejects_certificate t c;
        let t, c = example () in
        rejects_certificate t (change c (fun a -> { a with splits = [ (0, [ 0 ]) ] })) );
    ( "AVATAR extracted checker independently enforces dependencies and splitting",
      fun () ->
        let inputs, proof = extracted false in
        check (Avatar_checker.check inputs proof) "extracted checker rejected valid split";
        let inputs, bad = extracted true in
        check
          (not (Avatar_checker.check inputs bad))
          "extracted checker accepted shared-variable split";
        let inputs, proof = extracted false in
        let bad =
          {
            proof with
            Avatar_checker.boolean_steps = [ (Avatar_checker.Conflict 4, []) ];
            boolean_root = 0;
          }
        in
        check (not (Avatar_checker.check inputs bad)) "extracted checker erased branch dependency"
    );
    ( "AVATAR rejects forged Boolean inferences and mixed formats",
      fun () ->
        let t, c = example () in
        let mutate f =
          rejects_certificate t
            (change c (fun a ->
                 {
                   a with
                   boolean_steps =
                     List.map (fun s -> if s.boolean_id = 4 then f s else s) a.boolean_steps;
                 }))
        in
        mutate (fun s -> { s with boolean_rule = Boolean_resolve (2, 0, 3) });
        mutate (fun s -> { s with boolean_rule = Boolean_resolve (4, 1, 3) });
        mutate (fun s -> { s with boolean_clause = [ 0 ] });
        rejects_certificate t { c with root = 5 };
        rejects_certificate t { c with natural = Some (Wire_types.Number 0) } );
    ( "AVATAR proof pruning retains all SAT leaf ancestors and removes unused components",
      fun () ->
        let t, c = example ~spare:true () in
        accepts t c;
        let pruned = Proof.prune c in
        accepts t pruned;
        let a = Option.get pruned.avatar in
        equal (List.length pruned.axioms) 3 "unused axiom survived";
        equal
          ( List.length pruned.steps,
            List.length a.components,
            List.length a.splits,
            List.length a.boolean_steps )
          (7, 2, 1, 5) "incorrect AVATAR proof slice";
        accepts t (Certificate_io.decode (Certificate_io.encode pruned)) );
    ( "AVATAR exports conditional FO clauses and the checked SAT root",
      fun () ->
        let t, c = example () in
        accepts t c;
        let output = Tptp.tstp c in
        check (contains output "component_0,definition") "component definition absent";
        check
          (contains output "cnf(c5,plain,(~avatar_b_0)")
          "conditional empty clause exported unconditionally";
        check (contains output "cnf(b4,plain,($false)") "SAT refutation absent";
        check (Result.is_ok (Kernel.rocq_document t c)) "Rocq artifact generation failed" );
    ( "AVATAR exported labels cannot collide with Source predicate names",
      fun () ->
        let t, c = example () in
        let signature =
          Signature.make
            ~functions:[ ("a", 0); ("b", 0) ]
            ~predicates:[ ("p", 1); ("q", 1); ("r", 0); ("avatar_b_0", 0) ]
        in
        let theory =
          Theory.custom ~name:(Theory.name t) signature
            (List.map (fun (a : axiom) -> (a.name, a.formula)) (Theory.fixed t)
            @ [ ("collision", Pred ("avatar_b_0", [])) ])
        in
        let c = { c with axioms = Theory.fixed theory } in
        accepts theory c;
        let output = Tptp.tstp c in
        check (contains output "'srcp_avatar_b_0'") "Source predicate lost its namespace";
        check (contains output "avatar_b_0 <=>") "component label missing" );
  ]

let () =
  match Array.to_list Sys.argv with
  | [ _; "--export-rocq"; path ] -> (
      let t, c = example () in
      match Kernel.rocq_document t c with
      | Ok text -> Sexp.write_file path text
      | Error e -> failwith e)
  | _ -> run tests
