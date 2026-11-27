open Axiom_fuzzer
open Test_support
open Wire
module C = Source_checker

let apply s args = Fn (Original s, args)

let instantiate ?(visit = fun () -> true) env t =
  C.instantiate_bound visit apply env (Wire.checked_source_term t)

let functions model f args =
  match (f, args) with
  | "a", [] -> model land 1
  | "f", [ x ] -> x lxor (model land 1)
  | "g", [ x; y ] -> x lxor y
  | _ -> failwith "unexpected original function"

let rec evaluate model = function
  | V (_, i) -> (model lsr (i mod 4)) land 1
  | Fn (Original f, args) -> functions model f (List.map (evaluate model) args)
  | Fn (Skolem (_, id), args) ->
      List.fold_left ( lxor ) ((model lsr (id mod 4)) land 1) (List.map (evaluate model) args)

let rec source_value model env = function
  | B i -> List.nth env i
  | F _ -> failwith "free parameter in closed test term"
  | App (f, args) -> functions model f (List.map (source_value model env) args)

let rec generated rng depth size =
  if size = 0 then
    if depth > 0 && Random.State.bool rng then B (Random.State.int rng depth) else App ("a", [])
  else
    match Random.State.int rng 3 with
    | 0 -> generated rng depth 0
    | 1 -> App ("f", [ generated rng depth (size - 1) ])
    | _ -> App ("g", List.init 2 (fun _ -> generated rng depth (size - 1)))

let tests =
  [
    ( "Skolem environment substitution preserves nested-term semantics",
      fun () ->
        let rng = Random.State.make [| 67091 |] in
        for trial = 0 to 399 do
          let env =
            List.init (trial mod 6) (fun i ->
                if i mod 2 = 0 then v i else Fn (Skolem (42, i), [ v 0; Fn (Original "f", [ v 1 ]) ]))
          in
          let term = generated rng (List.length env) 4 in
          let result = Option.get (instantiate env term) in
          for model = 0 to 15 do
            equal (evaluate model result)
              (source_value model (List.map (evaluate model) env) term)
              "bound substitution changed term value"
          done;
          check
            (C.term_scoped (List.length env) true (Wire.checked_source_term term))
            "accepted term was not scoped"
        done );
    ( "Skolem environment substitution rejects free and missing binders",
      fun () ->
        let env = [ v 0; Fn (Skolem (9, 0), [ v 0 ]) ] in
        List.iter
          (fun t -> equal (instantiate env t) None "invalid source term accepted")
          [ F 0; F max_int; B 2; B max_int; App ("g", [ B 0; F 0 ]); App ("g", [ B max_int; B 1 ]) ];
        equal (instantiate env (B 1)) (Some (List.nth env 1)) "binder lookup changed";
        equal (instantiate [] (App ("a", []))) (Some (constant "a")) "closed constant rejected";
        check
          (rejects (fun () -> ignore (instantiate env (B (-1)))))
          "negative binder reached natural-number extraction" );
    ( "Skolem term substitution cancels without evaluating the suffix",
      fun () ->
        let term = App ("g", [ App ("f", [ B 0 ]); App ("g", [ B 1; App ("a", []) ]) ]) in
        let total = ref 0 in
        ignore
          (instantiate
             ~visit:(fun () ->
               incr total;
               true)
             [ v 0; v 1 ]
             term);
        for stop = 1 to !total do
          let calls = ref 0 in
          equal
            (instantiate
               ~visit:(fun () ->
                 incr calls;
                 !calls <> stop)
               [ v 0; v 1 ]
               term)
            None "partial term accepted";
          equal !calls stop "cancelled traversal continued into a sibling term"
        done );
    ( "Skolem witnesses preserve lexical universal dependencies across branches",
      fun () ->
        let ax =
          {
            axiom_id = 12;
            name = "witnesses";
            origin = Imported "witnesses";
            formula =
              Ex
                (Conj
                   [
                     All (Ex (Pred ("p", [ B 2; B 1; B 0 ])));
                     All (All (Ex (Pred ("q", [ B 3; B 2; B 1; B 0 ]))));
                   ]);
          }
        in
        List.iter
          (fun mode ->
            equal (Kernel.input_clauses ~mode ax) (Clausify.run ~mode ax)
              "binder substitution changed witness numbering or argument order")
          [ Distributive; Definitional; Hybrid ];
        equal
          (Kernel.input_clauses ~mode:Distributive ax)
          [
            [ positive (P ("p", [ Fn (Skolem (12, 0), []); v 0; Fn (Skolem (12, 1), [ v 0 ]) ])) ];
            [
              positive
                (P ("q", [ Fn (Skolem (12, 0), []); v 0; v 1; Fn (Skolem (12, 2), [ v 0; v 1 ]) ]));
            ];
          ]
          "existential witnesses gained unrelated universals or lost earlier dependencies" );
  ]

let () = run tests
