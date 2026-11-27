open Axiom_fuzzer
open Test_support
open Wire
module C = Source_checker

exception Stopped

let signature =
  Signature.make ~functions:[ ("a", 0); ("f", 1); ("g", 2) ] ~predicates:[ ("p", 2); ("q", 1) ]

let rec generated_term rng parameters depth size =
  if size = 0 then
    match Random.State.int rng 3 with
    | 0 when parameters -> F (Random.State.int rng 4)
    | 1 when depth > 0 -> B (Random.State.int rng depth)
    | _ -> App ("a", [])
  else
    match Random.State.int rng 3 with
    | 0 -> generated_term rng parameters depth 0
    | 1 -> App ("f", [ generated_term rng parameters depth (size - 1) ])
    | _ -> App ("g", List.init 2 (fun _ -> generated_term rng parameters depth (size - 1)))

let rec generated_formula rng parameters depth size =
  if size = 0 then
    match Random.State.int rng 5 with
    | 0 -> Top
    | 1 -> Bot
    | 2 -> Pred ("p", List.init 2 (fun _ -> generated_term rng parameters depth 1))
    | 3 -> Pred ("q", [ generated_term rng parameters depth 1 ])
    | _ -> Eq (generated_term rng parameters depth 1, generated_term rng parameters depth 1)
  else
    match Random.State.int rng 6 with
    | 0 -> generated_formula rng parameters depth 0
    | 1 -> Neg (generated_formula rng parameters depth (size - 1))
    | 2 ->
        Conj
          (List.init (Random.State.int rng 4) (fun _ ->
               generated_formula rng parameters depth (size - 1)))
    | 3 ->
        Disj
          (List.init (Random.State.int rng 4) (fun _ ->
               generated_formula rng parameters depth (size - 1)))
    | 4 -> All (generated_formula rng parameters (depth + 1) (size - 1))
    | _ -> Ex (generated_formula rng parameters (depth + 1) (size - 1))

let rec term_value model bound free = function
  | B i -> List.nth bound i
  | F i -> free i
  | App ("a", []) -> model land 1
  | App ("f", [ x ]) -> term_value model bound free x lxor (model land 1)
  | App ("g", [ x; y ]) -> term_value model bound free x lxor term_value model bound free y
  | _ -> failwith "unknown test function"

let rec holds model bound free = function
  | Top -> true
  | Bot -> false
  | Pred ("p", [ x; y ]) ->
      model land (1 lsl ((2 * term_value model bound free x) + term_value model bound free y)) <> 0
  | Pred ("q", [ x ]) -> term_value model bound free x = model land 1
  | Pred _ -> failwith "unknown test predicate"
  | Eq (x, y) -> term_value model bound free x = term_value model bound free y
  | Neg f -> not (holds model bound free f)
  | Conj fs -> List.for_all (holds model bound free) fs
  | Disj fs -> List.exists (holds model bound free) fs
  | All f -> List.for_all (fun x -> holds model (x :: bound) free f) [ 0; 1 ]
  | Ex f -> List.exists (fun x -> holds model (x :: bound) free f) [ 0; 1 ]

let rec raw_term = function
  | Wire_types.B i -> B i
  | Wire_types.F i -> F i
  | Wire_types.App (s, ts) -> App (s, List.map raw_term ts)

let rec raw_formula = function
  | Wire_types.Top -> Top
  | Wire_types.Bot -> Bot
  | Wire_types.Pred (s, ts) -> Pred (s, List.map raw_term ts)
  | Wire_types.Eq (x, y) -> Eq (raw_term x, raw_term y)
  | Wire_types.Neg f -> Neg (raw_formula f)
  | Wire_types.Conj fs -> Conj (List.map raw_formula fs)
  | Wire_types.Disj fs -> Disj (List.map raw_formula fs)
  | Wire_types.All f -> All (raw_formula f)
  | Wire_types.Ex f -> Ex (raw_formula f)

let rec raw_normal = function
  | C.NPred (positive, s, ts) ->
      let f = Pred (s, List.map raw_term ts) in
      if positive then f else Neg f
  | NEqual (positive, x, y) ->
      let f = Eq (raw_term x, raw_term y) in
      if positive then f else Neg f
  | NConj fs -> Conj (List.map raw_normal fs)
  | NDisj fs -> Disj (List.map raw_normal fs)
  | NAll f -> All (raw_normal f)
  | NEx f -> Ex (raw_normal f)

(* Unlike Wire.import, this test builder also accepts a surrounding scope. *)
let rec import_at arena depth = function
  | Top -> Source.truth arena
  | Bot -> Source.falsity arena
  | Pred (s, ts) -> Source.pred arena s (List.map (Wire.import_term arena) ts)
  | Eq (x, y) -> Source.eq arena (Wire.import_term arena x) (Wire.import_term arena y)
  | Neg f -> Source.not_ arena (import_at arena depth f)
  | Conj fs -> Source.and_ arena (List.map (import_at arena depth) fs)
  | Disj fs -> Source.or_ arena (List.map (import_at arena depth) fs)
  | All f -> Source.forall arena ~depth (import_at arena (depth + 1) f)
  | Ex f -> Source.exists arena ~depth (import_at arena (depth + 1) f)

let rec matrix_truth value = function
  | C.MLiteral l -> value l
  | MConj ms -> List.for_all (matrix_truth value) ms
  | MDisj ms -> List.exists (matrix_truth value) ms

let rec reference_cnf = function
  | C.MLiteral l -> [ [ l ] ]
  | MConj ms -> List.concat_map reference_cnf ms
  | MDisj ms ->
      List.fold_left
        (fun acc m -> List.concat_map (fun x -> List.map (fun y -> x @ y) (reference_cnf m)) acc)
        [ [] ] ms

let convert ?(limit = 100000) m = C.bounded_cnf (fun () -> true) limit m

let tests =
  [
    ( "Source substitution preserves open-term semantics and scope",
      fun () ->
        let rng = Random.State.make [| 193821 |] in
        let arena = Source.create signature in
        for trial = 0 to 249 do
          let depth = trial mod 3 in
          let raw = generated_formula rng true depth 3
          and replacement = generated_term rng true depth 2 in
          let v = trial mod 4 in
          let checked =
            C.substitute_formula 0 v
              (Wire.checked_source_term replacement)
              (Wire.checked_source raw)
          in
          check (C.formula_scoped depth false checked) "substitution lost scope";
          let actual =
            Source.subst_free arena v
              (Wire.import_term arena replacement)
              (import_at arena depth raw)
            |> Wire.export arena
          in
          for model = 0 to 15 do
            let bound = List.init depth (fun i -> (model lsr i) land 1)
            and free i = (model lsr i) land 1 in
            let value = term_value model bound free replacement in
            let expected = holds model bound (fun i -> if i = v then value else free i) raw in
            equal
              (holds model bound free (raw_formula checked))
              expected "extracted substitution changed meaning";
            equal (holds model bound free actual) expected
              "arena substitution bridge changed meaning"
          done
        done );
    ( "substitution lifts outer indices across nested binders",
      fun () ->
        let arena = Source.create signature in
        let raw = All (Ex (Pred ("p", [ F 0; B 1 ]))) in
        let actual =
          Source.subst_free arena 0
            (Source.apply arena "f" [ Source.bound arena 0 ])
            (import_at arena 1 raw)
          |> Wire.export arena
        in
        equal actual
          (All (Ex (Pred ("p", [ App ("f", [ B 2 ]); B 1 ]))))
          "replacement captured by an inner quantifier";
        check
          (Source.well_scoped arena ~depth:1 (import_at arena 1 actual))
          "outer scope not retained" );
    ( "substitution is simultaneous in its replacement and handles large free IDs",
      fun () ->
        let arena = Source.create signature in
        let raw = Pred ("p", [ F max_int; F 0 ]) in
        let replacement =
          Source.apply arena "g" [ Source.free arena max_int; Source.free arena 1 ]
        in
        let actual =
          Source.subst_free arena max_int replacement (Wire.import arena raw) |> Wire.export arena
        in
        equal actual
          (Pred ("p", [ App ("g", [ F max_int; F 1 ]); F 0 ]))
          "replacement was recursively substituted";
        equal
          (Source.subst_free arena 2 replacement (Wire.import arena raw))
          (Wire.import arena raw) "absent variable changed formula" );
    ( "substitution rejects negative IDs, foreign terms and lifted overflow",
      fun () ->
        let arena = Source.create signature and other = Source.create signature in
        let f = Wire.import arena (All (Pred ("q", [ F 0 ]))) in
        check
          (rejects (fun () -> ignore (Source.subst_free arena (-1) (Source.free arena 0) f)))
          "negative ID accepted";
        check
          (rejects (fun () -> ignore (Source.subst_free arena 0 (Source.free other 0) f)))
          "foreign term accepted";
        check
          (rejects (fun () -> ignore (Source.subst_free arena 0 (Source.bound arena max_int) f)))
          "lift overflow accepted" );
    ( "NNF preserves both polarities in finite models",
      fun () ->
        let rng = Random.State.make [| 362899 |] in
        for trial = 0 to 299 do
          let depth = trial mod 3 in
          let raw = generated_formula rng true depth 4 in
          List.iter
            (fun positive ->
              let result = C.nnf positive (Wire.checked_source raw) |> raw_normal in
              for model = 0 to 15 do
                let bound = List.init depth (fun i -> (model lsr i) land 1)
                and free i = (model lsr i) land 1 in
                equal (holds model bound free result)
                  (positive = holds model bound free raw)
                  "NNF changed formula semantics"
              done)
            [ true; false ]
        done );
    ( "NNF retains scope failures as well as valid scopes",
      fun () ->
        let cases =
          [
            Top;
            Bot;
            Conj [];
            Disj [];
            All (Pred ("q", [ B 0 ]));
            All (Pred ("q", [ B 1 ]));
            Neg (Ex (Eq (B max_int, F max_int)));
            Conj [ Bot; Pred ("q", [ B max_int ]) ];
            Disj [ Top; Pred ("q", [ F 0 ]) ];
          ]
        in
        List.iter
          (fun f ->
            let f = Wire.checked_source f in
            List.iter
              (fun positive ->
                List.iter
                  (fun depth ->
                    List.iter
                      (fun closed ->
                        equal
                          (C.normal_scoped depth closed (C.nnf positive f))
                          (C.formula_scoped depth closed f) "NNF erased scope errors")
                      [ false; true ])
                  [ 0; 1; 2 ])
              [ false; true ])
          cases );
    ( "NNF quantifier duality preserves Skolem dependencies and IDs",
      fun () ->
        let ax formula = { axiom_id = 7; name = "duality"; origin = Imported "duality"; formula } in
        let p = Pred ("p", [ B 1; B 0 ]) in
        equal
          (Kernel.input_clauses (ax (Neg (All (Ex p)))))
          [ [ negative (P ("p", [ Fn (Skolem (7, 0), []); v 0 ])) ] ]
          "negated universal lost constant witness";
        equal
          (Kernel.input_clauses (ax (Neg (Ex (All p)))))
          [ [ negative (P ("p", [ v 0; Fn (Skolem (7, 0), [ v 0 ]) ])) ] ]
          "negated existential lost universal dependency" );
    ( "bounded CNF preserves order, duplicates and finite-model semantics",
      fun () ->
        let rng = Random.State.make [| 489207 |] in
        let rec generated depth =
          if depth = 0 || Random.State.int rng 4 = 0 then C.MLiteral (Random.State.int rng 8)
          else
            let ms = List.init (Random.State.int rng 4) (fun _ -> generated (depth - 1)) in
            if Random.State.bool rng then C.MConj ms else MDisj ms
        in
        for _ = 1 to 200 do
          let matrix = generated 3 in
          let expected = reference_cnf matrix in
          equal (convert matrix) (Some expected) "full-budget CNF changed order or duplicates";
          List.iter
            (fun limit ->
              match convert ~limit matrix with
              | None -> ()
              | Some actual ->
                  equal actual expected "bounded CNF differs from distributive oracle";
                  check (List.length actual <= limit) "clause limit exceeded")
            [ 0; 1; 2; 5; 16; 256 ];
          for model = 0 to 15 do
            let value l = model land (1 lsl (l / 2)) <> 0 = (l mod 2 = 0) in
            equal
              (List.for_all (List.exists value) expected)
              (matrix_truth value matrix) "CNF changed matrix meaning"
          done
        done );
    ( "bounded CNF handles empty connectives and zero budget",
      fun () ->
        equal (convert ~limit:0 (C.MConj [])) (Some []) "truth needs no clauses";
        equal (convert ~limit:0 (C.MDisj [])) None "false escaped zero budget";
        equal (convert ~limit:1 (C.MDisj [])) (Some [ [] ]) "empty disjunction lost empty clause";
        equal (convert ~limit:0 (C.MLiteral 0)) None "atom escaped zero budget";
        equal
          (convert ~limit:0 (C.MDisj [ C.MConj [] ]))
          (Some []) "disjunction of truth not allowed at zero budget";
        equal
          (convert (C.MDisj [ C.MLiteral 0; C.MConj []; C.MLiteral 1 ]))
          (Some []) "truth did not annihilate product" );
    ( "CNF checks bounds before expansion without overflowing machine integers",
      fun () ->
        let rows = C.MConj (List.init 2000 (fun i -> C.MLiteral i)) in
        let allocated () =
          let s = Gc.quick_stat () in
          s.minor_words +. s.major_words -. s.promoted_words
        in
        let before = allocated () in
        equal (convert (C.MDisj [ rows; rows ])) None "four-million-clause expansion accepted";
        check
          (allocated () -. before < 1_000_000.)
          "CNF allocated cross product before rejecting it";
        equal (convert ~limit:2000 rows)
          (Some (List.init 2000 (fun i -> [ i ])))
          "exact clause budget rejected";
        equal (convert ~limit:1999 rows) None "conjunction escaped budget";
        let small =
          C.MDisj [ C.MConj [ C.MLiteral 0; C.MLiteral 1 ]; C.MConj [ C.MLiteral 2; C.MLiteral 3 ] ]
        in
        equal (convert ~limit:max_int small)
          (Some [ [ 0; 2 ]; [ 0; 3 ]; [ 1; 2 ]; [ 1; 3 ] ])
          "large budget overflowed";
        check (not (C.product_fits max_int 2 max_int)) "product bound overflowed" );
    ( "CNF cancellation cannot accept a partial result",
      fun () ->
        let matrix = C.MDisj [ C.MLiteral 0; C.MConj [ C.MLiteral 1; C.MLiteral 2 ]; C.MConj [] ] in
        let rec nodes = function
          | C.MLiteral _ -> 1
          | MConj ms | MDisj ms -> 1 + List.fold_left (fun n m -> n + nodes m) 0 ms
        in
        for budget = 0 to nodes matrix do
          let calls = ref 0 in
          let actual =
            C.bounded_cnf
              (fun () ->
                incr calls;
                !calls <= budget)
              100000 matrix
          in
          if budget < nodes matrix then equal actual None "cancelled traversal returned partial CNF"
          else equal actual (Some (reference_cnf matrix)) "full traversal was cancelled"
        done );
    ( "independent clausifiers agree after extracted preprocessing",
      fun () ->
        let rng = Random.State.make [| 82274 |] in
        for id = 0 to 299 do
          let formula = generated_formula rng false 0 3 in
          let ax = { axiom_id = id; name = "generated"; origin = Imported "generated"; formula } in
          List.iter
            (fun mode ->
              equal (Kernel.input_clauses ~mode ax) (Clausify.run ~mode ax)
                "CNF/Skolem order or numbering changed")
            [ Distributive; Definitional; Hybrid ]
        done );
    ( "kernel preprocessing propagates cooperative cancellation",
      fun () ->
        let ax =
          {
            axiom_id = 0;
            name = "cancel";
            origin = Imported "cancel";
            formula = All (Ex (Disj [ Pred ("p", [ B 1; B 0 ]); Neg (Pred ("q", [ B 0 ])) ]));
          }
        in
        let calls = ref 0 in
        ignore (Kernel.input_clauses ~guard:(fun () -> incr calls) ax);
        let count = !calls in
        check (count > 5) "guard absent from preprocessing";
        List.iter
          (fun stop ->
            calls := 0;
            let cancelled =
              try
                ignore
                  (Kernel.input_clauses
                     ~guard:(fun () ->
                       incr calls;
                       if !calls = stop then raise Stopped)
                     ax);
                false
              with Stopped -> true
            in
            check cancelled "preprocessing swallowed cancellation")
          [ 1; count / 2; count ] );
  ]

let () = run tests
