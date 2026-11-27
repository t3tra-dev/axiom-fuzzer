open Axiom_fuzzer
open Test_support
open Wire
module C = Source_checker

(* Independent two-element semantics. Original symbols stay fixed while every
   possible interpretation of the fresh functions (and CNF predicates) is tried.
   A model is chosen OUTSIDE the enumeration of variable assignments. *)
let code xs = List.fold_left (fun n x -> (2 * n) + x) 0 xs

let original model name args =
  match (name, args) with
  | "a", [] -> model land 1
  | "f", [ x ] -> 1 - x
  | "g", [ x; y ] -> x lxor y
  | _ -> failwith "unexpected original function"

let predicate model name args =
  match (name, args) with
  | "r", [ x; y ] -> model land (1 lsl code [ x; y ]) <> 0
  | "p", [ x ] -> model land (1 lsl code [ x; x ]) <> 0
  | _ -> failwith "unexpected original predicate"

let source_holds model raw =
  let rec term env = function
    | B i -> List.nth env i
    | F _ -> failwith "free parameter in model test"
    | App (s, ts) -> original model s (List.map (term env) ts)
  in
  let rec holds env = function
    | Top -> true
    | Bot -> false
    | Pred (p, ts) -> predicate model p (List.map (term env) ts)
    | Eq (s, t) -> term env s = term env t
    | Neg f -> not (holds env f)
    | Conj fs -> List.for_all (holds env) fs
    | Disj fs -> List.exists (holds env) fs
    | All f -> List.for_all (fun x -> holds (x :: env) f) [ 0; 1 ]
    | Ex f -> List.exists (fun x -> holds (x :: env) f) [ 0; 1 ]
  in
  holds [] raw

type fresh = Sk of int * int | Aux of int * int

let terms = function P (_, ts) | D (_, ts) -> ts | E (x, y) -> [ x; y ]

let variables atoms =
  let rec term = function V v -> [ v ] | Fn (_, ts) -> List.concat_map term ts in
  List.concat_map (fun a -> List.concat_map term (terms a)) atoms |> List.sort_uniq compare

let support (_, a) =
  List.map
    (fun (scope, i) ->
      check (scope = 0) "unexpected variable scope";
      i)
    (variables [ a ])

let slots atoms =
  let entries = ref [] in
  let add key arity =
    match List.assoc_opt key !entries with
    | None -> entries := (key, arity) :: !entries
    | Some n -> equal n arity "inconsistent fresh symbol arity"
  in
  let rec term = function
    | V _ -> ()
    | Fn (s, ts) ->
        (match s with Original _ -> () | Skolem (ax, id) -> add (Sk (ax, id)) (List.length ts));
        List.iter term ts
  in
  List.iter
    (fun a ->
      (match a with D ((ax, id), ts) -> add (Aux (ax, id)) (List.length ts) | _ -> ());
      List.iter term (terms a))
    atoms;
  let size = ref 0 in
  let table =
    List.sort compare !entries
    |> List.map (fun (key, arity) ->
        check (arity <= 8) "test interpretation too large";
        let offset = !size in
        size := !size + (1 lsl arity);
        (key, (arity, offset)))
  in
  (table, !size)

let interpretation table bits key args =
  let arity, offset = List.assoc key table in
  equal arity (List.length args) "semantic function arity mismatch";
  (bits lsr (offset + code args)) land 1

let atom_holds model fresh rho a =
  let rec term = function
    | V v -> rho v
    | Fn (Original s, ts) -> original model s (List.map term ts)
    | Fn (Skolem (ax, id), ts) -> fresh (Sk (ax, id)) (List.map term ts)
  in
  match a with
  | P (p, ts) -> predicate model p (List.map term ts)
  | E (x, y) -> term x = term y
  | D ((ax, id), ts) -> fresh (Aux (ax, id)) (List.map term ts) = 1

let literal model fresh rho (positive, atom) =
  positive = atom_holds model fresh (fun (_, v) -> rho v) atom

let update rho v x i = if i = v then x else rho i

let rec universal_holds model fresh rho = function
  | C.ULiteral l -> literal model fresh rho l
  | UConj fs -> List.for_all (universal_holds model fresh rho) fs
  | UDisj fs -> List.exists (universal_holds model fresh rho) fs
  | UAll (v, f) -> List.for_all (fun x -> universal_holds model fresh (update rho v x) f) [ 0; 1 ]

let rec matrix_holds model fresh rho = function
  | C.MLiteral l -> literal model fresh rho l
  | MConj fs -> List.for_all (matrix_holds model fresh rho) fs
  | MDisj fs -> List.exists (matrix_holds model fresh rho) fs

let rec atoms = function
  | C.ULiteral (_, a) -> [ a ]
  | UConj fs | UDisj fs -> List.concat_map atoms fs
  | UAll (_, f) -> atoms f

let all_assignments n predicate =
  let rec go bits = bits = 1 lsl n || (predicate (fun i -> (bits lsr i) land 1) && go (bits + 1)) in
  go 0

let exists_model size predicate =
  check (size <= 12) "test interpretation budget exceeded";
  let rec go bits = bits < 1 lsl size && (predicate bits || go (bits + 1)) in
  go 0

let traverse ?(env = []) ?(us = []) ?(next_v = 0) ?(next_s = 0) normal =
  Option.get
    (C.eliminate_quantifiers
       (fun () -> true)
       (fun s ts -> Fn (Original s, ts))
       (fun i -> V (0, i))
       (fun id ts -> Fn (Skolem (7, id), ts))
       (fun b p ts -> (b, P (p, ts)))
       (fun b x y -> (b, E (x, y)))
       max_int env us next_v next_s normal)

let compile raw =
  let result = traverse (C.nnf true (Wire.checked_source raw)) in
  let matrix = Option.get (C.checked_universals support max_int result.supplied_value) in
  let table, size = slots (atoms result.supplied_value) in
  (result, matrix, table, size)

let check_compilation raw (result, matrix, table, size) model =
  check (size <= 8 && result.C.next_variable <= 4) "quantifier test budget exceeded";
  let expected = source_holds model raw and satisfiable = ref false in
  for bits = 0 to (1 lsl size) - 1 do
    let fresh = interpretation table bits in
    let q = universal_holds model fresh (fun _ -> 0) result.supplied_value in
    equal q
      (universal_holds model fresh (fun _ -> 1) result.supplied_value)
      "closed formula depends on initial assignment";
    equal q
      (all_assignments result.next_variable (fun rho -> matrix_holds model fresh rho matrix))
      "universal erasure changed this Skolem model";
    check ((not q) || expected) "arbitrary Skolem model projects to a false source formula";
    satisfiable := !satisfiable || q
  done;
  equal !satisfiable expected "no common Skolem model preserves source truth"

let check_formula raw =
  let compiled = compile raw in
  for model = 0 to 15 do
    check_compilation raw compiled model
  done

let r x y = Pred ("r", [ x; y ])
let p x = Pred ("p", [ x ])
let f x = App ("f", [ x ])
let a = App ("a", [])

let clauses_model model fresh clauses =
  List.for_all
    (fun c ->
      let vars = variables (List.map (fun l -> l.atom) c) in
      all_assignments (List.length vars) (fun values ->
          let env = List.mapi (fun i var -> (var, values i)) vars in
          List.exists
            (fun l -> l.positive = atom_holds model fresh (fun v -> List.assoc v env) l.atom)
            c))
    clauses

let compile_axiom mode id formula =
  Kernel.input_clauses ~mode
    { axiom_id = id; name = "source-group"; origin = Imported "source-group"; formula }

let check_theory modes inputs =
  let clauses =
    List.mapi
      (fun i (id, formula) -> compile_axiom (List.nth modes (i mod List.length modes)) id formula)
      inputs
    |> List.concat
  in
  let table, size = slots (List.concat_map (List.map (fun l -> l.atom)) clauses) in
  for model = 0 to 15 do
    let actual =
      exists_model size (fun bits -> clauses_model model (interpretation table bits) clauses)
    in
    equal actual
      (List.for_all (fun (_, formula) -> source_holds model formula) inputs)
      "finite Source theory lost its common function/predicate model"
  done

let tests =
  [
    ( "Skolem interpretation is uniform across all universal assignments",
      fun () ->
        let valid = All (Ex (Eq (B 0, B 1))) and invalid = Ex (All (Eq (B 0, B 1))) in
        check
          (source_holds 0 valid && not (source_holds 0 invalid))
          "quantifier-order witness is ineffective";
        check_formula valid;
        check_formula invalid;
        let result, matrix, table, size = compile invalid in
        check
          (all_assignments result.next_variable (fun rho ->
               exists_model size (fun bits -> matrix_holds 0 (interpretation table bits) rho matrix)))
          "pointwise model selection should incorrectly accept this example";
        check
          (not
             (exists_model size (fun bits ->
                  all_assignments result.next_variable (fun rho ->
                      matrix_holds 0 (interpretation table bits) rho matrix))))
          "model was chosen inside the universal assignment" );
    ( "global model extension preserves earlier witnesses for every valuation",
      fun () ->
        let normal =
          C.NEx
            (NConj
               [
                 NEqual (true, Wire_types.B 0, Wire_types.App ("f", [ Wire_types.B 1 ]));
                 NPred (true, "r", [ Wire_types.B 1; Wire_types.B 0 ]);
               ])
        in
        let result =
          traverse ~env:[ Fn (Skolem (7, 0), [ v 0 ]) ] ~us:[ v 0 ] ~next_v:1 ~next_s:1 normal
        in
        equal (result.next_variable, result.next_symbol) (1, 2) "existing symbol supply was lost";
        for model = 0 to 15 do
          for old = 0 to 3 do
            let old_value x = (old lsr x) land 1 in
            let original rho =
              let y = old_value (rho 0) in
              List.exists (fun x -> x = 1 - y && predicate model "r" [ y; x ]) [ 0; 1 ]
            in
            let exact = ref false in
            for choice = 0 to 3 do
              let fresh key args =
                match (key, args) with
                | Sk (7, 0), [ x ] -> old_value x
                | Sk (7, 1), [ x ] -> (choice lsr x) land 1
                | _ -> failwith "unexpected witness dependency"
              in
              let target rho = universal_holds model fresh rho result.supplied_value in
              check
                (all_assignments 1 (fun rho -> (not (target rho)) || original rho))
                "projection required a specially chosen witness";
              exact := !exact || all_assignments 1 (fun rho -> target rho = original rho)
            done;
            check !exact "one extension could not preserve the old model pointwise"
          done
        done );
    ( "nested and sibling witnesses share a model without sharing fresh symbols",
      fun () ->
        List.iter check_formula
          [
            Ex (Ex (Conj [ p (B 1); Neg (p (B 0)) ]));
            All (Conj [ Ex (r (B 1) (B 0)); Ex (Neg (r (B 1) (B 0))) ]);
            Ex (All (Ex (Conj [ Eq (B 0, f (B 2)); r (B 1) (B 0) ])));
            Ex (Conj [ Eq (B 0, a); All (Ex (Eq (App ("g", [ B 0; B 1 ]), B 2))) ]);
            Conj [ All (Ex (r (B 1) (B 0))); All (Ex (Neg (r (B 1) (B 0)))) ];
            Neg (All (Ex (Conj [ r (B 1) (B 0); Neg (Eq (B 0, B 1)) ])));
          ] );
    ( "false branches and unused quantifiers have total model extensions",
      fun () ->
        List.iter check_formula
          [
            Ex Top;
            Ex Bot;
            All (Ex Top);
            All (Ex Bot);
            Conj [];
            Disj [];
            Disj [ Ex Bot; Ex (Eq (B 0, a)) ];
            Conj [ Ex Top; All Bot ];
            All (Disj [ Ex (Conj [ r (B 1) (B 0); Bot ]); Ex (Neg (r (B 1) (B 0))) ]);
            Ex (All (Disj [ Ex (r (B 2) (B 0)); Neg (r (B 1) (B 0)) ]));
          ] );
    ( "generated Source formulas preserve finite-model satisfiability through Skolemization",
      fun () ->
        let rng = Random.State.make [| 916420 |] in
        let rec term depth size =
          if size = 0 then
            if depth > 0 && Random.State.bool rng then B (Random.State.int rng depth) else a
          else
            match Random.State.int rng 3 with
            | 0 -> term depth 0
            | 1 -> f (term depth (size - 1))
            | _ -> App ("g", [ term depth (size - 1); term depth (size - 1) ])
        in
        let rec formula depth size =
          if size = 0 then
            match Random.State.int rng 5 with
            | 0 -> Top
            | 1 -> Bot
            | 2 -> p (term depth 1)
            | 3 -> r (term depth 1) (term depth 1)
            | _ -> Eq (term depth 1, term depth 1)
          else
            match Random.State.int rng 6 with
            | 0 -> Neg (formula depth (size - 1))
            | 1 -> All (formula (depth + 1) (size - 1))
            | 2 -> Ex (formula (depth + 1) (size - 1))
            | 3 -> Conj [ formula depth (size - 1); formula depth (size - 1) ]
            | 4 -> Disj [ formula depth (size - 1); formula depth (size - 1) ]
            | _ -> formula depth 0
        in
        let checked = ref 0 and attempts = ref 0 and truths = ref 0 and falsities = ref 0 in
        while !checked < 120 && !attempts < 5000 do
          incr attempts;
          let raw = formula 0 4 in
          let ((result, _, _, size) as compiled) = compile raw in
          if size <= 8 && result.next_variable <= 4 then begin
            for model = 0 to 15 do
              check_compilation raw compiled model;
              if source_holds model raw then incr truths else incr falsities
            done;
            incr checked
          end
        done;
        equal !checked 120 "generated corpus did not reach its target";
        check (!truths > 0 && !falsities > 0) "generated corpus missed a truth value" );
    ( "all kernel CNF modes admit one common model for functions and auxiliary predicates",
      fun () ->
        List.iter
          (fun raw ->
            List.iter
              (fun mode ->
                let clauses =
                  Kernel.input_clauses ~mode
                    { axiom_id = 7; name = "model"; origin = Imported "model"; formula = raw }
                in
                let table, size = slots (List.concat_map (List.map (fun l -> l.atom)) clauses) in
                let prepared =
                  List.map (fun c -> (c, variables (List.map (fun l -> l.atom) c))) clauses
                in
                for model = 0 to 15 do
                  let satisfiable =
                    exists_model size (fun bits ->
                        let fresh = interpretation table bits in
                        List.for_all
                          (fun (c, vars) ->
                            all_assignments (List.length vars) (fun values ->
                                let env = List.mapi (fun i var -> (var, values i)) vars in
                                List.exists
                                  (fun l ->
                                    l.positive
                                    = atom_holds model fresh (fun v -> List.assoc v env) l.atom)
                                  c))
                          prepared)
                  in
                  equal satisfiable (source_holds model raw)
                    "CNF chose a different model for each clause or valuation"
                done)
              [ Distributive; Definitional; Hybrid ])
          [
            All (Ex (Eq (B 0, B 1)));
            Ex (All (Eq (B 0, B 1)));
            All (Conj [ Ex (r (B 1) (B 0)); Ex (Neg (r (B 1) (B 0))) ]);
            Ex (Conj [ Eq (B 0, a); All (Ex (Eq (B 0, f (B 2)))) ]);
            Disj [ Ex Bot; All (Ex (r (B 1) (B 0))) ];
            Conj [ Ex (p (B 0)); Ex (Neg (p (B 0))) ];
            Ex Top;
            All Bot;
          ] );
    ( "local valuations need the scope-zero condition before lifting to all Wire scopes",
      fun () ->
        let clause = [ positive (P ("p", [ V (0, 0) ])); negative (P ("p", [ V (1, 0) ])) ] in
        let unused _ _ = failwith "unexpected fresh symbol" in
        check
          (all_assignments 1 (fun rho ->
               List.exists
                 (fun l -> l.positive = atom_holds 8 unused (fun (_, i) -> rho i) l.atom)
                 clause))
          "scope-collapsing witness should be a tautology";
        check
          (not (clauses_model 8 unused [ clause ]))
          "full scoped semantics incorrectly identified two variables";
        List.iter
          (fun mode ->
            List.iter
              (fun formula ->
                let clauses = compile_axiom mode 7 formula in
                List.iter
                  (fun c ->
                    List.iter
                      (fun (scope, _) ->
                        equal scope 0 "Source CNF retained a foreign variable scope")
                      (variables (List.map (fun l -> l.atom) c)))
                  clauses)
              [
                All (Ex (r (B 1) (B 0)));
                Ex (All (Eq (B 0, B 1)));
                All (Conj (List.init 40 (fun _ -> r (B 0) (B 0))));
                Ex Top;
                All Bot;
              ])
          [ Distributive; Definitional; Hybrid ] );
    ( "mixed CNF modes preserve one model for a finite Source axiom collection",
      fun () ->
        let theories =
          [
            [];
            [ Ex (p (B 0)); Ex (Neg (p (B 0))) ];
            [ All (p (B 0)); Ex (Conj [ Neg (p (B 0)); Eq (B 0, B 0) ]) ];
            [ All (Ex (r (B 1) (B 0))); Ex (All (Neg (r (B 0) (B 1)))) ];
            [ Ex (Conj [ Eq (B 0, a); p (f (B 0)) ]); All (Disj [ Neg (p (B 0)); Eq (B 0, f a) ]) ];
            [ Top; All (Ex (Eq (B 0, B 1))); Ex (Conj [ p (B 0); Eq (B 0, B 0) ]) ];
          ]
        in
        List.iter
          (fun formulas ->
            let inputs = List.mapi (fun i formula -> (7 * (i + 1), formula)) formulas in
            List.iter
              (fun modes -> check_theory modes inputs)
              [
                [ Distributive; Definitional; Hybrid ];
                [ Definitional; Hybrid; Distributive ];
                [ Hybrid; Distributive; Definitional ];
              ])
          theories );
    ( "duplicate axiom IDs can destroy a common Skolem model and are rejected",
      fun () ->
        let first = Ex (p (B 0)) and second = Ex (Neg (p (B 0))) in
        check
          (source_holds 1 first && source_holds 1 second)
          "distinct-witness Source theory should be satisfiable";
        let clauses = compile_axiom Distributive 7 first @ compile_axiom Distributive 7 second in
        let table, size = slots (List.concat_map (List.map (fun l -> l.atom)) clauses) in
        check
          (not
             (exists_model size (fun bits -> clauses_model 1 (interpretation table bits) clauses)))
          "duplicate namespace witness did not identify the existential constants";
        let theory, certificate, _ = prove "naive" in
        let duplicate =
          { certificate with axioms = List.hd certificate.axioms :: certificate.axioms }
        in
        match Kernel.check theory duplicate with
        | Error _ -> ()
        | Ok _ -> failwith "kernel accepted duplicate axiom IDs" );
    ( "unused definitions are interpreted after all axioms choose their Skolem witnesses",
      fun () ->
        let atom ax = P ("p", [ Fn (Skolem (ax, 0), []) ]) in
        let ds =
          [| { C.conjunction = true; arguments = []; children = [ C.DBase (true, atom 14) ] } |]
        in
        let lookup id = if id = 0 then Some ds.(0) else None in
        let clauses =
          Option.get
            (C.wire_definitional_cnf lookup
               (fun () -> true)
               ( = ) 1 100 7
               (C.MLiteral (true, atom 7))
               (C.DBase (true, atom 7)))
        in
        let second = compile_axiom Distributive 14 (Ex (Neg (p (B 0)))) in
        let fresh aux key args =
          equal args [] "unexpected nonconstant dependency";
          match key with
          | Sk (7, 0) -> 0
          | Sk (14, 0) -> 1
          | Aux (7, 0) -> aux
          | _ -> failwith "unexpected namespace"
        in
        check
          (clauses_model 1 (fresh 0) (clauses @ second))
          "unused foreign Skolem reference lost the common model";
        check
          (not (clauses_model 1 (fresh 1) (clauses @ second)))
          "auxiliary chosen before the foreign witness was fixed should become invalid" );
    ( "separate axiom namespaces preserve different arities at machine-integer limits",
      fun () ->
        List.iter
          (fun modes ->
            check_theory modes
              [
                (max_int - 1, All (Ex (r (B 1) (B 0))));
                (max_int, Ex (Conj [ Neg (p (B 0)); Eq (B 0, B 0) ]));
              ])
          [ [ Distributive; Definitional ]; [ Definitional; Hybrid ]; [ Hybrid; Distributive ] ] );
  ]

let () = run tests
