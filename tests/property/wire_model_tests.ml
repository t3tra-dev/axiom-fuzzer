open Axiom_fuzzer
open Test_support
open Wire
module C = Source_checker

let code xs = List.fold_left (fun n x -> ((2 * n) + x) land 3) 0 xs

let rec value model sk rho = function
  | V v -> rho v
  | Fn (Original s, ts) ->
      (String.length s + model + List.fold_left ( + ) 0 (List.map (value model sk rho) ts)) land 1
  | Fn (Skolem (ax, id), ts) -> sk (ax, id) (List.map (value model sk rho) ts)

let atom_holds model sk aux rho = function
  | P (_, ts) -> model land (1 lsl code (List.map (value model sk rho) ts)) <> 0
  | E (x, y) -> value model sk rho x = value model sk rho y
  | D (id, ts) -> aux id (List.map (value model sk rho) ts)

let clauses_hold model sk aux rho cs =
  List.for_all (List.exists (fun l -> l.positive = atom_holds model sk aux rho l.atom)) cs

let skolem model (ax, id) args = (model + ax + id + List.fold_left ( + ) 0 args) land 1
let lookup ds id = if id >= 0 && id < Array.length ds then Some ds.(id) else None

let checked ?(visit = fun () -> true) ?(budget = 100000) ds m root =
  C.wire_definitional_cnf (lookup ds) visit ( = ) (Array.length ds) budget 7 m root

let atom_vars a =
  let rec term = function V (_, i) -> [ i ] | Fn (_, ts) -> List.concat_map term ts in
  (match a with P (_, ts) | D (_, ts) -> List.concat_map term ts | E (x, y) -> term x @ term y)
  |> List.sort_uniq Int.compare

let valid_base = P ("p", [])

let tests =
  [
    ( "extracted Wire support contains exactly the semantic variable dependencies",
      fun () ->
        let rng = Random.State.make [| 736105 |] in
        let rec term n =
          if n = 0 then v (Random.State.int rng 5)
          else
            match Random.State.int rng 4 with
            | 0 -> term 0
            | 1 -> Fn (Original "f", List.init (Random.State.int rng 4) (fun _ -> term (n - 1)))
            | _ ->
                Fn
                  ( Skolem (7, Random.State.int rng 3),
                    List.init (Random.State.int rng 3) (fun _ -> term (n - 1)) )
        in
        for _ = 1 to 400 do
          let a =
            if Random.State.bool rng then P ("p", [ term 3; term 3 ]) else E (term 3, term 3)
          in
          let vars = Option.get (C.checked_wire_support a) in
          equal vars (atom_vars a) "variable collection lost, duplicated or reordered a dependency";
          for model = 0 to 15 do
            let rho (_, i) = (model lsr (i mod 4)) land 1 in
            let other (_, i) = if List.mem i vars then rho (0, i) else 1 - rho (0, i) in
            equal
              (atom_holds model (skolem model) (fun _ _ -> false) rho a)
              (atom_holds model (skolem model) (fun _ _ -> false) other a)
              "support omitted a semantic dependency"
          done
        done;
        equal
          (C.checked_wire_support (P ("p", [ v max_int; v 0; v max_int ])))
          (Some [ 0; max_int ])
          "large variable IDs changed order" );
    ( "Wire support rejects foreign scopes, negative integers and auxiliary base atoms",
      fun () ->
        List.iter
          (fun a -> equal (C.checked_wire_support a) None "invalid preprocessing atom accepted")
          [
            P ("p", [ V (1, 0) ]);
            E (v 0, V (-1, 0));
            P ("p", [ Fn (Original "f", [ V (0, -1) ]) ]);
            E (Fn (Skolem (7, 0), [ V (0, min_int) ]), v 0);
            D ((7, 0), []);
            D ((8, 0), [ v 0 ]);
          ];
        equal
          (C.checked_wire_support
             (E (Fn (Skolem (7, 0), [ v 2 ]), Fn (Original "sk_7_0", [ v 1 ]))))
          (Some [ 1; 2 ])
          "distinct function namespaces interfered with variable collection" );
    ( "Wire universal erasure enforces base atoms, lexical scope and cancellation",
      fun () ->
        let p i = C.ULiteral (true, P ("p", [ v i ])) in
        let tree = C.UConj [ UAll (0, p 0); UAll (1, p 1) ] in
        check
          (C.wire_checked_universals (fun () -> true) 2 tree <> None)
          "valid scoped Wire tree rejected";
        List.iter
          (fun bad ->
            equal
              (C.wire_checked_universals (fun () -> true) max_int bad)
              None "malformed Wire tree erased")
          [
            p 0;
            C.UAll (0, ULiteral (true, P ("p", [ V (1, 0) ])));
            UAll (0, ULiteral (true, P ("p", [ V (0, -1) ])));
            ULiteral (true, D ((7, 0), []));
            UDisj [ UAll (0, p 0); UAll (0, p 0) ];
            UConj [ UAll (0, p 0); p 0 ];
          ];
        for stop = 1 to 2 do
          let calls = ref 0 in
          equal
            (C.wire_checked_universals
               (fun () ->
                 incr calls;
                 !calls <> stop)
               2 tree)
            None "cancelled scope check accepted";
          equal !calls stop "scope check visited a sibling after cancellation"
        done;
        equal
          (C.wire_universal_scope
             (fun () -> true)
             [] max_int (max_int - 1)
             (C.UAll (max_int - 1, p (max_int - 1))))
          (Some max_int) "last available scope variable rejected";
        equal
          (C.wire_universal_scope (fun () -> true) [] max_int max_int (C.UAll (max_int, p max_int)))
          None "Wire scope supply overflowed" );
    ( "definition wrapper rejects auxiliary atoms hidden in unused declarations",
      fun () ->
        let bad = C.DBase (false, D ((7, 0), [])) in
        let ds = [| { C.conjunction = true; arguments = []; children = [ bad ] } |] in
        let matrix = C.MLiteral (true, valid_base) and root = C.DBase (true, valid_base) in
        check
          (C.checked_definitions (lookup ds) (fun () -> true) ( = ) C.wire_support 1 100 matrix root
          <> None)
          "generic checker should distinguish base and auxiliary namespaces abstractly";
        equal (checked ds matrix root) None
          "unused declaration merged a base predicate with a new auxiliary";
        equal
          (checked [||] (C.MLiteral (false, D ((7, 0), []))) bad)
          None "auxiliary base root bypassed validation";
        List.iter
          (fun a ->
            let malformed = C.DBase (true, a) in
            equal
              (checked
                 [| { C.conjunction = true; arguments = []; children = [ malformed ] } |]
                 matrix root)
              None "unused declaration bypassed Wire variable validation")
          [ P ("p", [ V (1, 0) ]); E (v 0, V (0, -1)) ] );
    ( "definition records preserve literal signs and ordered auxiliary arguments",
      fun () ->
        let first = P ("r", [ v 2; v 0 ]) and second = E (v 1, v 2) in
        let ds =
          [|
            {
              C.conjunction = true;
              arguments = [ 2; 0; 1 ];
              children = [ C.DBase (true, first); DBase (false, second) ];
            };
          |]
        in
        let matrix = C.MConj [ MLiteral (true, first); MLiteral (false, second) ]
        and root = C.DAux (true, 0, [ 2; 0; 1 ]) in
        let clauses = Option.get (checked ds matrix root) in
        for model = 0 to 15 do
          let aux id args =
            match (id, args) with
            | (7, 0), [ x2; x0; x1 ] -> model land (1 lsl code [ x2; x0 ]) <> 0 && x1 <> x2
            | _ -> failwith "auxiliary identity or argument order changed"
          in
          for values = 0 to 7 do
            let rho (_, i) = (values lsr i) land 1 in
            let expected =
              atom_holds model (skolem model) aux rho first
              && not (atom_holds model (skolem model) aux rho second)
            in
            equal
              (clauses_hold model (skolem model) aux rho clauses)
              expected "Wire conversion changed finite-model truth"
          done
        done );
    ( "fresh Wire namespaces permit simultaneous witnesses for different axioms",
      fun () ->
        let formula sign =
          Ex (Conj [ (if sign then Pred ("p", [ B 0 ]) else Neg (Pred ("p", [ B 0 ]))); Top ])
        in
        List.iter
          (fun mode ->
            let ax id sign =
              {
                axiom_id = id;
                name = "namespace";
                origin = Imported "namespace";
                formula = formula sign;
              }
            in
            let clauses =
              Kernel.input_clauses ~mode (ax 2 true) @ Kernel.input_clauses ~mode (ax 3 false)
            in
            let sk (ax, _) _ =
              if ax = 2 then 0 else if ax = 3 then 1 else failwith "unexpected axiom namespace"
            in
            check
              (clauses_hold 1 sk (fun _ _ -> true) (fun _ -> 0) clauses)
              "different axioms could not choose distinct witnesses";
            check
              (not (clauses_hold 1 (fun _ _ -> 0) (fun _ _ -> true) (fun _ -> 0) clauses))
              "namespace collision example did not distinguish the witnesses")
          [ Distributive; Definitional; Hybrid ] );
    ( "Wire CNF wrappers retain budgets, cancellation and machine-integer checks",
      fun () ->
        let matrix = C.MConj [ MLiteral (true, valid_base); MLiteral (false, valid_base) ] in
        equal (C.wire_distributive_cnf (fun () -> true) 1 matrix) None "distributive budget ignored";
        check
          (C.wire_distributive_cnf (fun () -> true) 2 matrix <> None)
          "exact distributive budget rejected";
        let ds =
          [|
            {
              C.conjunction = true;
              arguments = [];
              children = [ C.DBase (true, valid_base); DBase (false, valid_base) ];
            };
          |]
        in
        let root = C.DAux (true, 0, []) in
        equal (checked ~budget:3 ds matrix root) None "definition output exceeded budget";
        check (checked ~budget:4 ds matrix root <> None) "exact definition budget rejected";
        let calls = ref 0 in
        ignore
          (checked
             ~visit:(fun () ->
               incr calls;
               true)
             ds matrix root);
        for stop = 1 to !calls do
          let visits = ref 0 in
          equal
            (checked
               ~visit:(fun () ->
                 incr visits;
                 !visits <> stop)
               ds matrix root)
            None "cancelled Wire CNF accepted";
          equal !visits stop "cancelled Wire CNF continued visiting"
        done;
        List.iter
          (fun l ->
            check (not (C.wire_definition_valid l)) "negative auxiliary integer survived extraction")
          [ C.DAux (true, -1, []); DAux (false, 0, [ -1 ]); DAux (true, min_int, [ max_int ]) ] );
  ]

let () = run tests
