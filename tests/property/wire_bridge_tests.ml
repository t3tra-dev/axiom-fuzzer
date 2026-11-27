open Axiom_fuzzer
open Test_support
open Wire
module R = Rocq_checker
module C = Source_checker
module B = Wire_checker

module Normalize = Wire_normalizer.WireNormalize (struct
  type function_name = string
  type predicate_name = string

  let leb a b = compare a b <= 0
  let equal a b = a = b
end)

(* The pre-extraction implementation is an independent compatibility oracle. *)
let legacy_normalize c =
  let names = Hashtbl.create 16 in
  let rec term = function
    | V v ->
        let i =
          match Hashtbl.find_opt names v with
          | Some i -> i
          | None ->
              let i = Hashtbl.length names in
              Hashtbl.add names v i;
              i
        in
        V (0, i)
    | Fn (f, ts) -> Fn (f, List.map term ts)
  in
  let atom = function
    | P (p, ts) -> P (p, List.map term ts)
    | D (p, ts) -> D (p, List.map term ts)
    | E (x, y) ->
        let x = term x in
        let y = term y in
        E (x, y)
  in
  List.sort_uniq compare c
  |> List.map (fun l -> { l with atom = atom l.atom })
  |> List.sort_uniq compare

let generated_clauses seed count =
  let rng = Random.State.make [| seed |] in
  let vars = [| (0, 7); (1, 7); (0, max_int); (max_int, 0) |] in
  let rec term depth =
    if depth = 0 || Random.State.int rng 3 = 0 then V vars.(Random.State.int rng 4)
    else
      let f =
        match Random.State.int rng 4 with
        | 0 -> Original "sk_2_0"
        | 1 -> Original "関数"
        | 2 -> Skolem (2, 0)
        | _ -> Skolem (3, 0)
      in
      Fn (f, List.init (Random.State.int rng 3) (fun _ -> term (depth - 1)))
  in
  let literal () =
    let atom =
      match Random.State.int rng 3 with
      | 0 -> P ((if Random.State.bool rng then "p" else "q"), [ term 2; term 2 ])
      | 1 -> E (term 2, term 2)
      | _ -> D ((Random.State.int rng 4, 0), [ term 2; term 2 ])
    in
    { positive = Random.State.bool rng; atom }
  in
  List.init count (fun _ ->
      let c = List.init (Random.State.int rng 8) (fun _ -> literal ()) in
      match c with l :: _ when Random.State.bool rng -> (l :: c) @ [ l ] | _ -> c)

let variables c =
  let rec term acc = function V v -> v :: acc | Fn (_, ts) -> List.fold_left term acc ts in
  List.fold_left
    (fun acc l ->
      match l.atom with
      | P (_, ts) | D (_, ts) -> List.fold_left term acc ts
      | E (x, y) -> term (term acc x) y)
    [] c
  |> List.sort_uniq compare

let name_code s = String.fold_left (fun n ch -> (n + Char.code ch) land 15) 0 s
let symbol_code = function Original s -> name_code s | Skolem (a, i) -> (3 * a) + (5 * i) + 1
let predicate_code = function C.Named p -> name_code p | Auxiliary (a, i) -> (7 * a) + (3 * i) + 2
let arguments_code xs = List.fold_left (fun n x -> ((2 * n) + x) land 15) 0 xs
let functions model f args = (model + symbol_code f + arguments_code args) land 1

let predicates model p args =
  (model lsr ((predicate_code p + arguments_code args) land 3)) land 1 = 1

let rec value model rho = function
  | V v -> rho v
  | Fn (f, ts) -> functions model f (List.map (value model rho) ts)

let holds model rho l =
  let eval = value model rho in
  l.positive
  =
  match l.atom with
  | P (p, ts) -> predicates model (C.Named p) (List.map eval ts)
  | D (p, ts) -> predicates model (C.Auxiliary p) (List.map eval ts)
  | E (x, y) -> eval x = eval y

let valid model c =
  let vars = variables c in
  List.for_all
    (fun bits ->
      let bindings = List.mapi (fun i v -> (v, (bits lsr i) land 1)) vars in
      List.exists (holds model (fun v -> List.assoc v bindings)) c)
    (List.init (1 lsl List.length vars) Fun.id)

let decode table n =
  Hashtbl.to_seq table |> Seq.find_map (fun (key, id) -> if n = id then Some key else None)

let bridge ?(variable = fun (_, i) -> i) ?(functions = fun _ -> None) ?(predicates = fun _ -> None)
    wire numeric =
  B.encoded_inputs String.equal String.equal variable functions predicates wire numeric

let rec numeric_value model functions rho = function
  | R.Var n -> rho n
  | R.Fun (f, ts) -> functions model f (List.map (numeric_value model functions rho) ts)

let numeric_holds model functions predicates rho (positive, a) =
  let eval = numeric_value model functions rho in
  positive
  =
  match a with
  | R.Pred (p, ts) -> predicates model p (List.map eval ts)
  | R.Eq0 (x, y) -> eval x = eval y

(* The former encoder is a compatibility oracle, independent of the builder's
   private tables. Corrupt decoder fixtures below remain deliberately mutable. *)
type encoding = {
  functions : (symbol, int) Hashtbl.t;
  predicates : (string C.wire_predicate, int) Hashtbl.t;
  variables : (variable, int) Hashtbl.t;
  inputs : R.clause list;
}

let reference_encoding clauses =
  let functions = Hashtbl.create 32
  and predicates = Hashtbl.create 8
  and variables = Hashtbl.create 16 in
  let intern table key =
    match Hashtbl.find_opt table key with
    | Some id -> id
    | None ->
        let id = Hashtbl.length table in
        Hashtbl.add table key id;
        id
  in
  let rec term = function
    | V v -> R.Var (intern variables v)
    | Fn (s, ts) ->
        let id = intern functions s in
        R.Fun (id, List.map term ts)
  in
  let atom = function
    | P (p, ts) ->
        let id = intern predicates (C.Named p) in
        R.Pred (id, List.map term ts)
    | D (p, ts) ->
        let id = intern predicates (C.Auxiliary p) in
        R.Pred (id, List.map term ts)
    | E (x, y) ->
        let x = term x in
        let y = term y in
        R.Eq0 (x, y)
  in
  let inputs = List.map (List.map (fun l -> (l.positive, atom l.atom))) clauses in
  { functions; predicates; variables; inputs }

let tests =
  [
    ( "extracted normalization preserves legacy order and first-occurrence numbering",
      fun () ->
        List.iter
          (fun c ->
            equal (Kernel.normalize c) (legacy_normalize c)
              "normalization changed certificate representation")
          (generated_clauses 418209 600);
        List.iter
          (fun order ->
            let terms = List.init 512 (fun i -> V (i mod 3, order i)) in
            let c = [ positive (P ("p", terms @ List.rev terms)) ] in
            equal (Kernel.normalize c) (legacy_normalize c)
              "balanced variable table changed numbering")
          [ Fun.id; (fun i -> max_int - i); (fun i -> i * 137 mod 512) ];
        let c = [ positive (P ("p", [ V (1, 7); v 7; V (1, 7); v max_int ])) ] in
        equal (Kernel.normalize c)
          [ positive (P ("p", [ v 0; v 1; v 0; v 2 ])) ]
          "scope or first occurrence was lost" );
    ( "normalization preserves universal clause truth in finite models",
      fun () ->
        List.iter
          (fun c ->
            let normalized = Kernel.normalize c in
            for model = 0 to 15 do
              equal (valid model c) (valid model normalized)
                "normalization changed universal closure"
            done)
          (generated_clauses 206159 300) );
    ( "normalization enforces an exact distinct-variable limit without ID arithmetic",
      fun () ->
        let c = [ positive (P ("p", [ V (max_int, max_int); V (0, 0); V (max_int, max_int) ])) ] in
        equal (Normalize.normalize 1 c) None "distinct-variable limit ignored";
        equal (Normalize.normalize 2 c) (Some (legacy_normalize c)) "exact limit rejected";
        equal
          (Normalize.normalize 0 [ positive (P ("p", [ constant "a" ])) ])
          (Some [ positive (P ("p", [ constant "a" ])) ])
          "ground clause consumed a variable";
        equal (Normalize.normalize 0 []) (Some []) "empty clause rejected";
        equal (Normalize.normalize (-1) []) None "negative extracted limit accepted" );
    ( "numeric input encoding preserves signs, arguments and all Wire namespaces",
      fun () ->
        let clauses = generated_clauses 795102 240 in
        let first = List.filteri (fun i _ -> i < 100) clauses
        and rest = List.filteri (fun i _ -> i >= 100) clauses in
        let t = Verified.create [ (7, []); (2, first); (6, []); (9, rest) ] in
        check (Verified.encoding_valid t) "valid native encoding rejected";
        let encoded = Verified.inputs t in
        List.iteri
          (fun id (axiom, index, c) ->
            Verified.record t
              { id; clause = Kernel.normalize c; rule = Input (axiom, index) }
              ~expected:c ~apply:Fun.id)
          [ (2, 99, List.nth first 99); (9, 0, List.hd rest); (9, 139, List.nth rest 139) ];
        equal
          (List.filter_map (function R.Input i, _ -> Some i | _ -> None) (Verified.certificate t))
          [ 99; 100; 239 ] "empty axioms or local indices changed input IDs";
        let t = reference_encoding clauses in
        equal encoded t.inputs "native encoding changed from the independent reference";
        let f model id args = functions model (Option.get (decode t.functions id)) args in
        let p model id args = predicates model (Option.get (decode t.predicates id)) args in
        for model = 0 to 15 do
          for bits = 0 to 15 do
            let rho n = (bits lsr (n mod 4)) land 1 in
            let original v = rho (Hashtbl.find t.variables v) in
            List.iter2
              (List.iter2 (fun l n ->
                   equal (holds model original l) (numeric_holds model f p rho n)
                     "numeric bridge changed truth"))
              clauses t.inputs
          done
        done );
    ( "encoding rejects symbol collisions, missing inverse entries and argument changes",
      fun () ->
        let x = V (1, 4) and y = v 5 in
        let wire =
          [
            [
              positive (P ("p", [ Fn (Skolem (2, 0), [ x; y ]); Fn (Original "sk_2_0", []) ]));
              negative (D ((2, 0), [ x ]));
              positive (E (x, y));
            ];
          ]
        in
        let native = Verified.create [ (0, wire) ] in
        let t = reference_encoding wire in
        equal (Verified.inputs native) t.inputs "namespace encoding changed";
        let enc ?(f = decode t.functions) ?(p = decode t.predicates) numeric =
          bridge ~variable:(Hashtbl.find t.variables) ~functions:f ~predicates:p wire numeric
        in
        check (enc t.inputs) "namespace fixture rejected";
        let fid = Hashtbl.find t.functions (Skolem (2, 0))
        and pid = Hashtbl.find t.predicates (C.Auxiliary (2, 0)) in
        List.iter
          (fun wrong ->
            check
              (not (enc ~f:(fun n -> if n = fid then wrong else decode t.functions n) t.inputs))
              "function alias accepted")
          [ None; Some (Original "sk_2_0"); Some (Skolem (3, 0)); Some (Skolem (2, 1)) ];
        List.iter
          (fun wrong ->
            check
              (not (enc ~p:(fun n -> if n = pid then wrong else decode t.predicates n) t.inputs))
              "predicate alias accepted")
          [ None; Some (C.Named "p"); Some (C.Auxiliary (3, 0)); Some (C.Auxiliary (2, 1)) ];
        let clause = List.hd t.inputs in
        let mutate f = check (not (enc [ f clause ])) "structural encoding corruption accepted" in
        mutate (function (b, a) :: rest -> (not b, a) :: rest | _ -> assert false);
        mutate (function
          | (b, R.Pred (p, [ R.Fun (f, args); a ])) :: rest ->
              (b, R.Pred (p, [ R.Fun (f, List.rev args); a ])) :: rest
          | _ -> assert false);
        mutate (function
          | (b, R.Pred (p, args)) :: rest -> (b, R.Pred (p, List.tl args)) :: rest
          | _ -> assert false);
        mutate (fun c -> List.map (function b, R.Eq0 (x, y) -> (b, R.Eq0 (y, x)) | l -> l) c);
        mutate List.rev;
        mutate List.tl;
        mutate (fun c -> c @ [ List.hd c ]);
        check (not (enc [])) "missing input clause accepted";
        check (not (enc (t.inputs @ [ [] ]))) "extra input clause accepted" );
    ( "encoding requires consistent variables but not an injective forward symbol map",
      fun () ->
        let p _ = Some (C.Named "p") and f _ = Some (Original "a") in
        let x = V (1, 4) and y = v 9 in
        let wire = [ [ positive (P ("p", [ x; x; y; constant "a"; constant "a" ])) ] ] in
        let good =
          [ [ (true, R.Pred (11, [ R.Var 0; R.Var 0; R.Var 0; R.Fun (17, []); R.Fun (23, []) ])) ] ]
        in
        check
          (bridge ~variable:(fun _ -> 0) ~functions:f ~predicates:p wire good)
          "safe variable identification or multiple numeric names for one symbol rejected";
        let bad =
          [ [ (true, R.Pred (11, [ R.Var 0; R.Var 1; R.Var 0; R.Fun (17, []); R.Fun (23, []) ])) ] ]
        in
        check
          (not (bridge ~variable:(fun _ -> 0) ~functions:f ~predicates:p wire bad))
          "one variable acquired inconsistent numeric IDs" );
    ( "encoding rejects negative machine integers and accepts the last representable IDs",
      fun () ->
        let functions _ = Some (Skolem (max_int, max_int))
        and predicates _ = Some (C.Auxiliary (max_int, max_int)) in
        let wire =
          [
            [
              positive
                (D ((max_int, max_int), [ Fn (Skolem (max_int, max_int), [ V (max_int, max_int) ]) ]));
            ];
          ]
        in
        let numeric = [ [ (true, R.Pred (max_int, [ R.Fun (max_int, [ R.Var max_int ]) ])) ] ] in
        check
          (bridge ~variable:(fun _ -> max_int) ~functions ~predicates wire numeric)
          "large IDs overflowed";
        List.iter
          (fun n ->
            let p _ = Some (C.Named "p") in
            List.iter
              (fun variable ->
                check
                  (not
                     (bridge
                        ~variable:(fun _ -> 0)
                        ~predicates:p
                        [ [ positive (P ("p", [ V variable ])) ] ]
                        [ [ (true, R.Pred (0, [ R.Var 0 ])) ] ]))
                  "negative scoped variable accepted")
              [ (n, 0); (0, n) ];
            check
              (not
                 (bridge
                    ~variable:(fun _ -> n)
                    [ [ positive (E (v 0, v 0)) ] ]
                    [ [ (true, R.Eq0 (R.Var n, R.Var n)) ] ]))
              "negative numeric variable accepted";
            check
              (not
                 (bridge ~predicates:p
                    [ [ positive (P ("p", [])) ] ]
                    [ [ (true, R.Pred (n, [])) ] ]))
              "negative numeric predicate accepted";
            let f _ = Some (Original "a") in
            check
              (not
                 (bridge ~functions:f
                    [ [ positive (E (constant "a", constant "a")) ] ]
                    [ [ (true, R.Eq0 (R.Fun (n, []), R.Fun (n, []))) ] ]))
              "negative numeric function accepted";
            List.iter
              (fun ((a, i) as id) ->
                let sk = Fn (Skolem (a, i), []) in
                check
                  (not
                     (bridge
                        ~functions:(fun _ -> Some (Skolem (a, i)))
                        [ [ positive (E (sk, sk)) ] ]
                        [ [ (true, R.Eq0 (R.Fun (0, []), R.Fun (0, []))) ] ]))
                  "negative Skolem name accepted";
                check
                  (not
                     (bridge
                        ~predicates:(fun _ -> Some (C.Auxiliary id))
                        [ [ positive (D (id, [])) ] ]
                        [ [ (true, R.Pred (0, [])) ] ]))
                  "negative auxiliary name accepted")
              [ (n, 0); (0, n) ])
          [ -1; min_int ] );
    ( "checked bridge blocks false numeric refutations caused by symbol collisions",
      fun () ->
        let cases =
          [
            (positive (P ("p", [])), negative (P ("q", [])));
            (positive (P ("p", [ constant "a" ])), negative (P ("p", [ constant "b" ])));
            (positive (P ("p", [])), negative (D ((0, 0), [])));
          ]
        in
        List.iter
          (fun (p, q) ->
            let wire = [ [ p ]; [ q ] ] in
            let encoded = reference_encoding wire in
            let first = List.hd encoded.inputs in
            let second = List.map (fun (_, a) -> (false, a)) first in
            let numeric = [ first; second ]
            and proof = [ (R.Input 0, first); (R.Input 1, second); (R.Resolve (0, 0, 1, 0), []) ] in
            check (R.check numeric proof) "fixture did not produce a numeric refutation";
            check
              (not
                 (bridge ~variable:(Hashtbl.find encoded.variables)
                    ~functions:(decode encoded.functions) ~predicates:(decode encoded.predicates)
                    wire numeric))
              "satisfiable Wire inputs acquired a false refutation";
            let t = Verified.create [ (0, wire) ] in
            List.iteri
              (fun id c ->
                Verified.record t { id; clause = c; rule = Input (0, id) } ~expected:c ~apply:Fun.id)
              wire;
            check
              (rejects (fun () ->
                   Verified.record t
                     { id = 2; clause = []; rule = Resolve (0, 0, 1, 0, []) }
                     ~expected:[] ~apply:Fun.id))
              "native builder accepted a false resolution")
          cases );
    ( "native encoding remains stable while proof elaboration introduces new symbols",
      fun () ->
        let first = [ positive (P ("p", [ v 0 ])) ] in
        let second =
          Kernel.normalize [ negative (P ("p", [ v 0 ])); positive (P ("q", [ v 0 ])) ]
        in
        let wire = [ first; second ] in
        let t = Verified.create [ (0, wire) ] in
        let original = Verified.inputs t in
        List.iteri
          (fun id c ->
            Verified.record t { id; clause = c; rule = Input (0, id) } ~expected:c ~apply:Fun.id)
          wire;
        for i = 0 to 79 do
          let symbol =
            if i mod 2 = 0 then Original ("sk_0_" ^ string_of_int i) else Skolem (0, i - 1)
          in
          let term = Fn (symbol, []) in
          let expected = [ positive (P ("q", [ term ])) ] in
          let sigma = [ ((1, 0), term); ((2, 0), term) ] in
          let apply = function
            | V v as t -> Option.value ~default:t (List.assoc_opt v sigma)
            | t -> t
          in
          Verified.record t
            { id = i + 2; clause = expected; rule = Resolve (0, 0, 1, 0, sigma) }
            ~expected ~apply;
          check (Verified.encoding_valid t) "later symbols changed an earlier input name"
        done;
        equal original (Verified.inputs t) "previously returned immutable inputs changed";
        check
          (Option.is_some (R.replay original [] (Verified.certificate t)))
          "elaborated proof does not replay";
        check (not (Verified.check t)) "a proof without an empty clause was accepted" );
    ( "primitive lookup supports every rule and rejects absent or out-of-range parents",
      fun () ->
        let a = R.Fun (0, []) and b = R.Fun (1, []) and x = R.Var 0 in
        let p t = (true, R.Pred (0, [ t ])) and n t = (false, R.Pred (0, [ t ])) in
        let eq s t = (true, R.Eq0 (s, t)) in
        let inputs = [| []; [ p a ] |] in
        let db =
          [|
            [ p a ];
            [ n a; p b ];
            [ eq a b ];
            [ (false, R.Eq0 (a, a)); p b ];
            [ eq a b; eq a x ];
            [ p x ];
          |]
        in
        let lookup xs i = if i >= 0 && i < Array.length xs then Some xs.(i) else None in
        let context = (true, R.In_pred (0, [], R.Hole, [])) in
        List.iter
          (fun (rule, expected) ->
            equal
              (R.infer_with (lookup inputs) (lookup db) rule)
              (Some expected) "lookup inference changed its conclusion";
            equal
              (R.infer (Array.to_list inputs) (Array.to_list db) rule)
              (Some expected) "list replay disagrees with lookup")
          [
            (R.Input 1, [ p a ]);
            (R.Instance (5, [ (0, a) ]), [ p a ]);
            (R.Copy 0, [ p a ]);
            (R.Resolve (0, 0, 1, 0), [ p b ]);
            (R.Equality_resolve (3, 0), [ p b ]);
            (R.Paramodulate (2, 0, false, 0, 0, context), [ p b ]);
            (R.Paramodulate (2, 0, true, 1, 1, context), [ n a; p a ]);
            (R.Equality_factor (4, 0, false, 1, false), [ (false, R.Eq0 (b, x)); eq a x; eq a x ]);
          ];
        List.iter
          (fun id ->
            List.iter
              (fun rule ->
                equal
                  (R.infer_with (lookup inputs) (lookup db) rule)
                  None "invalid primitive reference accepted")
              [
                R.Input id;
                R.Copy id;
                R.Instance (id, []);
                R.Resolve (id, 0, 0, 0);
                R.Equality_resolve (id, 0);
                R.Paramodulate (id, 0, false, 0, 0, context);
                R.Equality_factor (id, 0, false, 1, false);
              ])
          [ -1; 6; max_int ];
        equal
          (R.infer_with (lookup inputs)
             (fun i -> if i = 5 then None else lookup db i)
             (R.Instance (5, [])))
          None "missing parent accepted" );
    ( "long sparse-ID proofs survive database growth and reject malformed late steps",
      fun () ->
        let theory =
          Theory.custom ~name:"long-proof"
            (Signature.make ~functions:[ ("a", 0); ("b", 0) ] ~predicates:[ ("p", 1) ])
            [
              ("eq", Eq (App ("a", []), App ("b", [])));
              ("p", Pred ("p", [ App ("a", []) ]));
              ("not-p", Neg (Pred ("p", [ App ("a", []) ])));
            ]
        in
        let axioms = Theory.fixed theory in
        let initial =
          List.mapi
            (fun i ax ->
              {
                id = 17 * (i + 1);
                rule = Input (ax.axiom_id, 0);
                clause = List.hd (Kernel.input_clauses ~mode:Distributive ax);
              })
            axioms
        in
        let steps = ref (List.rev initial) and previous = ref 34 in
        for i = 0 to 127 do
          let id = 17 * (i + 4) and reverse = i mod 2 = 1 in
          steps :=
            {
              id;
              clause = [ positive (P ("p", [ constant (if reverse then "a" else "b") ])) ];
              rule = Paramodulate (17, 0, reverse, !previous, 0, [ 0 ], []);
            }
            :: !steps;
          previous := id
        done;
        let root = 17 * 132 in
        let finish rule =
          {
            natural = None;
            avatar = None;
            cnf_mode = Distributive;
            theory = Theory.name theory;
            axioms;
            root;
            steps = List.rev ({ id = root; clause = []; rule } :: !steps);
          }
        in
        (match Kernel.check theory (finish (Resolve (!previous, 0, 51, 0, []))) with
        | Ok _ -> ()
        | Error e -> failwith ("long proof rejected: " ^ e));
        List.iter
          (fun rule ->
            match Kernel.check theory (finish rule) with
            | Error _ -> ()
            | Ok _ -> failwith "malformed late proof step accepted")
          [
            Resolve (root, 0, 51, 0, []);
            Resolve (!previous, -1, 51, 0, []);
            Resolve (max_int, 0, 51, 0, []);
            Resolve (!previous, 0, 51, 0, [ ((1, 0), V (1, 0)) ]);
            Resolve (!previous, 0, 51, 0, [ ((1, 0), constant "a"); ((1, 0), constant "a") ]);
          ] );
  ]

let () = run tests
