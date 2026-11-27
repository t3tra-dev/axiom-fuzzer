open Axiom_fuzzer
open Test_support
module C = Source_checker

exception Stopped

(* A base predicate carries its actual variable arguments. Truth tables below
   vary the predicate interpretation independently of the proposed circuit. *)
let support (_, vars) = vars
let lookup ds id = if id >= 0 && id < Array.length ds then Some ds.(id) else None

let checked ?(budget = 100000) ?(visit = fun () -> true) ds matrix root =
  C.checked_definitions (lookup ds) visit ( = ) support (Array.length ds) budget matrix root

let opposite = function
  | C.DBase (b, a) -> C.DBase (not b, a)
  | DAux (b, id, vs) -> C.DAux (not b, id, vs)

let root id d = C.DAux (true, id, d.C.arguments)

let reference_clauses id d =
  let r = root id d in
  if d.C.conjunction then
    List.map (fun l -> [ opposite r; l ]) d.children @ [ r :: List.map opposite d.children ]
  else [ opposite r :: d.children ] @ List.map (fun l -> [ r; opposite l ]) d.children

let propose matrix =
  let ds = ref [] and next = ref 0 in
  let rec visit = function
    | C.MLiteral (b, a) -> C.DBase (b, a)
    | MConj ms -> connective true ms
    | MDisj ms -> connective false ms
  and connective conjunction ms =
    let children = List.map visit ms in
    let arguments =
      List.concat_map (function C.DBase (_, a) -> support a | DAux (_, _, vs) -> vs) children
      |> List.sort_uniq Int.compare
    in
    let d = { C.conjunction; arguments; children } in
    let id = !next in
    incr next;
    ds := d :: !ds;
    root id d
  in
  let r = visit matrix in
  (Array.of_list (List.rev !ds), r)

let clauses ds m r =
  match checked ds m r with Some cs -> cs | None -> failwith "valid circuit rejected"

let tuples n = List.init (1 lsl n) (fun bits -> List.init n (fun i -> (bits lsr i) land 1))
let vector_index values = List.fold_right (fun x rest -> x + (2 * rest)) values 0

let base model rho (id, vars) =
  model land (1 lsl ((id + vector_index (List.map rho vars)) mod 4)) <> 0

let literal model aux rho = function
  | C.DBase (b, a) -> b = base model rho a
  | DAux (b, id, vars) -> b = aux id (List.map rho vars)

let rec matrix_holds model rho = function
  | C.MLiteral (b, a) -> b = base model rho a
  | MConj ms -> List.for_all (matrix_holds model rho) ms
  | MDisj ms -> List.exists (matrix_holds model rho) ms

let clauses_hold model aux rho cs = List.for_all (List.exists (literal model aux rho)) cs

let extension model ds =
  let tables = Array.make (Array.length ds) [] in
  let aux id args = List.assoc args tables.(id) in
  Array.iteri
    (fun id d ->
      tables.(id) <-
        List.map
          (fun values ->
            let env = List.combine d.C.arguments values in
            let rho v = Option.value ~default:0 (List.assoc_opt v env) in
            let f = literal model aux rho in
            (values, if d.conjunction then List.for_all f d.children else List.exists f d.children))
          (tuples (List.length d.arguments)))
    ds;
  aux

let generated rng depth =
  let rec go n =
    if n = 0 || Random.State.int rng 3 = 0 then
      C.MLiteral
        ( Random.State.bool rng,
          (Random.State.int rng 3, List.filter (fun _ -> Random.State.bool rng) [ 0; 1 ]) )
    else
      let ms = List.init (Random.State.int rng 4) (fun _ -> go (n - 1)) in
      if Random.State.bool rng then C.MConj ms else MDisj ms
  in
  go depth

let a = C.MLiteral (true, (0, [ 0 ]))
and b = C.MLiteral (false, (1, [ 1 ]))

let tests =
  [
    ( "definition checker preserves clause order, duplicates and empty connectives",
      fun () ->
        let rng = Random.State.make [| 71826 |] in
        let examples =
          [ a; C.MConj []; MDisj []; MConj [ a; a; b ]; MDisj [ MConj [ a; b ]; MDisj [] ] ]
        in
        List.iter
          (fun m ->
            let ds, r = propose m in
            let expected = Array.to_list (Array.mapi reference_clauses ds) |> List.concat in
            equal (clauses ds m r) (expected @ [ [ r ] ])
              "definition clauses changed order or multiplicity")
          (examples @ List.init 300 (fun _ -> generated rng 3)) );
    ( "one auxiliary model works for every valuation of a matrix",
      fun () ->
        let rng = Random.State.make [| 98792 |] in
        for _ = 1 to 200 do
          let m = generated rng 3 in
          let ds, r = propose m in
          let cs = clauses ds m r in
          for model = 0 to 15 do
            let aux = extension model ds in
            List.iter
              (fun values ->
                let rho i = List.nth values i in
                equal (clauses_hold model aux rho cs) (matrix_holds model rho m)
                  "first-order model extension changed meaning")
              (tuples 2)
          done
        done );
    ( "universal matrix satisfiability equals existence of a uniform auxiliary model",
      fun () ->
        List.iter
          (fun m ->
            let ds, r = propose m in
            let cs = clauses ds m r in
            let total = ref 0 in
            let offsets =
              Array.map
                (fun d ->
                  let offset = !total in
                  total := !total + (1 lsl List.length d.C.arguments);
                  offset)
                ds
            in
            for model = 0 to 15 do
              let universally predicate =
                List.for_all (fun values -> predicate (fun i -> List.nth values i)) (tuples 2)
              in
              let rec exists_interpretation bits =
                bits < 1 lsl !total
                && (universally (fun rho ->
                        clauses_hold model
                          (fun id args -> bits land (1 lsl (offsets.(id) + vector_index args)) <> 0)
                          rho cs)
                   || exists_interpretation (bits + 1))
              in
              equal (exists_interpretation 0)
                (universally (fun rho -> matrix_holds model rho m))
                "auxiliary quantifier incorrectly depends on valuation"
            done)
          [ a; C.MConj []; MDisj []; MConj [ a; b ]; MDisj [ a; b ]; MDisj [ MConj [ a; b ]; a ] ]
    );
    ( "definition checker rejects cycles, forward references and lost arguments",
      fun () ->
        let m = C.MConj [ C.MConj [ a ]; b ] in
        let ds, r = propose m in
        let reject index d message =
          let bad = Array.copy ds in
          bad.(index) <- d;
          equal (checked bad m r) None message
        in
        reject 0 { (ds.(0)) with children = [ root 0 ds.(0) ] } "self reference accepted";
        reject 0 { (ds.(0)) with children = [ root 1 ds.(1) ] } "forward reference accepted";
        reject 0 { (ds.(0)) with arguments = [] } "base-variable dependency omitted";
        reject 1 { (ds.(1)) with arguments = [ 1 ] } "auxiliary-variable dependency omitted";
        let d =
          { C.conjunction = true; arguments = []; children = [ C.DBase (true, (0, [ 0 ])) ] }
        in
        equal
          (checked [| d |] (C.MConj [ a ]) (root 0 d))
          None "nullary definition accepted a varying predicate" );
    ( "definition checker rejects missing nodes and mismatched syntax",
      fun () ->
        let m = C.MDisj [ C.MConj [ a ]; b ] in
        let ds, r = propose m in
        let bad = Array.copy ds in
        bad.(1) <- { (bad.(1)) with conjunction = true };
        equal (checked bad m r) None "wrong connective accepted";
        equal (checked ds m (opposite r)) None "negative root accepted";
        equal (checked ds (C.MDisj [ C.MConj [ b ]; b ]) r) None "changed base atom accepted";
        equal (checked ds (C.MDisj [ C.MConj [ a ] ]) r) None "missing child accepted";
        let missing id = if id = 0 then None else lookup ds id in
        equal
          (C.checked_definitions missing (fun () -> true) ( = ) support 2 1000 m r)
          None "missing declaration accepted";
        equal (checked ds m (C.DAux (true, max_int, []))) None "out-of-range ID overflowed" );
    ( "definition clause budgets include the root and reject before allocation",
      fun () ->
        let m = C.MConj [ a; b ] in
        let ds, r = propose m in
        equal (checked ~budget:4 ds m r) (Some (clauses ds m r)) "exact budget rejected";
        equal (checked ~budget:3 ds m r) None "root unit omitted from budget";
        equal
          (checked ~budget:0 [||] a (C.DBase (true, (0, [ 0 ]))))
          None "leaf escaped zero budget";
        equal (checked ~budget:max_int ds m r) (checked ds m r) "large budget overflowed";
        let huge =
          {
            C.conjunction = true;
            arguments = [];
            children = List.init 100000 (fun _ -> C.DBase (true, (0, [])));
          }
        in
        let allocated () =
          let s = Gc.quick_stat () in
          s.minor_words +. s.major_words -. s.promoted_words
        in
        let before = allocated () in
        equal
          (C.emit_definitions (lookup [| huge |]) (fun () -> true) 1 0 2)
          None "oversized declaration accepted";
        check (allocated () -. before < 1000.) "clauses allocated before checking budget" );
    ( "definition supports preserve machine integer limits and variable order",
      fun () ->
        let vars = [ max_int; 1; max_int - 1; 0; 1 ] in
        equal
          (C.definition_variables support [ C.DBase (true, (0, vars)); C.DAux (true, 0, [ 2; 1 ]) ])
          [ 0; 1; 2; max_int - 1; max_int ]
          "support ordering or bounds changed";
        let d =
          {
            C.conjunction = true;
            arguments = [ max_int ];
            children = [ C.DBase (true, (0, [ max_int ])) ];
          }
        in
        let m = C.MConj [ C.MLiteral (true, (0, [ max_int ])) ] in
        check (checked [| d |] m (root 0 d) <> None) "last valid variable rejected";
        check (C.literal_before max_int (C.DAux (true, max_int - 1, []))) "last earlier ID rejected";
        check (not (C.literal_before max_int (C.DAux (true, max_int, [])))) "same ID overflowed" );
    ( "definition cancellation cannot return partial clauses",
      fun () ->
        let m = C.MConj [ C.MDisj [ a; b ]; a ] in
        let ds, r = propose m in
        let total = ref 0 in
        ignore
          (checked
             ~visit:(fun () ->
               incr total;
               true)
             ds m r);
        for stop = 1 to !total do
          let calls = ref 0 in
          equal
            (checked
               ~visit:(fun () ->
                 incr calls;
                 !calls <> stop)
               ds m r)
            None "cancelled circuit accepted"
        done;
        let ax =
          {
            Wire.axiom_id = 8;
            name = "cancel";
            origin = Imported "cancel";
            formula =
              All
                (Ex (Disj [ Pred ("p", [ B 1; B 0 ]); Conj [ Eq (B 0, B 1); Pred ("q", [ B 1 ]) ] ]));
          }
        in
        let total = ref 0 in
        ignore (Kernel.input_clauses ~mode:Definitional ~guard:(fun () -> incr total) ax);
        for stop = 1 to !total do
          let calls = ref 0 in
          let stopped =
            try
              ignore
                (Kernel.input_clauses ~mode:Definitional
                   ~guard:(fun () ->
                     incr calls;
                     if !calls = stop then raise Stopped)
                   ax);
              false
            with Stopped -> true
          in
          check stopped "kernel swallowed cancellation during definition validation"
        done );
  ]

let () = run tests
