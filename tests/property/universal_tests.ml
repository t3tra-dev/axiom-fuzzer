open Axiom_fuzzer
open Test_support
open Wire
module C = Source_checker

let support (_, (_, vs)) = vs
let update rho v x i = if i = v then x else rho i

let literal model rho (positive, (id, vars)) =
  let code = List.fold_left (fun n v -> ((2 * n) + rho v) mod 4) id vars in
  positive = (model land (1 lsl code) <> 0)

let rec universal_holds model rho = function
  | C.ULiteral l -> literal model rho l
  | UConj fs -> List.for_all (universal_holds model rho) fs
  | UDisj fs -> List.exists (universal_holds model rho) fs
  | UAll (v, f) -> List.for_all (fun x -> universal_holds model (update rho v x) f) [ 0; 1 ]

let rec matrix_holds model rho = function
  | C.MLiteral l -> literal model rho l
  | MConj fs -> List.for_all (matrix_holds model rho) fs
  | MDisj fs -> List.exists (matrix_holds model rho) fs

let rec erased = function
  | C.ULiteral l -> C.MLiteral l
  | UConj fs -> C.MConj (List.map erased fs)
  | UDisj fs -> C.MDisj (List.map erased fs)
  | UAll (_, f) -> erased f

let all_assignments count predicate =
  let rec loop bits =
    bits = 1 lsl count || (predicate (fun i -> (bits lsr i) land 1) && loop (bits + 1))
  in
  loop 0

let generated rng depth =
  let next = ref 0 in
  let rec go allowed n =
    if n = 0 then
      C.ULiteral
        ( Random.State.bool rng,
          (Random.State.int rng 3, List.filter (fun _ -> Random.State.bool rng) allowed) )
    else
      match Random.State.int rng 4 with
      | 0 -> go allowed 0
      | 1 when !next < 6 ->
          let id = !next in
          incr next;
          C.UAll (id, go (id :: allowed) (n - 1))
      | choice ->
          let fs = List.init (Random.State.int rng 4) (fun _ -> go allowed (n - 1)) in
          if choice = 2 then C.UConj fs else UDisj fs
  in
  let tree = go [] depth in
  (tree, !next)

let compile ?(limit = max_int) ?(visit = fun () -> true) ?(next_v = 0) ?(next_s = 0) f =
  C.eliminate_quantifiers visit
    (fun s args -> Fn (Original s, args))
    (fun i -> V (0, i))
    (fun id args -> Fn (Skolem (3, id), args))
    (fun positive s ts -> (positive, P (s, ts)))
    (fun positive x y -> (positive, E (x, y)))
    limit [] [] next_v next_s f

let rec count all = function
  | C.NPred _ | NEqual _ -> 0
  | NConj fs | NDisj fs -> List.fold_left (fun n f -> n + count all f) 0 fs
  | NAll f -> (if all then 1 else 0) + count all f
  | NEx f -> (if all then 0 else 1) + count all f

let generated_normal rng =
  let rec go depth size =
    if size = 0 then
      let term =
        if depth = 0 then Wire_types.App ("a", []) else Wire_types.B (Random.State.int rng depth)
      in
      C.NPred (Random.State.bool rng, "p", [ term ])
    else
      match Random.State.int rng 5 with
      | 0 -> go depth 0
      | 1 -> C.NAll (go (depth + 1) (size - 1))
      | 2 -> C.NEx (go (depth + 1) (size - 1))
      | choice ->
          let fs = List.init (Random.State.int rng 4) (fun _ -> go depth (size - 1)) in
          if choice = 3 then C.NConj fs else NDisj fs
  in
  go 0 4

let tests =
  [
    ( "universal erasure preserves closed finite-model semantics across branches",
      fun () ->
        let rng = Random.State.make [| 672104 |] in
        for _ = 1 to 300 do
          let tree, count = generated rng 4 in
          equal
            (C.universal_scope support [] max_int 0 tree)
            (Some count) "scope checker lost variable supply";
          let matrix = Option.get (C.checked_universals support max_int tree) in
          equal matrix (erased tree) "erasure changed connective order or multiplicity";
          for model = 0 to 15 do
            let globally = all_assignments count (fun rho -> matrix_holds model rho matrix) in
            equal
              (universal_holds model (fun _ -> 0) tree)
              globally "quantifier erasure changed truth";
            equal
              (universal_holds model (fun _ -> 1) tree)
              globally "closed formula depends on initial valuation"
          done
        done );
    ( "universal erasure rejects shared IDs whose disjunction would become a tautology",
      fun () ->
        let p = C.ULiteral (true, (0, [ 0 ])) and not_p = C.ULiteral (false, (0, [ 0 ])) in
        let bad = C.UDisj [ C.UAll (0, p); C.UAll (0, not_p) ] in
        check (not (universal_holds 2 (fun _ -> 0) bad)) "test needs a false quantified formula";
        check
          (all_assignments 1 (fun rho -> matrix_holds 2 rho (erased bad)))
          "test needs an unsound tautological erasure";
        equal (C.checked_universals support max_int bad) None "sibling universal reused an ID";
        let valid = C.UDisj [ C.UAll (0, p); C.UAll (1, C.ULiteral (false, (0, [ 1 ]))) ] in
        let matrix = Option.get (C.checked_universals support max_int valid) in
        check
          (not (all_assignments 2 (fun rho -> matrix_holds 2 rho matrix)))
          "fresh siblings lost counterassignment" );
    ( "universal scopes reject sibling leakage, shadowing and future references",
      fun () ->
        let p i = C.ULiteral (true, (0, [ i ])) in
        List.iter
          (fun tree ->
            equal (C.checked_universals support max_int tree) None "invalid lexical scope accepted")
          [
            p 0;
            C.UConj [ C.UAll (0, p 0); p 0 ];
            UAll (0, UAll (0, p 0));
            UAll (0, p 1);
            UAll (1, p 1);
            UAll (0, p max_int);
          ];
        check
          (C.checked_universals support max_int (C.UAll (0, UConj [ UAll (1, p 0); p 0 ])) <> None)
          "outer variable was not available after a nested branch" );
    ( "universal scope limits reject before integer increment",
      fun () ->
        let leaf = C.ULiteral (true, (0, [])) in
        equal
          (C.checked_universals support 0 leaf)
          (Some (C.MLiteral (true, (0, []))))
          "ground formula needs no supply";
        equal
          (C.checked_universals support 0 (C.UAll (0, leaf)))
          None "universal escaped zero budget";
        equal
          (C.checked_universals support 1 (C.UAll (0, leaf)))
          (Some (C.MLiteral (true, (0, []))))
          "exact supply rejected";
        let last = C.UAll (max_int - 1, C.ULiteral (true, (0, [ max_int - 1 ]))) in
        equal
          (C.universal_scope support [] max_int (max_int - 1) last)
          (Some max_int) "last available variable rejected";
        equal
          (C.universal_scope support [] max_int max_int (C.UAll (max_int, leaf)))
          None "variable supply overflowed" );
    ( "quantifier traversal consumes exactly the universal and existential counts",
      fun () ->
        let rng = Random.State.make [| 667281 |] in
        for _ = 1 to 300 do
          let normal = generated_normal rng in
          let result = Option.get (compile ~next_v:7 ~next_s:11 normal) in
          equal result.next_variable (7 + count true normal) "universal supply drifted";
          equal result.next_symbol (11 + count false normal) "Skolem supply drifted";
          let exact = max (count true normal) (count false normal) in
          check (compile ~limit:exact normal <> None) "exact two-supply budget rejected";
          if exact > 0 then
            equal (compile ~limit:(exact - 1) normal) None "allocation exceeded its supply"
        done );
    ( "quantifier allocation keeps lexical Skolem arguments and global sibling IDs",
      fun () ->
        let normal =
          C.NEx
            (NConj
               [
                 NAll (NEx (NPred (true, "p", [ Wire_types.B 2; Wire_types.B 1; Wire_types.B 0 ])));
                 NAll
                   (NAll
                      (NEx
                         (NPred
                            ( false,
                              "q",
                              [ Wire_types.B 3; Wire_types.B 2; Wire_types.B 1; Wire_types.B 0 ] ))));
               ])
        in
        let r = Option.get (compile normal) in
        equal (r.next_variable, r.next_symbol) (3, 3) "sibling supplies were reset";
        equal r.supplied_value
          (C.UConj
             [
               UAll
                 ( 0,
                   ULiteral
                     (true, P ("p", [ Fn (Skolem (3, 0), []); v 0; Fn (Skolem (3, 1), [ v 0 ]) ]))
                 );
               UAll
                 ( 1,
                   UAll
                     ( 2,
                       ULiteral
                         ( false,
                           P
                             ( "q",
                               [
                                 Fn (Skolem (3, 0), []); v 1; v 2; Fn (Skolem (3, 2), [ v 1; v 2 ]);
                               ] ) ) ) );
             ])
          "witness depends on a sibling universal or omits an enclosing one" );
    ( "quantifier supplies reach max_int without wrapping",
      fun () ->
        let normal = C.NAll (NEx (NPred (true, "p", [ Wire_types.B 1; Wire_types.B 0 ]))) in
        let r = Option.get (compile ~next_v:(max_int - 1) ~next_s:(max_int - 1) normal) in
        equal (r.next_variable, r.next_symbol) (max_int, max_int) "last fresh supply overflowed";
        equal (compile ~next_v:max_int (C.NAll (NConj []))) None "universal increment overflowed";
        equal (compile ~next_s:max_int (C.NEx (NConj []))) None "Skolem increment overflowed";
        check
          (compile ~next_v:max_int ~next_s:max_int (C.NConj []) <> None)
          "unused exhausted supply rejected" );
    ( "quantifier traversal rejects malformed original binder environments",
      fun () ->
        List.iter
          (fun normal -> equal (compile normal) None "invalid binder environment accepted")
          [
            C.NPred (true, "p", [ Wire_types.F 0 ]);
            NPred (true, "p", [ Wire_types.B 0 ]);
            NAll (NPred (true, "p", [ Wire_types.B 1 ]));
            NEx (NEqual (false, Wire_types.B 0, Wire_types.F max_int));
            NConj [ NAll (NConj []); NPred (true, "p", [ Wire_types.B 0 ]) ];
          ] );
    ( "quantifier traversal cancellation cannot advance into later siblings",
      fun () ->
        let f =
          C.NConj
            [
              NAll (NEx (NPred (true, "p", [ Wire_types.B 1; Wire_types.B 0 ])));
              NEx (NAll (NEqual (false, Wire_types.App ("f", [ Wire_types.B 1 ]), Wire_types.B 0)));
            ]
        in
        let total = ref 0 in
        ignore
          (compile
             ~visit:(fun () ->
               incr total;
               true)
             f);
        for stop = 1 to !total do
          let calls = ref 0 in
          equal
            (compile
               ~visit:(fun () ->
                 incr calls;
                 !calls <> stop)
               f)
            None "partial quantifier result accepted";
          equal !calls stop "cancelled traversal evaluated later nodes"
        done );
  ]

let () = run tests
