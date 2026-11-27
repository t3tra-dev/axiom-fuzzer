open Axiom_fuzzer
open Test_support
open Wire
module C = Source_checker

let domain = [ 0; 1 ]
let forall f = List.for_all f domain
let exists f = List.exists f domain
let update free variable value i = if i = variable then value else free i
let membership model x y = model land (1 lsl ((2 * x) + y)) <> 0

let eval model free formula =
  let term bound = function
    | B i -> List.nth bound i
    | F i -> free i
    | App _ -> failwith "unexpected schema-test function"
  in
  let rec holds bound = function
    | Top -> true
    | Bot -> false
    | Pred ("member", [ x; y ]) -> membership model (term bound x) (term bound y)
    | Pred _ -> failwith "unexpected schema-test predicate"
    | Eq (x, y) -> term bound x = term bound y
    | Neg f -> not (holds bound f)
    | Conj fs -> List.for_all (holds bound) fs
    | Disj fs -> List.exists (holds bound) fs
    | All f -> forall (fun x -> holds (x :: bound) f)
    | Ex f -> exists (fun x -> holds (x :: bound) f)
  in
  holds [] formula

let schema_meaning kind model free phi =
  let mem = membership model in
  let unary x = eval model (update free 0 x) phi in
  let relation x y = eval model (update (update free 0 x) 1 y) phi in
  match kind with
  | C.Comprehension | UnrestrictedSeparation ->
      exists (fun result -> forall (fun x -> mem x result = unary x))
  | Separation ->
      forall (fun set ->
          exists (fun result -> forall (fun x -> mem x result = (mem x set && unary x))))
  | Replacement ->
      let functional =
        forall (fun x ->
            exists (fun y -> relation x y && forall (fun z -> (not (relation x z)) || z = y)))
      in
      (not functional)
      || forall (fun set ->
          exists (fun result ->
              forall (fun y -> mem y result = exists (fun x -> mem x set && relation x y))))

let rec parameter_meaning variables meaning free =
  match variables with
  | [] -> meaning free
  | v :: vs -> forall (fun x -> parameter_meaning vs meaning (update free v x))

let rec generated rng depth size =
  let term () =
    if depth > 0 && Random.State.int rng 3 = 0 then B (Random.State.int rng depth)
    else F (Random.State.int rng 4)
  in
  if size = 0 then
    match Random.State.int rng 4 with
    | 0 -> Top
    | 1 -> Bot
    | 2 -> Pred ("member", [ term (); term () ])
    | _ -> Eq (term (), term ())
  else
    match Random.State.int rng 6 with
    | 0 -> generated rng depth 0
    | 1 -> Neg (generated rng depth (size - 1))
    | 2 -> Conj (List.init (Random.State.int rng 3) (fun _ -> generated rng depth (size - 1)))
    | 3 -> Disj (List.init (Random.State.int rng 3) (fun _ -> generated rng depth (size - 1)))
    | 4 -> All (generated rng (depth + 1) (size - 1))
    | _ -> Ex (generated rng (depth + 1) (size - 1))

let kinds = [ C.Comprehension; Separation; Replacement; UnrestrictedSeparation ]
let parameters = function C.Replacement -> [ 2; 3 ] | _ -> [ 1; 2; 3 ]

let wire_kind = function
  | C.Comprehension -> Wire.Comprehension
  | Separation -> Separation
  | Replacement -> Replacement
  | UnrestrictedSeparation -> Unrestricted_separation

let theory = function
  | C.Comprehension -> Theory.create "naive"
  | UnrestrictedSeparation -> Theory.create "mutated-separation"
  | Separation | Replacement -> Theory.create "zf"

let checked kind variables fresh phi =
  C.checked_schema kind "member" variables fresh (Wire.checked_source phi)

let expansion kind variables fresh phi =
  match checked kind variables fresh phi with
  | Some result -> Wire.source_of_checked result
  | None -> failwith "valid schema expansion rejected"

let tests =
  [
    ( "portable Source equivalence preserves finite-model semantics",
      fun () ->
        let rng = Random.State.make [| 519703 |] in
        for _ = 1 to 200 do
          let phi = generated rng 0 3 in
          let wrapped = Conj [ Top; Neg (Neg phi); phi; Conj [ phi; Top ] ] in
          check (C.equivalent phi wrapped) "Boolean equivalence rejected";
          let simplified = C.simplify wrapped in
          for model = 0 to 15 do
            let free i = (model lsr (i mod 4)) land 1 in
            equal (eval model free simplified) (eval model free phi)
              "Source simplification changed meaning"
          done
        done;
        check (not (C.equivalent Top Bot)) "true and false identified" );
    ( "extracted handle sorting agrees with machine-integer ordering",
      fun () ->
        let rng = Random.State.make [| 48269 |] in
        for size = 0 to 150 do
          let ids =
            List.init size (fun _ ->
                if Random.State.int rng 4 = 0 then max_int else Random.State.int rng 31)
          in
          equal (C.sort_handles ids) (List.sort_uniq compare ids)
            "handle sort changed order or lost a distinct ID"
        done;
        let descending = List.init 10000 (fun i -> 10000 - i) in
        equal
          (C.sort_handles (descending @ descending))
          (List.init 10000 (fun i -> i + 1))
          "large duplicate list mis-sorted" );
    ( "shallow Boolean normalization preserves arbitrary node valuations",
      fun () ->
        let rng = Random.State.make [| 976221 |] in
        let nodes = Array.make 200 (C.BKeep 0) in
        for id = 0 to 199 do
          nodes.(id) <-
            (if id < 4 then C.BKeep id
             else
               match Random.State.int rng 6 with
               | 0 -> BTrue
               | 1 -> BFalse
               | 2 -> BNot (Random.State.int rng id)
               | 3 -> BAnd (List.init (Random.State.int rng 5) (fun _ -> Random.State.int rng id))
               | 4 -> BOr (List.init (Random.State.int rng 5) (fun _ -> Random.State.int rng id))
               | _ -> BKeep (Random.State.int rng id))
        done;
        let view i = nodes.(i) in
        for model = 0 to 15 do
          let values = Array.make 200 false in
          let eval_node = function
            | C.BTrue -> true
            | BFalse -> false
            | BKeep i -> values.(i)
            | BNot i -> not values.(i)
            | BAnd ids -> List.for_all (Array.get values) ids
            | BOr ids -> List.exists (Array.get values) ids
          in
          for id = 0 to 199 do
            values.(id) <- (if id < 4 then model land (1 lsl id) <> 0 else eval_node nodes.(id))
          done;
          for _ = 1 to 200 do
            let ids = List.init (Random.State.int rng 16) (fun _ -> Random.State.int rng 200) in
            equal
              (eval_node (C.boolean_and view ids))
              (List.for_all (Array.get values) ids)
              "conjunction normalization changed meaning";
            equal
              (eval_node (C.boolean_or view ids))
              (List.exists (Array.get values) ids)
              "disjunction normalization changed meaning";
            let id = Random.State.int rng 200 in
            equal
              (eval_node (C.boolean_not view id))
              (not values.(id))
              "negation normalization changed meaning"
          done
        done );
    ( "arena Boolean bridges preserve sharing, ID order and opaque quantifiers",
      fun () ->
        let arena = Source.create Signature.sets in
        let x = Source.free arena 0 and y = Source.free arena 1 in
        let p = Source.member arena x y and q = Source.eq arena x y in
        let all = Source.all arena [ 0; 1 ] p in
        let expected = Source.and_ arena [ p; q; all ] in
        let terms, formulas = Source.counts arena in
        for _ = 1 to 100 do
          equal
            (Source.and_ arena [ all; q; p; expected; p ])
            expected "conjunction lost canonical sharing";
          equal
            (Source.not_ arena (Source.not_ arena all))
            all "opaque quantifier changed under double negation"
        done;
        let terms', formulas' = Source.counts arena in
        equal terms terms' "Boolean normalization allocated terms";
        equal formulas' (formulas + 1) "Boolean normalization repeatedly allocated formulas";
        equal (Wire.export arena expected)
          (Conj [ Wire.export arena p; Wire.export arena q; Wire.export arena all ])
          "arena ID order changed" );
    ( "Boolean constants cannot hide foreign arena inputs",
      fun () ->
        let a = Source.create Signature.sets and b = Source.create Signature.sets in
        let foreign = Source.truth b in
        List.iter
          (fun f -> check (rejects f) "constant simplification erased a foreign handle")
          [
            (fun () -> ignore (Source.and_ a [ Source.falsity a; foreign ]));
            (fun () -> ignore (Source.or_ a [ Source.truth a; foreign ]));
            (fun () -> ignore (Source.not_ a foreign));
          ] );
    ( "all four extracted schemas match their finite-model specifications",
      fun () ->
        let rng = Random.State.make [| 64287 |] in
        for _ = 1 to 120 do
          let phi = generated rng 0 3 in
          List.iter
            (fun kind ->
              let variables = parameters kind in
              let result = expansion kind variables 4 phi in
              check (Wire.source_scoped ~closed:true result) "schema output is not closed";
              for model = 0 to 15 do
                let free i = i land 1 in
                let expected =
                  parameter_meaning variables (fun free -> schema_meaning kind model free phi) free
                in
                equal (eval model free result) expected
                  "schema changed its quantified specification"
              done)
            kinds
        done );
    ( "schema checker rejects captured parameters and missing quantifiers",
      fun () ->
        let phi = Pred ("member", [ F 0; F 2 ]) in
        equal (checked C.Separation [ 2 ] 2 phi) None "fresh set variable captured a parameter";
        equal (checked C.Separation [] 3 phi) None "unclosed parameter accepted";
        equal
          (checked C.Replacement [] 1 (Eq (F 0, F 1)))
          None "result variable collided with a principal variable";
        equal (checked C.Comprehension [] 0 (Eq (F 0, F 0))) None "zero fresh bound accepted";
        equal
          (checked C.Comprehension [ 2 ] 3 (Conj [ Bot; Eq (B 0, F 2) ]))
          None "bad bound index hidden in false branch";
        equal
          (checked C.Separation [ max_int ] max_int (Pred ("member", [ F 0; F max_int ])))
          None "parameter-bound comparison overflowed" );
    ( "schema parameter closure handles renaming, order and unused parameters",
      fun () ->
        let original = Pred ("member", [ F 0; F 2 ]) and renamed = Pred ("member", [ F 0; F 7 ]) in
        List.iter
          (fun kind ->
            let a = expansion kind [ 2; 3 ] 4 original and b = expansion kind [ 7; 5 ] 8 renamed in
            for model = 0 to 15 do
              equal
                (eval model (fun _ -> 0) a)
                (eval model (fun _ -> 1) b)
                "parameter renaming/order changed meaning"
            done)
          [ C.Separation; Replacement ] );
    ( "independent schema reconstruction accepts generated instances",
      fun () ->
        let rng = Random.State.make [| 716243 |] in
        let theories = List.map (fun kind -> (kind, theory kind)) kinds in
        for id = 0 to 99 do
          let raw = generated rng 0 3 in
          List.iter
            (fun (kind, t) ->
              let a = Theory.arena t in
              let phi = Wire.import a raw in
              let ax = Theory.instantiate t ~id:(id + 100) (wire_kind kind) phi in
              check (Theory.validate_axiom t ax)
                "independent schema reconstruction disagrees with generator";
              let copied = Theory.copy t in
              check (Theory.validate_axiom copied ax) "validation depends on arena allocation order")
            theories
        done );
    ( "schema provenance rejects weakened formulas and changed conditions",
      fun () ->
        let t = Theory.create "zf" in
        let a = Theory.arena t in
        let x = Source.free a 0 and y = Source.free a 1 in
        let phi = Source.member a x y in
        let ax = Theory.instantiate t ~id:20 Wire.Replacement phi in
        check (Theory.validate_axiom t ax) "valid replacement rejected";
        List.iter
          (fun bad -> check (not (Theory.validate_axiom t bad)) "forged schema accepted")
          [
            { ax with formula = Top };
            { ax with formula = All (Eq (B 0, B 0)) };
            { ax with origin = Instance (Replacement, Eq (F 0, F 1)) };
            { ax with origin = Instance (Separation, Wire.export a phi) };
            { ax with name = "replacement_19" };
          ];
        let disallowed = Theory.create "separation" in
        check (not (Theory.validate_axiom disallowed ax)) "manifest allowed a replacement instance"
    );
    ( "schema freshness handles the last representable variable indices",
      fun () ->
        List.iter
          (fun kind ->
            let reserved = if kind = C.Replacement then 3 else 2 in
            let t = theory kind in
            let a = Theory.arena t in
            let phi high = Source.member a (Source.free a 0) (Source.free a high) in
            let valid = Theory.instantiate t ~id:20 (wire_kind kind) (phi (max_int - reserved)) in
            check (Theory.validate_axiom t valid) "last safe parameter index rejected";
            check
              (rejects (fun () ->
                   ignore
                     (Theory.instantiate t ~id:21 (wire_kind kind) (phi (max_int - reserved + 1)))))
              "fresh index overflow accepted";
            let forged =
              { valid with origin = Instance (wire_kind kind, Wire.export a (phi max_int)) }
            in
            check (not (Theory.validate_axiom t forged)) "overflowing provenance accepted")
          kinds );
    ( "checked source bridge roundtrips every constructor before normalization",
      fun () ->
        let f =
          All
            (Ex
               (Conj
                  [
                    Top;
                    Bot;
                    Pred ("member", [ B 1; F 0 ]);
                    Eq (App ("f", [ B 0 ]), F max_int);
                    Neg (Disj [ Pred ("p", []); Conj [] ]);
                    Disj [];
                  ]))
        in
        equal
          (Wire.source_of_checked (Wire.checked_source f))
          f "source bridge changed constructors or symbol names" );
  ]

let () = run tests
