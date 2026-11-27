open Axiom_fuzzer
open Test_support
open Wire_types
module N = Natural_checker

let signature = Signature.make ~functions:[ ("c", 0) ] ~predicates:[ ("p", 1) ]

let theory formulas =
  Theory.custom ~name:"natural-test" signature
    (List.mapi (fun i f -> (string_of_int i, f)) formulas)

let source i = Pair (Number 0, N.permission_code (FixedPermission i))
let equality w = Pair (Number 1, N.equality_code w)

let certificate t assumptions deduction =
  Natural.certificate t (N.certificate_code { assumptions; deduction })

let accepts t c = check (Result.is_ok (Kernel.check t c)) "natural certificate rejected"
let rejects_proof t c = check (Result.is_error (Kernel.check t c)) "invalid natural proof accepted"
let term c = Option.get (N.fol_term_value c)
let constant = term (Pair (N.string_code "c", Number 0))
let variable = term (Number 0)
let predicate t = N.named_predicate "p" [ t ]

(* Source.Standard.equal. Extraction renames it in natural_checker.ml, whose AVL functor also
   defines [equal], so the test builds the same formula itself. *)
let standard_equal x y = N.Atom (None, [ x; y ])

let fixture () =
  let p = Pred ("p", [ App ("c", []) ]) in
  let t = theory [ p; Neg p ] in
  (t, certificate t [ source 0; source 1 ] (ImplicationElimination (Assume 1, Assume 0)))

let redundant_fixture () =
  let t, _ = fixture () in
  let p = predicate constant in
  let deduction =
    N.ImplicationElimination
      (ImplicationIntroduction (p, ImplicationElimination (Assume 2, Assume 0)), Assume 0)
  in
  (t, certificate t [ source 0; source 1; source 0 ] deduction)

let minimize t c = (Minimizer.run ~config:config.engine t c).certificate

let tests =
  [
    ( "natural false premise and portable replay",
      fun () ->
        let t = theory [ Bot ] in
        let c = certificate t [ source 0 ] (Assume 0) in
        accepts t c;
        equal (Certificate_io.decode (Certificate_io.encode c)) c "natural serialization";
        rejects_proof (theory []) c;
        check (rejects (fun () -> ignore (Tptp.tstp c))) "empty TSTP proof exported";
        equal
          (List.map (fun (a : Wire.axiom) -> a.formula) (Natural.premises t (Option.get c.natural)))
          [ Bot ] "finite Source premises";
        accepts t (Proof.prune c) );
    ( "natural implication and authority rejection",
      fun () ->
        let t, c = fixture () in
        accepts t c;
        rejects_proof t
          (certificate t [ source 0; source 1 ] (ImplicationElimination (Assume 0, Assume 1)));
        rejects_proof t (certificate t [ source 2 ] (Assume 0));
        rejects_proof t { c with theory = "different" };
        rejects_proof t { c with root = 1 };
        rejects_proof t { c with natural = Some (Number (-1)) } );
    ( "natural quantifiers and existential translation",
      fun () ->
        let p = Pred ("p", [ B 0 ]) in
        let t = theory [ All p; Neg (Pred ("p", [ App ("c", []) ])) ] in
        accepts t
          (certificate t
             [ source 0; source 1 ]
             (ImplicationElimination (Assume 1, UniversalElimination (constant, Assume 0))));
        let t = theory [ Ex p; All (Neg p) ] in
        accepts t
          (certificate t [ source 0; source 1 ] (ImplicationElimination (Assume 0, Assume 1))) );
    ( "natural equality is a logical axiom",
      fun () ->
        let t = theory [ All (Neg (Eq (B 0, B 0))) ] in
        accepts t
          (certificate t
             [ source 0; equality (N.Refl variable) ]
             (ImplicationElimination
                ( UniversalElimination (constant, Assume 0),
                  UniversalElimination (constant, Assume 1) ))) );
    ( "natural eigenvariable condition and rule roundtrips",
      fun () ->
        let p = predicate variable in
        let infer context proof = N.infer context proof in
        let unsafe = Option.get (infer [ p ] (UniversalIntroduction (Assume 0))) in
        let universal = Option.get (N.fol_formula_value (Pair (Number 4, N.fol_formula_code p))) in
        check (not (N.form_dec unsafe universal)) "universal introduction failed to shift context";
        let proofs =
          [
            N.Assume 0;
            ImplicationIntroduction (p, Assume 0);
            ImplicationElimination (Assume 1, Assume 0);
            UniversalIntroduction (Assume 0);
            UniversalElimination (constant, Assume 0);
            Explosion (p, Assume 0);
            Peirce (p, p);
          ]
        in
        List.iter
          (fun proof -> equal (N.proof_value (N.proof_code proof)) (Some proof) "deduction codec")
          proofs;
        check (Option.is_some (infer [] (Peirce (p, p)))) "Peirce rule";
        check
          (Option.is_some
             (infer [] (UniversalIntroduction (ImplicationIntroduction (p, Assume 0)))))
          "forall identity";
        equal (infer [ N.source_sentence Bot ] (Explosion (p, Assume 0))) (Some p) "explosion" );
    ( "natural nested binders preserve variable scope",
      fun () ->
        let signature = Signature.make ~functions:[ ("c", 0); ("f", 1) ] ~predicates:[ ("r", 2) ] in
        let c = App ("c", []) in
        let fc = App ("f", [ c ]) in
        let t =
          Theory.custom ~name:"nested" signature
            [
              ("all", All (All (Pred ("r", [ B 1; B 0 ]))));
              ("negative", Neg (Pred ("r", [ c; fc ])));
            ]
        in
        let fc = N.Fun ("f", [ constant ]) in
        let proof x y =
          certificate t
            [ source 0; source 1 ]
            (ImplicationElimination
               (Assume 1, UniversalElimination (y, UniversalElimination (x, Assume 0))))
        in
        accepts t (proof constant fc);
        rejects_proof t (proof fc constant);
        equal
          (N.instantiate (N.Var 0) (N.All (N.Atom (Some "r", [ N.Var 1; N.Var 0 ]))))
          (N.All (N.Atom (Some "r", [ N.Var 1; N.Var 0 ])))
          "free witness captured under a binder" );
    ( "natural equality symmetry transitivity and congruence",
      fun () ->
        let signature =
          Signature.make
            ~functions:[ ("c", 0); ("d", 0); ("e", 0); ("f", 1) ]
            ~predicates:[ ("p", 1) ]
        in
        let c = App ("c", []) and d = App ("d", []) and e = App ("e", []) in
        let t =
          Theory.custom ~name:"equality-chain" signature
            [
              ("dc", Eq (d, c));
              ("de", Eq (d, e));
              ("positive", Pred ("p", [ App ("f", [ c ]) ]));
              ("negative", Neg (Pred ("p", [ App ("f", [ e ]) ])));
            ]
        in
        let c = N.Fun ("c", []) and d = N.Fun ("d", []) and e = N.Fun ("e", []) in
        let fc = N.Fun ("f", [ c ]) and fe = N.Fun ("f", [ e ]) in
        let witnesses predicate =
          [
            source 0;
            source 1;
            source 2;
            source 3;
            equality (N.Sym (d, c));
            equality (N.Trans (c, d, e));
            equality (N.Function ("f", [ c ], [ e ]));
            equality (N.Predicate (predicate, [ fc ], [ fe ]));
          ]
        in
        (* Derive the translated conjunction a /\ True. The body is under one
           additional assumption, so its outer context indices are shifted. *)
        let conjunction a body =
          N.ImplicationIntroduction
            ( N.Imp (a, N.neg N.truth),
              ImplicationElimination
                (ImplicationElimination (Assume 0, body), ImplicationIntroduction (N.Bot, Assume 0))
            )
        in
        let ce offset =
          N.ImplicationElimination
            ( ImplicationElimination
                (Assume (5 + offset), ImplicationElimination (Assume (4 + offset), Assume offset)),
              Assume (1 + offset) )
        in
        let fce offset =
          N.ImplicationElimination
            (Assume (6 + offset), conjunction (standard_equal c e) (ce (offset + 1)))
        in
        let proof =
          N.ImplicationElimination
            ( Assume 3,
              ImplicationElimination
                ( ImplicationElimination (Assume 7, conjunction (standard_equal fc fe) (fce 1)),
                  Assume 2 ) )
        in
        accepts t (certificate t (witnesses "p") proof);
        rejects_proof t (certificate t (witnesses "q") proof) );
    ( "natural registered and equivalent permissions",
      fun () ->
        let open Theory in
        let schema =
          Schema.create ~name:"false-schema" ~revision:"current"
            ~encode:(fun () -> "unit")
            ~decode:(function "unit" -> Some () | _ -> None)
            ~enumerate:(fun _ _ -> List.to_seq [ () ])
            ~expand:(fun a () -> Source.falsity a)
            ~check:(fun _ () f -> f = Bot)
            ()
        in
        let t = register_schema (theory []) schema in
        let permission =
          N.EquivalentPermission
            (N.RegisteredPermission ("false-schema", "current", "unit", Bot), Conj [ Bot; Top ])
        in
        let axiom = Pair (Number 0, N.permission_code permission) in
        (* Authorization is independently checked before the deduction. *)
        check (Option.is_some (N.axiom_at (manifest t) axiom)) "registered permission";
        let bad =
          Pair
            ( Number 0,
              N.permission_code (N.RegisteredPermission ("false-schema", "current", "wrong", Bot))
            )
        in
        check (Option.is_none (N.axiom_at (manifest t) bad)) "forged registered parameter";
        accepts t
          (certificate t
             [
               Pair
                 ( Number 0,
                   N.permission_code
                     (N.RegisteredPermission ("false-schema", "current", "unit", Bot)) );
             ]
             (Assume 0)) );
    ( "certified reference finite bounds are inconclusive",
      fun () ->
        let t = theory [ Bot ] in
        equal (Natural.search t 2) None "small stage must not pretend consistency";
        check (rejects (fun () -> ignore (Natural.search t (-1)))) "negative stage accepted";
        equal
          (N.search
             (function [ 2 ] -> Some 2 | _ -> None)
             (fun budget c -> budget = 2 && c = 2)
             2)
          (Some 2) "budget and word dovetailing" );
    ( "natural pruning removes unused and duplicate premises beneath both binders",
      fun () ->
        let t = theory [ Bot; Pred ("p", [ App ("c", []) ]) ] in
        let c =
          certificate t
            [ source 1; source 0; source 0 ]
            (UniversalElimination
               ( constant,
                 UniversalIntroduction
                   (ImplicationElimination (ImplicationIntroduction (N.Bot, Assume 3), Assume 1)) ))
        in
        accepts t c;
        let pruned = Proof.prune c in
        accepts t pruned;
        equal
          (Natural.statistics (Option.get pruned.natural))
          (6, 1) "pruning changed deduction nodes or failed to merge witnesses";
        equal (Proof.prune pruned) pruned "pruning is not idempotent";
        let small = minimize t c in
        accepts t small;
        equal (Natural.statistics (Option.get small.natural)) (1, 1) "Bottom shortcut missing" );
    ( "natural implication beta reduction is checked and portable",
      fun () ->
        let t, c = redundant_fixture () in
        accepts t c;
        let small = minimize t c in
        accepts t small;
        equal (Natural.statistics (Option.get small.natural)) (3, 2) "implication detour survived";
        equal small (minimize t small) "reduction not at a fixed point";
        accepts t (Certificate_io.decode (Certificate_io.encode small));
        equal
          (List.length (Natural.premises t (Option.get small.natural)))
          2 "Source export retained an unused premise" );
    ( "natural universal beta reduction handles nested eigenvariables",
      fun () ->
        let t = theory [ All (Pred ("p", [ B 0 ])); Neg (Pred ("p", [ App ("c", []) ])) ] in
        let general =
          N.UniversalIntroduction (UniversalIntroduction (UniversalElimination (N.Var 1, Assume 0)))
        in
        let instance =
          N.UniversalElimination (constant, UniversalElimination (constant, general))
        in
        let c =
          certificate t [ source 0; source 1 ] (ImplicationElimination (Assume 1, instance))
        in
        accepts t c;
        let small = minimize t c in
        accepts t small;
        equal (Natural.statistics (Option.get small.natural)) (4, 2) "universal detours survived" );
    ( "natural assumption substitution avoids capture across local hypotheses and quantifiers",
      fun () ->
        let p = predicate (N.Var 0) in
        let context = [ N.All p ] and argument = N.UniversalElimination (N.Var 0, Assume 0) in
        let bodies =
          [
            N.UniversalIntroduction (Assume 0);
            UniversalIntroduction (ImplicationIntroduction (p, Assume 1));
            ImplicationIntroduction (p, UniversalIntroduction (Assume 1));
            UniversalIntroduction (UniversalIntroduction (Assume 0));
          ]
        in
        List.iter
          (fun body ->
            let before = N.ImplicationElimination (ImplicationIntroduction (p, body), argument) in
            let after = Natural.substitute_assumption ~guard:(fun () -> ()) 0 argument body in
            let expected = N.infer context before in
            check (Option.is_some expected) "invalid capture test fixture";
            equal (N.infer context after) expected
              "substitution captured an eigenvariable or hypothesis")
          bodies );
    ( "natural shrinking preserves a verified result on budget expiry or rejected proposals",
      fun () ->
        let t, c = redundant_fixture () in
        let zero = { config.engine with limits = { config.engine.limits with seconds = 0. } } in
        let result = Minimizer.run ~config:zero t c in
        equal result.certificate c "zero budget modified the input";
        equal result.inconclusive 1 "budget expiry not reported";
        let code = Option.get c.natural in
        let kept, attempts, rejected =
          Natural.shrink ~guard:(fun () -> ()) ~accept:(fun _ -> false) t code
        in
        equal kept code "unverified proposal escaped";
        check (attempts > 0 && rejected = attempts) "replay rejection not counted";
        let replays = ref 0 in
        let guard () = if !replays > 0 then raise Natural.Stop in
        let accept code =
          incr replays;
          Result.is_ok (Kernel.check t { c with natural = Some code })
        in
        let kept, _, _ = Natural.shrink ~guard ~accept t code in
        accepts t { c with natural = Some kept };
        equal (snd (Natural.statistics kept)) 2 "last verified compaction was lost";
        let forged = certificate t [ source 0 ] (Assume 0) in
        check
          (rejects (fun () -> ignore (minimize t forged)))
          "invalid input was repaired into acceptance" );
    ( "natural repeated detours shrink without growing the proof",
      fun () ->
        let t, c = fixture () in
        let original = Option.get (N.certificate_value (Option.get c.natural)) in
        let rec wrap n proof =
          if n = 0 then proof
          else
            wrap (n - 1)
              (N.UniversalElimination
                 ( constant,
                   UniversalIntroduction
                     (ImplicationElimination (ImplicationIntroduction (N.Bot, Assume 0), proof)) ))
        in
        for n = 1 to 20 do
          let large = certificate t original.assumptions (wrap n original.deduction) in
          accepts t large;
          let small = minimize t large in
          accepts t small;
          equal (Natural.statistics (Option.get small.natural)) (3, 2) "nested detours remained"
        done );
  ]

let () =
  match Array.to_list Sys.argv with
  | [ _; "--export-rocq"; path ] -> (
      let t, c = fixture () in
      match Kernel.rocq_document t c with
      | Ok text -> Sexp.write_file path text
      | Error e -> failwith e)
  | [ _; "--export-shrunk-rocq"; path ] -> (
      let t, c = redundant_fixture () in
      match Kernel.rocq_document t (minimize t c) with
      | Ok text -> Sexp.write_file path text
      | Error e -> failwith e)
  | [ _; "--export-minimize"; proof; problem ] ->
      let _, c = redundant_fixture () in
      Certificate_io.write proof { c with theory = "tptp" };
      Sexp.write_file problem "fof(p,axiom,p(c)). fof(n,axiom,~p(c)).\n"
  | _ -> run tests
