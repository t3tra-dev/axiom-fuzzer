open Axiom_fuzzer
open Test_support
open Wire

let bools n = List.init (1 lsl n) (fun mask -> Array.init n (fun i -> mask land (1 lsl i) <> 0))

let rec assignments choices n =
  if n = 0 then [ [] ]
  else List.concat_map (fun x -> List.map (fun xs -> x :: xs) (assignments choices (n - 1))) choices

let rec pow a n = if n = 0 then 1 else a * pow a (n - 1)
let code xs = List.fold_left (fun n x -> (2 * n) + x) 0 xs

let source_truth relation formula =
  let term env = function
    | B i -> List.nth env i
    | F _ -> failwith "free formula in semantic test"
    | App _ -> failwith "unexpected function"
  in
  let rec eval env = function
    | Top -> true
    | Bot -> false
    | Pred ("r", ts) -> relation.(code (List.map (term env) ts))
    | Pred _ -> failwith "unexpected predicate"
    | Eq (s, t) -> term env s = term env t
    | Neg f -> not (eval env f)
    | Conj fs -> List.for_all (eval env) fs
    | Disj fs -> List.exists (eval env) fs
    | All f -> List.for_all (fun x -> eval (x :: env) f) [ 0; 1 ]
    | Ex f -> List.exists (fun x -> eval (x :: env) f) [ 0; 1 ]
  in
  eval [] formula

let clause_satisfiable relation clauses =
  let functions = Hashtbl.create 8 and definitions = Hashtbl.create 8 in
  let rec gather = function
    | V _ -> ()
    | Fn (s, ts) ->
        Hashtbl.replace functions s (List.length ts);
        List.iter gather ts
  in
  List.iter
    (List.iter (fun l ->
         (match l.atom with
         | D (id, args) -> Hashtbl.replace definitions id (List.length args)
         | _ -> ());
         List.iter gather (Clause.atom_terms l.atom)))
    clauses;
  let fs = Hashtbl.fold (fun s n xs -> (s, n) :: xs) functions [] in
  let table_choices =
    List.map
      (fun (s, arity) ->
        assignments [ 0; 1 ] (pow 2 arity) |> List.map (fun values -> (s, Array.of_list values)))
      fs
  in
  let rec tables = function
    | [] -> [ [] ]
    | choices :: rest ->
        List.concat_map (fun x -> List.map (fun xs -> x :: xs) (tables rest)) choices
  in
  let predicate_choices =
    Hashtbl.fold
      (fun id arity xs -> List.map (fun values -> (id, values)) (bools (pow 2 arity)) :: xs)
      definitions []
  in
  List.exists
    (fun table ->
      List.exists
        (fun predicates ->
          List.for_all
            (fun c ->
              let vars = Wire.variables c in
              List.for_all
                (fun values ->
                  let env = List.combine vars values in
                  let rec term = function
                    | V v -> List.assoc v env
                    | Fn (s, ts) -> (List.assoc s table).(code (List.map term ts))
                  in
                  List.exists
                    (fun l ->
                      let truth =
                        match l.atom with
                        | P ("r", ts) -> relation.(code (List.map term ts))
                        | P _ -> failwith "unexpected atom"
                        | D (id, ts) -> (List.assoc id predicates).(code (List.map term ts))
                        | E (s, t) -> term s = term t
                      in
                      l.positive = truth)
                    c)
                (assignments [ 0; 1 ] (List.length vars)))
            clauses)
        (tables predicate_choices))
    (tables table_choices)

let tests =
  [
    ( "extracted Source abstraction preserves finite-model semantics",
      fun () ->
        let rng = Random.State.make [| 71943 |] in
        let arena =
          Source.create
            (Signature.make
               ~functions:[ ("a", 0); ("f", 1); ("g", 2) ]
               ~predicates:[ ("p", 2); ("q", 1) ])
        in
        let rec term depth size =
          if size = 0 then
            match Random.State.int rng (if depth = 0 then 2 else 3) with
            | 0 -> F (Random.State.int rng 3)
            | 1 -> App ("a", [])
            | _ -> B (Random.State.int rng depth)
          else
            match Random.State.int rng 3 with
            | 0 -> term depth 0
            | 1 -> App ("f", [ term depth (size - 1) ])
            | _ -> App ("g", [ term depth (size - 1); term depth (size - 1) ])
        in
        let rec formula depth size =
          if size = 0 then
            match Random.State.int rng 5 with
            | 0 -> Top
            | 1 -> Bot
            | 2 -> Pred ("p", [ term depth 2; term depth 2 ])
            | 3 -> Pred ("q", [ term depth 2 ])
            | _ -> Eq (term depth 2, term depth 2)
          else
            match Random.State.int rng 6 with
            | 0 -> formula depth 0
            | 1 -> Neg (formula depth (size - 1))
            | 2 -> Conj [ formula depth (size - 1); formula depth (size - 1) ]
            | 3 -> Disj [ formula depth (size - 1); formula depth (size - 1) ]
            | 4 -> All (formula (depth + 1) (size - 1))
            | _ -> Ex (formula (depth + 1) (size - 1))
        in
        let eval model free f =
          let rec value env = function
            | B i -> List.nth env i
            | F i -> free i
            | App ("a", []) -> model land 1
            | App ("f", [ x ]) -> value env x lxor (model land 1)
            | App ("g", [ x; y ]) -> value env x lxor value env y
            | _ -> assert false
          in
          let rec holds env = function
            | Top -> true
            | Bot -> false
            | Pred ("p", ts) -> model land (1 lsl code (List.map (value env) ts)) <> 0
            | Pred ("q", [ t ]) -> value env t = model land 1
            | Pred _ -> assert false
            | Eq (x, y) -> value env x = value env y
            | Neg f -> not (holds env f)
            | Conj fs -> List.for_all (holds env) fs
            | Disj fs -> List.exists (holds env) fs
            | All f -> List.for_all (fun x -> holds (x :: env) f) [ 0; 1 ]
            | Ex f -> List.exists (fun x -> holds (x :: env) f) [ 0; 1 ]
          in
          holds [] f
        in
        for _ = 1 to 300 do
          let raw = formula 0 3 in
          let f = Wire.import arena raw in
          check (Wire.source_scoped raw) "generated formula rejected by extracted scope checker";
          List.iter
            (fun v ->
              let all = Wire.export arena (Source.all arena [ v ] f)
              and ex = Wire.export arena (Source.ex arena [ v ] f) in
              for model = 0 to 15 do
                let free i = (model lsr i) land 1 in
                let inst x = eval model (fun i -> if i = v then x else free i) raw in
                equal (eval model free all)
                  (List.for_all inst [ 0; 1 ])
                  "universal closure captured a variable or changed a symbol";
                equal (eval model free ex)
                  (List.exists inst [ 0; 1 ])
                  "existential closure captured a variable or changed a symbol"
              done)
            [ 0; 1; 2 ]
        done );
    ( "extracted Source scope rejects hidden malformed branches",
      fun () ->
        let arena = Source.create Signature.sets in
        let good = All (Ex (Pred ("member", [ B 1; B 0 ]))) in
        check (Wire.source_scoped ~closed:true good) "closed nested formula rejected";
        let parameter = All (Pred ("member", [ B 0; F 0 ])) in
        check
          (Wire.source_scoped parameter && not (Wire.source_scoped ~closed:true parameter))
          "free parameter treated as bound";
        List.iter
          (fun bad ->
            check (not (Wire.source_scoped bad)) "invalid raw scope accepted";
            check
              (rejects (fun () -> ignore (Wire.import arena bad)))
              "simplification erased malformed input")
          [
            Pred ("member", [ B 0; F 0 ]);
            Conj [ Bot; Pred ("member", [ B max_int; F 0 ]) ];
            All (Pred ("member", [ B 1; B 0 ]));
            Conj [ Bot; Pred ("member", [ B (-1); F 0 ]) ];
            Disj [ Top; Pred ("member", [ F (-1); F 0 ]) ];
          ] );
    ( "KBO is stable under substitutions and contexts",
      fun () ->
        let rng = Random.State.make [| 88123 |] in
        let rec term depth =
          if depth = 0 then
            if Random.State.bool rng then v (Random.State.int rng 3)
            else constant (if Random.State.bool rng then "a" else "b")
          else if Random.State.bool rng then term 0
          else
            Fn
              ( Original (if Random.State.bool rng then "f" else "g"),
                [ term (depth - 1); term (depth - 1) ] )
        in
        for _ = 1 to 600 do
          let a = term 2 and b = term 2 and c = term 2 in
          check (not (Ordering.greater a a)) "KBO is reflexive";
          if Ordering.greater a b then (
            check (not (Ordering.greater b a)) "KBO is not asymmetric";
            let replacements = List.init 3 (fun _ -> term 1) in
            let subst = Clause.map_vars (fun (_, i) -> List.nth replacements i) in
            check (Ordering.greater (subst a) (subst b)) "KBO not substitution stable";
            check
              (Ordering.greater (Fn (Original "h", [ c; a ])) (Fn (Original "h", [ c; b ])))
              "KBO not context stable";
            if Ordering.greater b c then check (Ordering.greater a c) "KBO not transitive");
          List.iter
            (fun child ->
              check
                (Ordering.greater (Fn (Original "h", [ a; b ])) child)
                "KBO lacks subterm property")
            [ a; b ]
        done;
        check
          (not
             (Ordering.greater (Fn (Original "f", [ v 0; v 0 ])) (Fn (Original "g", [ v 0; v 1 ]))))
          "variable multiplicities ignored" );
    ( "LPO is a simplification order that agrees with its textbook definition",
      fun () ->
        let rng = Random.State.make [| 20261115 |] in
        let symbols = [| ("f", 1); ("g", 1); ("h", 2); ("k", 3); ("a", 0); ("b", 0); ("c", 0) |] in
        let fn name ts = Fn (Original name, ts) in
        let rec term ?(ground = false) depth =
          if depth = 0 || Random.State.int rng 4 = 0 then
            if (not ground) && Random.State.int rng 3 = 0 then v (Random.State.int rng 3)
            else
              let name, _ = symbols.(4 + Random.State.int rng 3) in
              fn name []
          else
            let name, arity = symbols.(Random.State.int rng 4) in
            fn name (List.init arity (fun _ -> term ~ground (depth - 1)))
        in
        (* Precedences: E generators (one unified precedence, and class-first), and the
           alphabetical fallback of an empty table. *)
        let clauses =
          [
            [ positive (E (fn "f" [ fn "h" [ v 0; constant "a" ] ], fn "g" [ constant "b" ])) ];
            [ negative (E (fn "k" [ v 0; v 1; constant "c" ], fn "f" [ fn "f" [ v 1 ] ])) ];
          ]
        in
        let orders =
          List.concat_map
            (fun precedence ->
              List.map
                (fun e_signature ->
                  let order = Ordering.create () in
                  ignore
                    (Eorder.install
                       {
                         Eorder.ordering = Lpo;
                         precedence;
                         weights = Unit_weights;
                         const_weight = 0;
                         e_signature;
                         e_ranks = true;
                       }
                       order clauses);
                  order)
                [ true; false ])
            [ Eorder.Invfreq_constmin; Invarity; Arity; Invfreq; Unary_first; Const_min ]
          @
          let order = Ordering.create () in
          Ordering.install_table ~kind:Lpo order (Hashtbl.create 1);
          [ order ]
        in
        List.iter
          (fun order ->
            check (Ordering.kind order = Lpo) "LPO not installed";
            let greater = Ordering.greater ~order in
            (* The definition: s > t iff t is a variable of s other than s; or some argument
               s_i >= t; or s = f(..) > g(..) = t with f > g in the precedence and s greater
               than every t_j; or f = g, the arguments are lexicographically greater, and s is
               greater than every t_j. *)
            let precedence f ss g ts =
              let head h xs = (Ordering.Function h, List.length xs) in
              Ordering.lpo_precedence order (head f ss) (head g ts)
            in
            let rec reference s t =
              match (s, t) with
              | V _, _ -> false
              | Fn _, V x -> List.mem x (Wire.variables [ positive (E (s, s)) ])
              | Fn (f, ss), Fn (g, ts) ->
                  List.exists (fun si -> si = t || reference si t) ss
                  ||
                  let c = precedence f ss g ts in
                  (c > 0 || (c = 0 && lex ss ts)) && List.for_all (reference s) ts
            and lex ss ts =
              match (ss, ts) with
              | si :: ss, ti :: ts -> if si = ti then lex ss ts else reference si ti
              | _ -> false
            in
            for _ = 1 to 400 do
              let s = term 4 and t = term 4 and u = term 3 in
              equal (greater s t) (reference s t) "LPO4 disagrees with the definition";
              check (not (greater s s)) "LPO is reflexive";
              if greater s t then (
                check (not (greater t s)) "LPO is not asymmetric";
                if greater t u then check (greater s u) "LPO is not transitive";
                let replacements = List.init 3 (fun _ -> term 2) in
                let subst = Clause.map_vars (fun (_, i) -> List.nth replacements i) in
                check (greater (subst s) (subst t)) "LPO is not stable under substitution";
                List.iter
                  (fun context ->
                    check (greater (context s) (context t)) "LPO is not compatible with contexts")
                  [
                    (fun x -> fn "f" [ x ]);
                    (fun x -> fn "h" [ u; x ]);
                    (fun x -> fn "h" [ x; u ]);
                    (fun x -> fn "k" [ u; x; u ]);
                  ]);
              List.iter
                (fun context -> check (greater (context s) s) "LPO lacks the subterm property")
                [
                  (fun x -> fn "g" [ x ]);
                  (fun x -> fn "h" [ u; x ]);
                  (fun x -> fn "k" [ fn "f" [ x ]; u; u ]);
                ];
              (* Total on ground terms. *)
              let s = term ~ground:true 4 and t = term ~ground:true 4 in
              if s <> t then
                check (greater s t <> greater t s) "LPO is not total on distinct ground terms"
            done)
          orders;
        let order = List.hd orders in
        let fx = fn "f" [ v 0 ] and k = fn "k" [ v 0; v 0; v 1 ] in
        (* Duplicating variables: KBO never orients f(h(x,x)) = k(x,x,y)-like rules, LPO can. *)
        check (Ordering.greater ~order (fn "h" [ fx; fx ]) fx) "h(f(x),f(x)) > f(x)";
        check (not (Ordering.greater ~order fx k)) "a missing variable y is never smaller";
        check
          (Ordering.greater (fn "f" [ fn "h" [ v 0; v 0 ] ]) (fn "h" [ v 0; v 0 ]))
          "the standard KBO keeps the subterm property";
        check
          (Ordering.kind Ordering.standard = Kbo && Ordering.kind (Ordering.create ()) = Kbo)
          "orders start as KBO" );
    ( "clausification preserves finite-model satisfiability",
      fun () ->
        let r x y = Pred ("r", [ x; y ]) in
        let formulas =
          [
            Ex (All (r (B 0) (B 1)));
            All (Ex (r (B 1) (B 0)));
            Neg (All (Ex (r (B 1) (B 0))));
            All (Disj [ r (B 0) (B 0); Neg (r (B 0) (B 0)) ]);
            Ex (Conj [ r (B 0) (B 0); All (r (B 0) (B 1)) ]);
            Conj [ Ex (r (B 0) (B 0)); Ex (Neg (r (B 0) (B 0))) ];
            Neg (Ex (Conj [ r (B 0) (B 0); Neg (r (B 0) (B 0)) ]));
            Top;
            Bot;
          ]
        in
        List.iteri
          (fun id formula ->
            let ax =
              { axiom_id = id; name = "finite-model"; origin = Imported "finite-model"; formula }
            in
            List.iter
              (fun mode ->
                let clauses = Clausify.run ~mode ax in
                equal clauses (Kernel.input_clauses ~mode ax) "independent CNF mismatch";
                List.iter
                  (fun relation ->
                    equal (source_truth relation formula)
                      (clause_satisfiable relation clauses)
                      "CNF changed satisfiability")
                  (bools 4))
              [ Distributive; Definitional; Hybrid ])
          formulas );
    ( "enumeration remains well-scoped and source-only",
      fun () ->
        let a = Source.create Signature.sets in
        let fs = Enumerate.exhaustive a ~arity:1 |> Seq.take 400 |> List.of_seq in
        equal (List.length fs) 400 "enumerator exhausted";
        equal (List.length (List.sort_uniq compare fs)) 400 "duplicate formulas emitted";
        List.iter
          (fun f -> check (Source.well_scoped a ~depth:0 f) "ill-scoped synthesized formula")
          fs;
        check
          (List.exists (fun f -> List.exists (( <= ) 1) (Source.free_vars a f)) fs)
          "diagonal failed to grow parameter budget";
        check
          (List.exists (fun f -> match Wire.export a f with All _ | Ex _ -> true | _ -> false) fs)
          "quantifiers never enumerated" );
    ( "functions are enumerated from the source signature",
      fun () ->
        let a =
          Source.create (Signature.make ~functions:[ ("a", 0); ("f", 1) ] ~predicates:[ ("p", 1) ])
        in
        let fs = Enumerate.bounded a ~arity:1 ~parameters:0 ~max_size:2 |> List.of_seq in
        check
          (List.exists
             (fun f ->
               match Wire.export a f with Pred ("p", [ App ("f", [ F 0 ]) ]) -> true | _ -> false)
             fs)
          "function term missing";
        let a = Source.create (Signature.make ~functions:[] ~predicates:[ ("=", 2) ]) in
        let fs = Enumerate.bounded a ~arity:1 ~parameters:0 ~max_size:1 |> List.of_seq in
        check
          (List.exists
             (fun f -> match Wire.export a f with Pred ("=", _) -> true | _ -> false)
             fs)
          "named predicate was confused with logical equality" );
    ( "two CNF implementations agree on generated formulas",
      fun () ->
        let t = Theory.create "zf" in
        let a = Theory.arena t in
        Enumerate.bounded a ~arity:2 ~parameters:0 ~max_size:2
        |> Seq.take 100
        |> Seq.iteri (fun i f ->
            List.iter
              (fun schema ->
                let ax = Theory.instantiate t ~id:(20 + i) schema f in
                List.iter
                  (fun mode ->
                    equal (Clausify.run ~mode ax) (Kernel.input_clauses ~mode ax)
                      "CNF mismatch in schema instance")
                  [ Distributive; Definitional; Hybrid ])
              [ Separation; Replacement ]) );
    ( "successful unifiers solve all input equations",
      fun () ->
        let rng = Random.State.make [| 0x51a; 0x2026 |] in
        let rec random_term depth =
          if depth = 0 then
            if Random.State.bool rng then v (Random.State.int rng 4)
            else constant (if Random.State.bool rng then "a" else "b")
          else if Random.State.bool rng then random_term 0
          else Fn (Original "f", [ random_term (depth - 1); random_term (depth - 1) ])
        in
        let u = Unify.create (Term.create ()) in
        for _ = 1 to 500 do
          let pairs = List.init 3 (fun _ -> (random_term 2, random_term 2)) in
          Unify.solve u pairs (fun _ apply ->
              List.iter
                (fun (x, y) -> equal (apply x) (apply y) "unifier does not solve equation")
                pairs);
          equal (Unify.mark u) 0 "trial leaked state"
        done );
    ( "proof mutations are rejected",
      fun () ->
        let t, c, _ = prove "naive" in
        let reject c = check (Result.is_error (Kernel.check t c)) "forged certificate accepted" in
        reject { c with root = (List.hd c.steps).id };
        reject { c with theory = "zf" };
        List.iter
          (fun target ->
            reject { c with steps = List.filter (fun (s : step) -> s.id <> target.id) c.steps };
            reject
              {
                c with
                steps =
                  List.map
                    (fun (s : step) ->
                      if s.id = target.id then
                        {
                          s with
                          clause =
                            (if s.clause = [] then [ positive (P ("member", [ v 0; v 0 ])) ] else []);
                        }
                      else s)
                    c.steps;
              })
          c.steps;
        reject { c with steps = c.steps @ [ List.hd c.steps ] };
        reject { c with axioms = List.map (fun a -> { a with formula = Bot }) c.axioms };
        reject
          {
            c with
            axioms =
              List.map
                (fun a ->
                  {
                    a with
                    origin = Instance (Comprehension, Pred ("member", [ App ("sk_0_0", []); F 0 ]));
                  })
                c.axioms;
          };
        let cyclic = [ ((1, 0), Fn (Skolem ((List.hd c.axioms).axiom_id, 0), [ V (1, 0) ])) ] in
        reject
          {
            c with
            steps =
              List.map
                (fun (s : step) ->
                  match s.rule with
                  | Factor (p, i, j, _) -> { s with rule = Factor (p, i, j, cyclic) }
                  | _ -> s)
                c.steps;
          } );
    ( "malformed binders cannot hide behind Boolean simplification",
      fun () ->
        let a = Source.create Signature.sets in
        check
          (rejects (fun () -> ignore (Wire.import a (Conj [ Bot; Pred ("member", [ B 99; F 0 ]) ]))))
          "dangling binder was simplified away" );
    ( "imported theory is checked against the external manifest",
      fun () ->
        let t = Tptp.parse "fof(p,axiom,p). fof(n,axiom,~p)." in
        let result = Scheduler.run config t in
        let c = Option.get result.certificate in
        let other = Tptp.parse "fof(p,axiom,q). fof(n,axiom,~q)." in
        check (Result.is_error (Kernel.check other c)) "certificate authorized its own inputs" );
  ]

let () = run tests
