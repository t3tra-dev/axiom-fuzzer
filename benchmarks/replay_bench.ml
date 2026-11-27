(* A valid, deliberately long equality proof isolates replay from search.
   Repeated rewrites alternate P(a) and P(b); the final resolution uses ~P(a). *)
open Axiom_fuzzer
open Wire

let fixture rewrites =
  let a = App ("a", []) and b = App ("b", []) in
  let theory =
    Theory.custom ~name:"replay-bench"
      (Signature.make ~functions:[ ("a", 0); ("b", 0) ] ~predicates:[ ("p", 1) ])
      [
        ("equality", Eq (a, b));
        ("positive", Pred ("p", [ a ]));
        ("negative", Neg (Pred ("p", [ a ])));
      ]
  in
  let axioms = Theory.fixed theory in
  let inputs =
    List.map (fun ax -> (ax.axiom_id, Kernel.input_clauses ~mode:Distributive ax)) axioms
  in
  let initial =
    List.mapi
      (fun id (axiom, clauses) -> { id; clause = List.hd clauses; rule = Input (axiom, 0) })
      inputs
  in
  let literal name = { positive = true; atom = P ("p", [ Fn (Original name, []) ]) } in
  let steps = ref (List.rev initial) and previous = ref 1 in
  for i = 0 to rewrites - 1 do
    let id = i + 3 and reverse = i mod 2 = 1 in
    steps :=
      {
        id;
        clause = [ literal (if reverse then "a" else "b") ];
        rule = Paramodulate (0, 0, reverse, !previous, 0, [ 0 ], []);
      }
      :: !steps;
    previous := id
  done;
  let root = rewrites + 3 in
  let final = { id = root; clause = []; rule = Resolve (!previous, 0, 2, 0, []) } in
  ( theory,
    {
      natural = None;
      avatar = None;
      cnf_mode = Distributive;
      theory = Theory.name theory;
      axioms;
      steps = List.rev (final :: !steps);
      root;
    } )

let cnf_fixture width variables =
  let signature =
    Signature.make
      ~functions:[ ("a", 0) ]
      ~predicates:(List.init width (fun i -> ("p" ^ string_of_int i, variables)))
  in
  let arguments = List.init variables (fun i -> F i) in
  let formula = Conj (List.init width (fun i -> Pred ("p" ^ string_of_int i, arguments))) in
  let theory =
    Theory.custom ~name:"replay-bench" signature
      [
        ("wide", formula);
        ("negative", Neg (Pred ("p0", List.init variables (fun _ -> App ("a", [])))));
      ]
  in
  let engine =
    Engine.create
      {
        Engine.default_config with
        cnf_mode = Definitional;
        limits = { Engine.attempt_limits with seconds = 30.; max_given = 20; max_retained = 100000 };
        budget = Engine.no_budget;
      }
  in
  List.iter (Engine.add_axiom engine) (Theory.fixed theory);
  Engine.finish engine;
  (theory, Option.get (Engine.certificate engine ~theory:(Theory.name theory)))

(* A valid AVATAR refutation of [levels] chained splits. Level i splits
   ~r_i | p_i(X) | q_i(Y) into three components; each of p_i and q_i yields r_(i+1)
   with ~p_i(a) | r_(i+1), ~q_i(a) | r_(i+1), and a conflict with ~r_(i+1). The
   Boolean part resolves the splits from r_0 to the split of ~r_n. Steps grow
   linearly in [levels]; every dependency set has at most two components. *)
let avatar_chain levels =
  let a = App ("a", []) in
  let r i = Pred ("r" ^ string_of_int i, [])
  and p i x = Pred ("p" ^ string_of_int i, [ x ])
  and q i x = Pred ("q" ^ string_of_int i, [ x ]) in
  let signature =
    Signature.make
      ~functions:[ ("a", 0) ]
      ~predicates:
        (List.init (levels + 1) (fun i -> ("r" ^ string_of_int i, 0))
        @ List.concat
            (List.init levels (fun i -> [ ("p" ^ string_of_int i, 1); ("q" ^ string_of_int i, 1) ]))
        )
  in
  let formulas =
    [ ("start", r 0) ]
    @ List.concat
        (List.init levels (fun i ->
             [
               ("split" ^ string_of_int i, All (All (Disj [ Neg (r i); p i (B 1); q i (B 0) ])));
               ("p" ^ string_of_int i, Disj [ Neg (p i a); r (i + 1) ]);
               ("q" ^ string_of_int i, Disj [ Neg (q i a); r (i + 1) ]);
             ]))
    @ [ ("goal", Neg (r levels)) ]
  in
  let theory = Theory.custom ~name:"replay-bench-avatar" signature formulas in
  let axioms = Theory.fixed theory in
  let inputs =
    List.map (fun (ax : axiom) -> (ax.axiom_id, Kernel.input_clauses ~mode:Distributive ax)) axioms
  in
  let lit positive name args = { positive; atom = P (name, args) } in
  let x = V (0, 0) and y = V (0, 1) and ca = Fn (Original "a", []) in
  (* Components: ~r_i (0..levels), p_i(X), q_i(Y) (levels each). *)
  let kr i = i and kp i = levels + 1 + i and kq i = (2 * levels) + 1 + i in
  let components =
    List.init (levels + 1) (fun i -> [ lit false ("r" ^ string_of_int i) [] ])
    @ List.init levels (fun i -> [ lit true ("p" ^ string_of_int i) [ x ] ])
    @ List.init levels (fun i -> [ lit true ("q" ^ string_of_int i) [ y ] ])
  in
  let steps = ref [] and next = ref 0 and table = Hashtbl.create 1024 in
  let add rule =
    let clause =
      match rule with
      | Component k -> Kernel.normalize (List.nth components k)
      | _ -> (
          match
            Kernel.derive ~inputs ~steps:(List.map (Hashtbl.find table) (parents rule)) rule
          with
          | Ok c -> c
          | Error e -> failwith e)
    in
    let id = !next in
    incr next;
    let step = { id; clause; rule } in
    Hashtbl.replace table id step;
    steps := step :: !steps;
    (id, clause)
  in
  let input name =
    let ax = List.find (fun (ax : axiom) -> ax.name = name) axioms in
    add (Input (ax.axiom_id, 0))
  in
  let index_of name positive clause =
    let rec go i = function
      | [] -> failwith ("missing literal " ^ name)
      | l :: rest -> (
          match l.atom with
          | P (n, _) when n = name && l.positive = positive -> i
          | _ -> go (i + 1) rest)
    in
    go 0 clause
  in
  let start, _ = input "start" in
  let component k = add (Component k) in
  let conflicts = Hashtbl.create 16 and splits = ref [] in
  let kr0, _ = component (kr 0) in
  let empty0, _ = add (Resolve (start, 0, kr0, 0, [])) in
  Hashtbl.replace conflicts "r0" empty0;
  for i = 0 to levels - 1 do
    let s = string_of_int i in
    let split, _ = input ("split" ^ s) in
    splits := (split, [ kr i; kp i; kq i ]) :: !splits;
    let next_r, _ = component (kr (i + 1)) in
    List.iter
      (fun (name, k) ->
        let c, _ = component k in
        let side, side_clause = input name in
        let derived, _ =
          add (Resolve (c, 0, side, index_of name false side_clause, [ ((1, 0), ca) ]))
        in
        let empty, _ = add (Resolve (derived, 0, next_r, 0, [])) in
        Hashtbl.replace conflicts name empty)
      [ ("p" ^ s, kp i); ("q" ^ s, kq i) ]
  done;
  let goal, _ = input "goal" in
  splits := (goal, [ kr levels ]) :: !splits;
  let splits = List.rev !splits in
  let booleans = ref [] and bid = ref 0 in
  let boolean clause rule =
    let id = !bid in
    incr bid;
    booleans := { boolean_id = id; boolean_clause = clause; boolean_rule = rule } :: !booleans;
    id
  in
  let pos k = k + 1 and neg k = -(k + 1) in
  let previous = ref (boolean [ neg (kr 0) ] (Conflict (Hashtbl.find conflicts "r0"))) in
  for i = 0 to levels - 1 do
    let s = string_of_int i in
    let split = boolean [ pos (kr i); pos (kp i); pos (kq i) ] (Split i) in
    let t = boolean [ pos (kp i); pos (kq i) ] (Boolean_resolve (split, kr i, !previous)) in
    let cp =
      boolean [ neg (kp i); neg (kr (i + 1)) ] (Conflict (Hashtbl.find conflicts ("p" ^ s)))
    in
    let u = boolean [ pos (kq i); neg (kr (i + 1)) ] (Boolean_resolve (t, kp i, cp)) in
    let cq =
      boolean [ neg (kq i); neg (kr (i + 1)) ] (Conflict (Hashtbl.find conflicts ("q" ^ s)))
    in
    previous := boolean [ neg (kr (i + 1)) ] (Boolean_resolve (u, kq i, cq))
  done;
  let last = boolean [ pos (kr levels) ] (Split levels) in
  let root = boolean [] (Boolean_resolve (last, kr levels, !previous)) in
  ( theory,
    {
      natural = None;
      avatar = Some { components; splits; boolean_steps = List.rev !booleans; boolean_root = root };
      cnf_mode = Distributive;
      theory = Theory.name theory;
      axioms;
      steps = List.rev !steps;
      root = 0;
    } )

(* [rounds] repetitions of one AVATAR refutation over a fixed theory: the split of
   p(X) | q(Y), for each component a chain of [rewrites] (even) paramodulations with a = b
   carrying the component as its dependency, a conflict with ~p(a) or ~q(a), and the
   Boolean resolution of the split with both conflicts. Every round ends in an empty
   Boolean clause; the theory does not grow with the proof. *)
let avatar_rounds rounds rewrites =
  let a = App ("a", []) and b = App ("b", []) in
  let p x = Pred ("p", [ x ]) and q x = Pred ("q", [ x ]) in
  let signature =
    Signature.make ~functions:[ ("a", 0); ("b", 0) ] ~predicates:[ ("p", 1); ("q", 1) ]
  in
  let formulas =
    [
      ("split", All (All (Disj [ p (B 1); q (B 0) ])));
      ("equality", Eq (a, b));
      ("not-p", Neg (p a));
      ("not-q", Neg (q a));
    ]
  in
  let theory = Theory.custom ~name:"replay-bench-avatar-rounds" signature formulas in
  let axioms = Theory.fixed theory in
  let inputs =
    List.map (fun (ax : axiom) -> (ax.axiom_id, Kernel.input_clauses ~mode:Distributive ax)) axioms
  in
  let components =
    [
      [ { positive = true; atom = P ("p", [ V (0, 0) ]) } ];
      [ { positive = true; atom = P ("q", [ V (0, 1) ]) } ];
    ]
  in
  let steps = ref [] and next = ref 0 and table = Hashtbl.create 1024 in
  let add rule =
    let clause =
      match rule with
      | Component k -> Kernel.normalize (List.nth components k)
      | _ -> (
          match
            Kernel.derive ~inputs ~steps:(List.map (Hashtbl.find table) (parents rule)) rule
          with
          | Ok c -> c
          | Error e -> failwith e)
    in
    let id = !next in
    incr next;
    let step = { id; clause; rule } in
    Hashtbl.replace table id step;
    steps := step :: !steps;
    id
  in
  let input name =
    let ax = List.find (fun (ax : axiom) -> ax.name = name) axioms in
    add (Input (ax.axiom_id, 0))
  in
  let split = input "split" and equality = input "equality" in
  let not_p = input "not-p" and not_q = input "not-q" in
  let ca = Fn (Original "a", []) in
  let booleans = ref [] and bid = ref 0 in
  let boolean clause rule =
    let id = !bid in
    incr bid;
    booleans := { boolean_id = id; boolean_clause = clause; boolean_rule = rule } :: !booleans;
    id
  in
  let root = ref 0 in
  for _ = 1 to rounds do
    let refute k side =
      let c = add (Component k) in
      (* p(X) -> p(b) by a = b at X := a, then back and forth between b and a. *)
      let current =
        ref
          (if rewrites = 0 then c
           else add (Paramodulate (equality, 0, false, c, 0, [ 0 ], [ ((2, 0), ca) ])))
      in
      for r = 1 to rewrites - 1 do
        current := add (Paramodulate (equality, 0, r mod 2 = 1, !current, 0, [ 0 ], []))
      done;
      let sigma = if rewrites = 0 then [ ((1, 0), ca) ] else [] in
      add (Resolve (!current, 0, side, 0, sigma))
    in
    let empty_p = refute 0 not_p and empty_q = refute 1 not_q in
    let s = boolean [ 1; 2 ] (Split 0) in
    let cp = boolean [ -1 ] (Conflict empty_p) in
    let t = boolean [ 2 ] (Boolean_resolve (s, 0, cp)) in
    let cq = boolean [ -2 ] (Conflict empty_q) in
    root := boolean [] (Boolean_resolve (t, 1, cq))
  done;
  ( theory,
    {
      natural = None;
      avatar =
        Some
          {
            components;
            splits = [ (split, [ 0; 1 ]) ];
            boolean_steps = List.rev !booleans;
            boolean_root = !root;
          };
      cnf_mode = Distributive;
      theory = Theory.name theory;
      axioms;
      steps = List.rev !steps;
      root = 0;
    } )

(* One split of p_0(X_0) | ... | p_(width-1)(X_(width-1)) into [width] components, each
   refuted by ~p_j(a). The Boolean part removes one literal at a time from the split
   clause, so its claimed clauses have width-1, ..., 0 literals. With [deep], a further
   chain resolves ~p_0(a) | ... | ~p_(width-1)(a) with every component in turn, so its
   dependency sets grow to all [width] components, and ends in one more conflict. *)
let avatar_wide ?(deep = false) width =
  let a = App ("a", []) and p j x = Pred ("p" ^ string_of_int j, [ x ]) in
  let signature =
    Signature.make
      ~functions:[ ("a", 0) ]
      ~predicates:(List.init width (fun j -> ("p" ^ string_of_int j, 1)))
  in
  let rec quantify k body = if k = 0 then body else All (quantify (k - 1) body) in
  let wide = quantify width (Disj (List.init width (fun j -> p j (B j)))) in
  let formulas =
    (("wide", wide) :: List.init width (fun j -> ("not" ^ string_of_int j, Neg (p j a))))
    @ if deep then [ ("all-not", Disj (List.init width (fun j -> Neg (p j a)))) ] else []
  in
  let theory = Theory.custom ~name:"replay-bench-avatar-wide" signature formulas in
  let axioms = Theory.fixed theory in
  let inputs =
    List.map (fun (ax : axiom) -> (ax.axiom_id, Kernel.input_clauses ~mode:Distributive ax)) axioms
  in
  let components =
    List.init width (fun j ->
        [ { positive = true; atom = P ("p" ^ string_of_int j, [ V (0, j) ]) } ])
  in
  let steps = ref [] and next = ref 0 and table = Hashtbl.create 1024 in
  let add rule =
    let clause =
      match rule with
      | Component k -> Kernel.normalize (List.nth components k)
      | _ -> (
          match
            Kernel.derive ~inputs ~steps:(List.map (Hashtbl.find table) (parents rule)) rule
          with
          | Ok c -> c
          | Error e -> failwith e)
    in
    let id = !next in
    incr next;
    let step = { id; clause; rule } in
    Hashtbl.replace table id step;
    steps := step :: !steps;
    (id, clause)
  in
  let input name =
    let ax = List.find (fun (ax : axiom) -> ax.name = name) axioms in
    add (Input (ax.axiom_id, 0))
  in
  let split, _ = input "wide" in
  let conflicts =
    List.init width (fun j ->
        let c, _ = add (Component j) in
        let side, _ = input ("not" ^ string_of_int j) in
        fst (add (Resolve (c, 0, side, 0, [ ((1, 0), Fn (Original "a", [])) ]))))
  in
  let booleans = ref [] and bid = ref 0 in
  let boolean clause rule =
    let id = !bid in
    incr bid;
    booleans := { boolean_id = id; boolean_clause = clause; boolean_rule = rule } :: !booleans;
    id
  in
  let deep_empty =
    if not deep then None
    else
      let all_not, all_clause = input "all-not" in
      let index_of name clause =
        let rec go i = function
          | [] -> failwith ("missing literal " ^ name)
          | l :: rest -> ( match l.atom with P (n, _) when n = name -> i | _ -> go (i + 1) rest)
        in
        go 0 clause
      in
      let current = ref (all_not, all_clause) in
      for j = 0 to width - 1 do
        let c, _ = add (Component j) in
        let id, clause = !current in
        current :=
          add
            (Resolve
               ( c,
                 0,
                 id,
                 index_of ("p" ^ string_of_int j) clause,
                 [ ((1, 0), Fn (Original "a", [])) ] ))
      done;
      Some (fst !current)
  in
  let current = ref (boolean (List.init width (fun j -> j + 1)) (Split 0)) in
  List.iteri
    (fun j empty ->
      let unit = boolean [ -(j + 1) ] (Conflict empty) in
      current :=
        boolean
          (List.init (width - j - 1) (fun k -> j + k + 2))
          (Boolean_resolve (!current, j, unit)))
    conflicts;
  Option.iter
    (fun empty -> ignore (boolean (List.init width (fun j -> -(j + 1))) (Conflict empty)))
    deep_empty;
  ( theory,
    {
      natural = None;
      avatar =
        Some
          {
            components;
            splits = [ (split, List.init width Fun.id) ];
            boolean_steps = List.rev !booleans;
            boolean_root = !current;
          };
      cnf_mode = Distributive;
      theory = Theory.name theory;
      axioms;
      steps = List.rev !steps;
      root = 0;
    } )

let () =
  let rewrites = ref 512 and runs = ref 7 and width = ref 0 and variables = ref 0 in
  let levels = ref 0 and wide = ref 0 and rounds = ref 0 and round_rewrites = ref 0 in
  let deep = ref false in
  Arg.parse
    [
      ("--rewrites", Arg.Set_int rewrites, "N Even number of equality rewrites");
      ("--runs", Arg.Set_int runs, "N Measured repetitions");
      ("--cnf-width", Arg.Set_int width, "N Definitional CNF width (0: equality proof)");
      ("--variables", Arg.Set_int variables, "N Variables per CNF atom");
      ("--avatar-levels", Arg.Set_int levels, "N AVATAR proof of N chained splits");
      ("--avatar-width", Arg.Set_int wide, "N AVATAR proof of one split into N components");
      ("--avatar-deep", Arg.Set deep, " With --avatar-width, a chain whose dependencies grow to N");
      ("--avatar-rounds", Arg.Set_int rounds, "N AVATAR proof of N rounds over a fixed theory");
      ( "--round-rewrites",
        Arg.Set_int round_rewrites,
        "N Even number of rewrites per component in each round" );
    ]
    (fun _ -> raise (Arg.Bad "unexpected argument"))
    "replay_bench";
  if !rewrites < 0 || !rewrites mod 2 <> 0 || !rewrites > max_int - 4 || !runs < 1 then
    invalid_arg "rewrites must be a nonnegative even number; runs must be positive";
  if !width < 0 || !variables < 0 || !levels < 0 || !wide < 0 || !rounds < 0 || !round_rewrites < 0
  then invalid_arg "negative size";
  if !round_rewrites mod 2 <> 0 then invalid_arg "round rewrites must be even";
  let theory, certificate =
    if !rounds > 0 then avatar_rounds !rounds !round_rewrites
    else if !levels > 0 then avatar_chain !levels
    else if !wide > 0 then avatar_wide ~deep:!deep !wide
    else if !width = 0 then fixture !rewrites
    else cnf_fixture !width !variables
  in
  let replay () =
    match Kernel.check theory certificate with Ok _ -> () | Error error -> failwith error
  in
  replay ();
  let proof_steps =
    List.length certificate.steps
    + match certificate.avatar with None -> 0 | Some a -> List.length a.boolean_steps
  in
  print_endline
    "run,rewrites,cnf_width,variables,avatar_levels,avatar_width,avatar_rounds,proof_steps,seconds,allocated_words";
  for run = 0 to !runs - 1 do
    Gc.full_major ();
    let allocated = Telemetry.allocated_words () and started = Telemetry.now () in
    replay ();
    let seconds = Telemetry.now () -. started
    and allocated = Telemetry.allocated_words () -. allocated in
    let equality = !width = 0 && !levels = 0 && !wide = 0 && !rounds = 0 in
    Printf.printf "%d,%d,%d,%d,%d,%d,%d,%d,%.9f,%.0f\n%!" run
      (if equality then !rewrites else if !rounds > 0 then !round_rewrites else 0)
      !width
      (if !width = 0 then 0 else !variables)
      !levels !wide !rounds proof_steps seconds allocated
  done
