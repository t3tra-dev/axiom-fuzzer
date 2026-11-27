(* The reference calculus and checker are extracted from Rocq. Native artifact
   handling and heuristic reduction stay outside that trusted checker. *)
open Wire_types
module N = Natural_checker

let certificate theory proof : Wire.certificate =
  {
    natural = Some proof;
    avatar = None;
    theory = Theory.name theory;
    cnf_mode = Hybrid;
    axioms = [];
    steps = [];
    root = 0;
  }

let validate_code ~guard code =
  let rec visit = function
    | Number n ->
        guard ();
        if n < 0 then invalid_arg "negative natural-deduction code"
    | Pair (x, y) ->
        guard ();
        visit x;
        visit y
  in
  visit code

let check ~guard theory code =
  validate_code ~guard code;
  let accepted = N.direct_check (Theory.manifest theory) code in
  guard ();
  accepted

let rec nodes ?(guard = fun () -> ()) p =
  guard ();
  let count = nodes ~guard in
  match p with
  | N.Assume _ | Peirce _ -> 1
  | ImplicationIntroduction (_, p)
  | UniversalIntroduction p
  | UniversalElimination (_, p)
  | Explosion (_, p) ->
      1 + count p
  | ImplicationElimination (p, q) -> 1 + count p + count q

let statistics code =
  match N.certificate_value code with
  | None -> (0, 0)
  | Some c -> (nodes c.deduction, List.length c.assumptions)

(* Assumption indices and object-language variables have independent binders.
   These transformations only propose proofs; the minimizer replays every
   accepted pass through the independent kernel. *)
let rec map_assumptions ~guard f depth p =
  guard ();
  let map = map_assumptions ~guard f depth in
  match p with
  | N.Assume i -> N.Assume (if i < depth then i else depth + f (i - depth))
  | ImplicationIntroduction (a, p) ->
      N.ImplicationIntroduction (a, map_assumptions ~guard f (depth + 1) p)
  | ImplicationElimination (p, q) -> N.ImplicationElimination (map p, map q)
  | UniversalIntroduction p -> N.UniversalIntroduction (map p)
  | UniversalElimination (t, p) -> N.UniversalElimination (t, map p)
  | Explosion (a, p) -> N.Explosion (a, map p)
  | Peirce _ -> p

let compact ?(guard = fun () -> ()) (c : _ N.certificate) =
  let used = Hashtbl.create 16 in
  ignore
    (map_assumptions ~guard
       (fun i ->
         Hashtbl.replace used i ();
         i)
       0 c.deduction);
  let unique = Hashtbl.create 16 and indices = Hashtbl.create 16 in
  let assumptions = ref [] and count = ref 0 in
  List.iteri
    (fun i witness ->
      guard ();
      if Hashtbl.mem used i then
        let index =
          match Hashtbl.find_opt unique witness with
          | Some j -> j
          | None ->
              let j = !count in
              incr count;
              assumptions := witness :: !assumptions;
              Hashtbl.add unique witness j;
              j
        in
        Hashtbl.add indices i index)
    c.assumptions;
  let index i =
    match Hashtbl.find_opt indices i with
    | Some j -> j
    | None -> invalid_arg "natural pruning: invalid assumption index"
  in
  { N.assumptions = List.rev !assumptions; deduction = map_assumptions ~guard index 0 c.deduction }

let prune code =
  match N.certificate_value code with
  | None -> invalid_arg "natural pruning: invalid certificate"
  | Some c -> N.certificate_code (compact c)

let rec substitute_variables ~guard rho p =
  guard ();
  let map = substitute_variables ~guard rho in
  match p with
  | N.Assume _ -> p
  | ImplicationIntroduction (a, p) -> N.ImplicationIntroduction (N.subst rho a, map p)
  | ImplicationElimination (p, q) -> N.ImplicationElimination (map p, map q)
  | UniversalIntroduction p -> N.UniversalIntroduction (substitute_variables ~guard (N.up rho) p)
  | UniversalElimination (t, p) -> N.UniversalElimination (N.subst_term rho t, map p)
  | Explosion (a, p) -> N.Explosion (N.subst rho a, map p)
  | Peirce (a, b) -> N.Peirce (N.subst rho a, N.subst rho b)

let rec substitute_assumption ~guard depth argument p =
  guard ();
  let sub = substitute_assumption ~guard depth argument in
  match p with
  | N.Assume i when i = depth -> map_assumptions ~guard (fun j -> j + depth) 0 argument
  | Assume i -> N.Assume (if i > depth then i - 1 else i)
  | ImplicationIntroduction (a, p) ->
      N.ImplicationIntroduction (a, substitute_assumption ~guard (depth + 1) argument p)
  | ImplicationElimination (p, q) -> N.ImplicationElimination (sub p, sub q)
  | UniversalIntroduction p ->
      let argument = substitute_variables ~guard (fun i -> N.Var (i + 1)) argument in
      N.UniversalIntroduction (substitute_assumption ~guard depth argument p)
  | UniversalElimination (t, p) -> N.UniversalElimination (t, sub p)
  | Explosion (a, p) -> N.Explosion (a, sub p)
  | Peirce _ -> p

exception Stop

let shrink ~guard ~accept theory code =
  let current = ref code and attempts = ref 0 and inconclusive = ref 0 in
  let decoded code =
    match N.certificate_value code with
    | Some c -> c
    | None -> invalid_arg "natural shrinking: invalid certificate"
  in
  let size c = (nodes ~guard c.N.deduction, List.length c.assumptions) in
  let rec data_size = function
    | Number n ->
        guard ();
        String.length (string_of_int n)
    | Pair (x, y) ->
        guard ();
        3 + data_size x + data_size y
  in
  let submit candidate =
    guard ();
    let candidate = compact ~guard candidate in
    let previous = decoded !current in
    let n, a = size candidate and old_n, old_a = size previous in
    if n <= old_n && a <= old_a && (n < old_n || a < old_a) then
      let code = N.certificate_code candidate in
      if data_size code > data_size !current then false
      else (
        incr attempts;
        if accept code then (
          current := code;
          true)
        else (
          incr inconclusive;
          false))
    else false
  in
  let rec reduce context p =
    guard ();
    let p =
      match p with
      | N.Assume _ | Peirce _ -> p
      | ImplicationIntroduction (a, p) -> N.ImplicationIntroduction (a, reduce (a :: context) p)
      | ImplicationElimination (p, q) ->
          N.ImplicationElimination (reduce context p, reduce context q)
      | UniversalIntroduction p -> N.UniversalIntroduction (reduce (List.map N.shift0 context) p)
      | UniversalElimination (t, p) -> N.UniversalElimination (t, reduce context p)
      | Explosion (a, p) -> N.Explosion (a, reduce context p)
    in
    let conclusion = N.infer context p in
    let best = ref p and count = ref (nodes ~guard p) in
    let offer q =
      guard ();
      let n = nodes ~guard q in
      if n < !count && N.infer context q = conclusion then (
        best := q;
        count := n)
    in
    (* Direct use of a local premise often removes a whole detour. *)
    List.iteri (fun i a -> if conclusion = Some a then offer (N.Assume i)) context;
    (match p with
    | ImplicationElimination (ImplicationIntroduction (_, body), argument) ->
        (* Substitution can duplicate the argument. Bound work before allocating
           that tree, and only keep a strict reduction. *)
        let uses = ref 0 in
        ignore
          (map_assumptions ~guard
             (fun i ->
               if i = 0 then incr uses;
               i)
             0 body);
        let body_size = nodes ~guard body and arg_size = nodes ~guard argument in
        if !uses = 0 || arg_size <= ((!count - body_size) / !uses) + 1 then
          offer (substitute_assumption ~guard 0 argument body)
    | UniversalElimination (t, UniversalIntroduction body) ->
        offer (substitute_variables ~guard (N.push t (fun i -> N.Var i)) body)
    | ImplicationIntroduction (_, ImplicationElimination (f, Assume 0)) ->
        let uses = ref false in
        ignore
          (map_assumptions ~guard
             (fun i ->
               if i = 0 then uses := true;
               i)
             0 f);
        if not !uses then offer (map_assumptions ~guard (fun i -> i - 1) 0 f)
    | _ -> ());
    (* A child with the same context can already prove the conclusion (in
       particular Bottom); never discard an introduction's context change. *)
    (match p with
    | ImplicationElimination (p, q) ->
        offer p;
        offer q
    | UniversalElimination (_, p) | Explosion (_, p) -> offer p
    | _ -> ());
    !best
  in
  (try
     ignore (submit (decoded !current));
     let progress = ref true in
     while !progress do
       guard ();
       let c = decoded !current in
       let context =
         match N.context_at (N.axiom_at (Theory.manifest theory)) c.assumptions with
         | Some context -> context
         | None -> invalid_arg "natural shrinking: unauthorized premise"
       in
       progress := submit { c with deduction = reduce context c.deduction }
     done
   with Stop -> incr inconclusive);
  (!current, !attempts, !inconclusive)

let search theory stage =
  if stage < 0 then invalid_arg "negative reference stage";
  if stage = max_int then invalid_arg "reference machine integer limit";
  Option.map (certificate theory) (N.reference_run (Theory.manifest theory) stage)

let finite_premises theory code =
  let manifest = Theory.manifest theory in
  let c =
    match N.certificate_value code with Some c -> c | None -> invalid_arg "invalid natural proof"
  in
  (* Export the actual finite Source premises. Arbitrary registered callbacks
     are not serialized or claimed to have been proved by Rocq. *)
  let axioms = ref [] in
  let assumptions =
    List.map
      (function
        | Pair (Number 0, p) ->
            let formula =
              match N.permission_value p with
              | Some p -> (
                  match N.authorize manifest p with
                  | Some f -> f
                  | None -> invalid_arg "unauthorized Source premise")
              | None -> invalid_arg "invalid Source permission"
            in
            let id = List.length !axioms in
            let name = "source_" ^ string_of_int id in
            axioms := { axiom_id = id; name; origin = Fixed name; formula } :: !axioms;
            Pair (Number 0, N.permission_code (FixedPermission id))
        | w -> w)
      c.assumptions
  in
  let fixed_axioms = List.rev !axioms in
  let finite =
    {
      manifest with
      Source_checker.fixed_axioms;
      allowed_schemas = [];
      registered_check = (fun _ _ _ _ -> false);
    }
  in
  let proof = N.certificate_code { c with assumptions } in
  if not (N.direct_check finite proof) then invalid_arg "natural Source export replay failed";
  (finite, proof)

let premises theory code = (fst (finite_premises theory code)).Source_checker.fixed_axioms

let document theory code =
  let finite, proof = finite_premises theory code in
  let fixed_axioms = finite.Source_checker.fixed_axioms in
  let list f xs = List.fold_right (fun x rest -> "(cons " ^ f x ^ " " ^ rest ^ ")") xs "nil" in
  let app f xs = "(" ^ f ^ " " ^ String.concat " " xs ^ ")" in
  let nat = string_of_int in
  let string s =
    app "bytes" [ list (fun c -> nat (Char.code c)) (List.of_seq (String.to_seq s)) ]
  in
  let rec term = function
    | B i -> app "L.SBound" [ nat i ]
    | F i -> app "L.SFree" [ nat i ]
    | App (f, ts) -> app "L.SApply" [ string f; list term ts ]
  in
  let rec source = function
    | Top -> "L.STop"
    | Bot -> "L.SBot"
    | Pred (p, ts) -> app "L.SPred" [ string p; list term ts ]
    | Eq (x, y) -> app "L.SEq" [ term x; term y ]
    | Neg f -> app "L.SNeg" [ source f ]
    | Conj fs -> app "L.SConj" [ list source fs ]
    | Disj fs -> app "L.SDisj" [ list source fs ]
    | All f -> app "L.SAll" [ source f ]
    | Ex f -> app "L.SEx" [ source f ]
  in
  let axiom a =
    Printf.sprintf
      "{| V.axiom_id := %d; V.axiom_name := %s; V.axiom_origin := V.FixedAxiom %s; V.axiom_formula \
       := %s |}"
      a.axiom_id (string a.name) (string a.name) (source a.formula)
  in
  let rec data = function
    | Number n -> app "E.Number" [ nat n ]
    | Pair (x, y) -> app "E.Pair" [ data x; data y ]
  in
  let symbols = list (fun (s, n) -> "(" ^ string s ^ ", " ^ nat n ^ ")") in
  "(* Refutation from the displayed finite Source premises. Their authorization\n\
   against the original manifest was checked before export. *)\n\
   From Stdlib Require Import List String Ascii.\n\
   Require Import AxiomFuzzer.Source.Standard AxiomFuzzer.Source.Validation\n\
   AxiomFuzzer.Reference.Encoding AxiomFuzzer.Reference.Certificate.\n\
   Import ListNotations.\n\
   Module L := AxiomFuzzer.Source.Language.\n\
   Module V := AxiomFuzzer.Source.Validation.\n\
   Module E := AxiomFuzzer.Reference.Encoding.\n\
   Definition bytes (xs : list nat) : string :=\n\
   fold_right (fun n s => String (Ascii.ascii_of_nat n) s) EmptyString xs.\n\
   Definition source_manifest : V.theory := {| V.theory_name := " ^ string finite.theory_name
  ^ "; V.unrestricted_signature := "
  ^ string_of_bool finite.unrestricted_signature
  ^ "; V.function_symbols := " ^ symbols finite.function_symbols ^ "; V.predicate_symbols := "
  ^ symbols finite.predicate_symbols ^ "; V.fixed_axioms := " ^ list axiom fixed_axioms
  ^ "; V.allowed_schemas := []; V.registered_check := fun _ _ _ _ => false |}.\n\
     Definition proof := " ^ data proof
  ^ ".\n\
     Lemma accepted : direct_check source_manifest proof = true.\n\
     Proof. vm_compute. reflexivity. Qed.\n\
     Theorem source_refutation :\n\
     (Standard.source_theory source_manifest) ⊢T Bot.\n\
     Proof. apply (@direct_sound source_manifest proof), accepted. Qed.\n\
     Print Assumptions source_refutation.\n"
