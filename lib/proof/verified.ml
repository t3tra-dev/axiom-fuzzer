open Wire
(** Translation to the independently extracted Rocq clause checker. It expands an IR inference into
    instantiation, a primitive inference, alpha-renaming, and checked set contraction. No theorem is
    assumed for this translation: every emitted primitive step is itself checked by [Rocq_checker].
    Original Wire inputs and their numeric encoding are checked by [Wire_checker] before accepting
    the refutation. *)

module R = Rocq_checker

type 'p predicate_repr = 'p Source_checker.wire_predicate = Named of 'p | Auxiliary of (int * int)
type predicate = string predicate_repr

module Db = struct
  type t = { mutable data : R.clause array; mutable used : int }

  let create () = { data = Array.make 64 []; used = 0 }
  let get t id = if id >= 0 && id < t.used then Some t.data.(id) else None

  let add t clause =
    if t.used = Array.length t.data then (
      let capacity = Array.length t.data in
      if capacity = Sys.max_array_length then invalid_arg "Rocq bridge: proof resource limit";
      let data = Array.make (capacity + min capacity (Sys.max_array_length - capacity)) [] in
      Array.blit t.data 0 data 0 t.used;
      t.data <- data);
    let id = t.used in
    t.data.(id) <- clause;
    t.used <- id + 1;
    id
end

type t = {
  functions : (symbol, int) Hashtbl.t;
  predicates : (predicate, int) Hashtbl.t;
  variables : (variable, int) Hashtbl.t;
  input_ids : (int * int, int) Hashtbl.t;
  inputs : R.clause list;
  input_array : R.clause array;
  components : R.clause list;
  db : Db.t;
  mutable steps : R.step list;
  wire_inputs : Wire.clause list;
  parents : (int, int * clause) Hashtbl.t;
}

let intern table key =
  match Hashtbl.find_opt table key with
  | Some n -> n
  | None ->
      let n = Hashtbl.length table in
      Hashtbl.add table key n;
      n

let rec term t = function
  | V v -> R.Var (intern t.variables v)
  | Fn (s, ts) ->
      let f = intern t.functions s in
      R.Fun (f, List.map (term t) ts)

let atom t = function
  | P (p, ts) ->
      let p = intern t.predicates (Named p) in
      R.Pred (p, List.map (term t) ts)
  | D (p, ts) ->
      let p = intern t.predicates (Auxiliary p) in
      R.Pred (p, List.map (term t) ts)
  | E (x, y) ->
      let x = term t x in
      let y = term t y in
      R.Eq0 (x, y)

let clause t c = List.map (fun l -> (l.positive, atom t l.atom)) c

let create ?(components = []) inputs =
  let t =
    {
      functions = Hashtbl.create 32;
      predicates = Hashtbl.create 8;
      variables = Hashtbl.create 16;
      input_ids = Hashtbl.create 32;
      inputs = [];
      input_array = [||];
      components = [];
      db = Db.create ();
      steps = [];
      parents = Hashtbl.create 64;
      wire_inputs = List.concat_map snd inputs;
    }
  in
  let encoded = ref [] and next = ref 0 in
  List.iter
    (fun (a, cs) ->
      List.iteri
        (fun i c ->
          Hashtbl.add t.input_ids (a, i) !next;
          let c = clause t c in
          encoded := c :: !encoded;
          incr next)
        cs)
    inputs;
  let inputs = List.rev !encoded in
  let components = List.map (clause t) components in
  { t with inputs; components; input_array = Array.of_list (inputs @ components) }

let inputs t = t.inputs
let certificate t = List.rev t.steps

let infer t rule =
  let input id =
    if id >= 0 && id < Array.length t.input_array then Some t.input_array.(id) else None
  in
  R.infer_with input (Db.get t.db) rule

let append t rule conclusion =
  let id = Db.add t.db conclusion in
  t.steps <- (rule, conclusion) :: t.steps;
  id

let add t rule conclusion =
  (match infer t rule with
  | Some expected when R.included expected conclusion -> ()
  | _ ->
      invalid_arg
        ("Rocq primitive inference rejected: "
        ^
        match rule with
        | R.Input _ -> "input"
        | R.Instance _ -> "instance"
        | R.Copy _ -> "copy"
        | R.Resolve _ -> "resolve"
        | R.Equality_resolve _ -> "equality resolution"
        | R.Paramodulate _ -> "paramodulation"
        | R.Equality_factor _ -> "equality factoring"));
  append t rule conclusion

let computed t rule =
  match infer t rule with
  | Some c -> append t rule c
  | None -> invalid_arg "Rocq inference has no conclusion"

let rec term_context t target path =
  match (path, target) with
  | [], _ -> R.Hole
  | i :: rest, Fn (s, ts) ->
      let before = List.filteri (fun j _ -> j < i) ts
      and after = List.filteri (fun j _ -> j > i) ts in
      R.Under
        ( intern t.functions s,
          List.map (term t) before,
          term_context t (List.nth ts i) rest,
          List.map (term t) after )
  | _ -> invalid_arg "Rocq bridge: invalid context"

let context t l = function
  | [] -> invalid_arg "Rocq bridge: empty context"
  | i :: path ->
      let in_pred p ts =
        R.In_pred
          ( intern t.predicates p,
            List.map (term t) (List.filteri (fun j _ -> j < i) ts),
            term_context t (List.nth ts i) path,
            List.map (term t) (List.filteri (fun j _ -> j > i) ts) )
      in
      let ctx =
        match l.atom with
        | P (p, ts) -> in_pred (Named p) ts
        | D (p, ts) -> in_pred (Auxiliary p) ts
        | E (x, y) when i = 0 -> R.In_eq_left (term_context t x path, term t y)
        | E (x, y) when i = 1 -> R.In_eq_right (term t x, term_context t y path)
        | _ -> invalid_arg "Rocq bridge: invalid atom context"
      in
      (l.positive, ctx)

let map_atom f = function
  | P (p, ts) -> P (p, List.map f ts)
  | D (p, ts) -> D (p, List.map f ts)
  | E (x, y) -> E (f x, f y)

let record t (step : step) ~expected ~apply =
  let instance parent scope =
    let id, c = Hashtbl.find t.parents parent in
    let substitution =
      List.map
        (fun ((_, i) as v) -> (intern t.variables v, term t (apply (V (scope, i)))))
        (variables c)
    in
    computed t (R.Instance (id, substitution))
  in
  let id =
    match step.rule with
    | Input (a, i) -> computed t (R.Input (Hashtbl.find t.input_ids (a, i)))
    | Component id -> computed t (R.Input (Hashtbl.length t.input_ids + id))
    | Resolve (p, i, q, j, _) ->
        let p = instance p 1 in
        let q = instance q 2 in
        computed t (R.Resolve (p, i, q, j))
    | Factor (p, _, _, _) ->
        let p = instance p 1 in
        add t (R.Copy p) (clause t expected)
    | Equality_resolve (p, i, _) ->
        let p = instance p 1 in
        computed t (R.Equality_resolve (p, i))
    | Equality_factor (p, i, r, j, q, _) ->
        let p = instance p 1 in
        computed t (R.Equality_factor (p, i, r, j, q))
    | Paramodulate (p, i, reverse, q, j, path, _) ->
        let p = instance p 1 in
        let q_id = instance q 2 in
        (* The IR path was selected before substitution. Substitution preserves
         every constructor on that path, so the same context is applicable. *)
        let _, target = Hashtbl.find t.parents q in
        let rec transform = function
          | V (_, i) -> apply (V (2, i))
          | Fn (s, ts) -> Fn (s, List.map transform ts)
        in
        let literal = List.nth target j in
        let ctx = context t { literal with atom = map_atom transform literal.atom } path in
        computed t (R.Paramodulate (p, i, reverse, q_id, j, ctx))
  in
  let names = Hashtbl.create 16 and bindings = ref [] in
  let rec visit = function
    | V v ->
        if not (Hashtbl.mem names v) then (
          let index = Hashtbl.length names in
          Hashtbl.add names v index;
          bindings := (intern t.variables v, term t (V (0, index))) :: !bindings)
    | Fn (_, ts) -> List.iter visit ts
  in
  List.sort_uniq compare expected
  |> List.iter (fun l ->
      match l.atom with
      | P (_, ts) | D (_, ts) -> List.iter visit ts
      | E (x, y) ->
          visit x;
          visit y);
  let id = computed t (R.Instance (id, List.rev !bindings)) in
  let id = add t (R.Copy id) (clause t step.clause) in
  Hashtbl.add t.parents step.id (id, step.clause)

let inverse table =
  let entries = Array.make (Hashtbl.length table) None in
  Hashtbl.iter
    (fun key id ->
      if id < 0 || id >= Array.length entries then invalid_arg "Rocq bridge: invalid symbol ID";
      if entries.(id) <> None then invalid_arg "Rocq bridge: duplicate symbol ID";
      entries.(id) <- Some key)
    table;
  fun id -> if id >= 0 && id < Array.length entries then entries.(id) else None

let encoding_valid t =
  (* Freeze inverse maps before checking. No symbol is interned while the
     extracted bridge compares the original inputs with their numeric image. *)
  let functions = inverse t.functions and predicates = inverse t.predicates in
  let variable v = Option.value ~default:(-1) (Hashtbl.find_opt t.variables v) in
  Wire_checker.encoded_inputs String.equal String.equal variable functions predicates t.wire_inputs
    t.inputs

let check t = encoding_valid t && R.check t.inputs (certificate t)

module Source_kernel = Kernel_checker.Kernel (struct
  type function_name = string
  type predicate_name = string

  let leb a b = Stdlib.compare a b <= 0
  let equal a b = a = b
end)

let source_certificate ~conditional ~name prepared t =
  {
    Kernel_checker.certificate_theory = name;
    certificate_axioms = prepared;
    numeric_inputs = t.inputs;
    numeric_proof = (if conditional then [] else certificate t);
  }

let avatar_certificate t (avatar : Wire.avatar_certificate) =
  let module A = Avatar_checker in
  let base = Hashtbl.length t.input_ids in
  let extra = ref [] and next = ref t.db.used in
  let components = Array.of_list avatar.components in
  let splits =
    List.map
      (fun (p, ids) ->
        let parent, occurrence = Hashtbl.find t.parents p in
        let parts = List.map (Array.get components) ids in
        let substitution =
          Avatar_proof.split_substitution occurrence parts
          |> List.map (fun (v, value) -> (intern t.variables v, term t value))
        in
        let rule = R.Instance (parent, substitution) in
        let conclusion =
          match infer t rule with
          | Some c -> c
          | None -> invalid_arg "AVATAR: split instance failed"
        in
        let id = !next in
        incr next;
        extra := (A.Ordinary rule, conclusion) :: !extra;
        (id, ids))
      avatar.splits
  in
  let fo_steps =
    List.map
      (fun (r, c) ->
        ((match r with R.Input i when i >= base -> A.Component (i - base) | r -> A.Ordinary r), c))
      (certificate t)
    @ List.rev !extra
  in
  let parent id = fst (Hashtbl.find t.parents id) in
  let boolean_ids = Hashtbl.create 128 in
  let boolean_steps =
    List.mapi
      (fun index s ->
        let previous id = Hashtbl.find boolean_ids id in
        let r =
          match s.boolean_rule with
          | Split id -> A.Split id
          | Conflict id -> A.Conflict (parent id)
          | Boolean_resolve (p, pivot, q) -> A.Boolean_resolve (previous p, pivot, previous q)
        in
        Hashtbl.add boolean_ids s.boolean_id index;
        (r, List.map (fun l -> (l > 0, Avatar_proof.component_of_literal l)) s.boolean_clause))
      avatar.boolean_steps
  in
  {
    A.components = t.components;
    fo_steps;
    splits;
    boolean_steps;
    boolean_root = Hashtbl.find boolean_ids avatar.boolean_root;
  }

let check_theory ?avatar ~guard ~manifest ~name prepared t =
  let functions = inverse t.functions and predicates = inverse t.predicates in
  let variable v = Option.value ~default:(-1) (Hashtbl.find_opt t.variables v) in
  let visit () =
    guard ();
    true
  in
  let source = source_certificate ~conditional:(Option.is_some avatar) ~name prepared t in
  match avatar with
  | None -> Source_kernel.check visit max_int 100000 variable functions predicates manifest source
  | Some a ->
      Source_kernel.avatar_check visit max_int 100000 variable functions predicates manifest source
        (avatar_certificate t a)

let document ?avatar ?definitions ~manifest ~name prepared t =
  let nat = string_of_int in
  let list f xs = "[" ^ String.concat "; " (List.map f xs) ^ "]" in
  let pair f g (x, y) = "(" ^ f x ^ ", " ^ g y ^ ")" in
  let bool = function true -> "true" | false -> "false" in
  let rec term = function
    | R.Var i -> "(NK.Var " ^ nat i ^ ")"
    | R.Fun (f, ts) -> "(NK.Fun " ^ nat f ^ " " ^ list term ts ^ ")"
  in
  let atom = function
    | R.Pred (p, ts) -> "(NK.Pred " ^ nat p ^ " " ^ list term ts ^ ")"
    | R.Eq0 (x, y) -> "(NK.Eq " ^ term x ^ " " ^ term y ^ ")"
  in
  let literal = pair bool atom in
  let rec context = function
    | R.Hole -> "NK.Hole"
    | R.Under (f, b, c, a) ->
        "(NK.Under " ^ nat f ^ " " ^ list term b ^ " " ^ context c ^ " " ^ list term a ^ ")"
  in
  let actx = function
    | R.In_pred (p, b, c, a) ->
        "(NK.In_pred " ^ nat p ^ " " ^ list term b ^ " " ^ context c ^ " " ^ list term a ^ ")"
    | R.In_eq_left (c, t) -> "(NK.In_eq_left " ^ context c ^ " " ^ term t ^ ")"
    | R.In_eq_right (t, c) -> "(NK.In_eq_right " ^ term t ^ " " ^ context c ^ ")"
  in
  let rule = function
    | R.Input i -> "(NK.Input " ^ nat i ^ ")"
    | R.Instance (p, s) -> "(NK.Instance " ^ nat p ^ " " ^ list (pair nat term) s ^ ")"
    | R.Copy p -> "(NK.Copy " ^ nat p ^ ")"
    | R.Resolve (p, i, q, j) -> Printf.sprintf "(NK.Resolve %d %d %d %d)" p i q j
    | R.Equality_resolve (p, i) -> Printf.sprintf "(NK.Equality_resolve %d %d)" p i
    | R.Equality_factor (p, i, r, j, q) ->
        Printf.sprintf "(NK.Equality_factor %d %d %s %d %s)" p i (bool r) j (bool q)
    | R.Paramodulate (p, i, r, q, j, c) ->
        Printf.sprintf "(NK.Paramodulate %d %d %s %d %d %s)" p i (bool r) q j (pair bool actx c)
  in
  let app name args = "(" ^ name ^ " " ^ String.concat " " args ^ ")" in
  let string s =
    app "bytes" [ list (fun c -> nat (Char.code c)) (List.of_seq (String.to_seq s)) ]
  in
  let variable = pair nat nat in
  let symbol = function
    | Original s -> app "W.Original" [ string s ]
    | Skolem (a, i) -> app "W.Skolem" [ nat a; nat i ]
  in
  let rec wire_term = function
    | V v -> app "W.V" [ variable v ]
    | Fn (s, ts) -> app "W.Fn" [ symbol s; list wire_term ts ]
  in
  let wire_atom = function
    | P (p, ts) -> app "W.P" [ string p; list wire_term ts ]
    | E (x, y) -> app "W.E" [ wire_term x; wire_term y ]
    | D (id, ts) -> app "W.D" [ variable id; list wire_term ts ]
  in
  let wire_literal l =
    "{| W.positive := " ^ bool l.positive ^ "; W.atom := " ^ wire_atom l.atom ^ " |}"
  in
  let predicate = function
    | Named p -> app "W.Named" [ string p ]
    | Auxiliary id -> app "W.Auxiliary" [ variable id ]
  in
  let nodes = ref 0 and largest_index = ref 0 in
  let index i =
    largest_index := max !largest_index i;
    nat i
  in
  let rec source_term = function
    | B i ->
        incr nodes;
        app "L.SBound" [ index i ]
    | F i ->
        incr nodes;
        app "L.SFree" [ index i ]
    | App (s, ts) ->
        incr nodes;
        app "L.SApply" [ string s; list source_term ts ]
  in
  let rec source f =
    incr nodes;
    match f with
    | Top -> "L.STop"
    | Bot -> "L.SBot"
    | Pred (p, ts) -> app "L.SPred" [ string p; list source_term ts ]
    | Eq (x, y) -> app "L.SEq" [ source_term x; source_term y ]
    | Neg f -> app "L.SNeg" [ source f ]
    | Conj fs -> app "L.SConj" [ list source fs ]
    | Disj fs -> app "L.SDisj" [ list source fs ]
    | All f -> app "L.SAll" [ source f ]
    | Ex f -> app "L.SEx" [ source f ]
  in
  let schema = function
    | Comprehension -> "V.ComprehensionSchema"
    | Separation -> "V.SeparationSchema"
    | Replacement -> "V.ReplacementSchema"
    | Unrestricted_separation -> "V.UnrestrictedSchema"
    | Registered (n, r) -> app "V.RegisteredSchema" [ string n; string r ]
  in
  let origin = function
    | Fixed n -> app "V.FixedAxiom" [ string n ]
    | Imported n -> app "V.ImportedAxiom" [ string n ]
    | Instance (s, f) -> app "V.SchemaInstance" [ schema s; source f ]
    | Registered_instance (n, r, d) -> app "V.RegisteredInstance" [ string n; string r; string d ]
  in
  let axiom a =
    Printf.sprintf
      "{| V.axiom_id := %d; V.axiom_name := %s; V.axiom_origin := %s; V.axiom_formula := %s |}"
      a.axiom_id (string a.name) (origin a.origin) (source a.formula)
  in
  let definition_literal = function
    | Source_checker.DBase (p, a) -> app "N.DBase" [ bool p; wire_atom a ]
    | DAux (p, id, vs) -> app "N.DAux" [ bool p; nat id; list nat vs ]
  in
  let definition (d : _ Source_checker.definition) =
    "{| N.conjunction := " ^ bool d.conjunction ^ "; N.arguments := " ^ list nat d.arguments
    ^ "; N.children := "
    ^ list definition_literal d.children
    ^ " |}"
  in
  let prepared_axiom (a : Kernel_checker.prepared_axiom) =
    let hint =
      match a.cnf_hint with
      | DistributiveEvidence -> "SK.DistributiveEvidence"
      | DefinitionalEvidence (ds, root) ->
          app "SK.DefinitionalEvidence" [ list definition ds; definition_literal root ]
    in
    "{| SK.original_axiom := " ^ axiom a.original_axiom ^ "; SK.cnf_hint := " ^ hint ^ " |}"
  in
  let raw =
    List.concat_map
      (fun a ->
        match Kernel_checker.compile_input (fun () -> true) max_int 100000 a with
        | Some input -> input.source_clauses
        | None -> invalid_arg "Rocq export: Source reconstruction failed")
      prepared
  in
  let ranks = List.sort_uniq compare (List.concat (raw @ t.wire_inputs)) in
  let table t =
    Hashtbl.fold (fun key id xs -> (id, key) :: xs) t [] |> List.sort compare |> List.map snd
  in
  let variable_table =
    Hashtbl.fold (fun v id xs -> (v, id) :: xs) t.variables [] |> List.sort compare
  in
  let data =
    "{| SK.certificate_theory := " ^ string name ^ "; SK.certificate_axioms := "
    ^ list prepared_axiom prepared ^ "; SK.numeric_inputs := "
    ^ list (list literal) t.inputs
    ^ "; SK.numeric_proof := "
    ^ list (pair rule (list literal)) (if Option.is_some avatar then [] else certificate t)
    ^ " |}"
  in
  let avatar_text =
    match avatar with
    | None -> ""
    | Some a ->
        let a = avatar_certificate t a in
        let fo_rule = function
          | Avatar_checker.Ordinary r -> app "A.Ordinary" [ rule r ]
          | Component i -> app "A.Component" [ nat i ]
        in
        let sat_rule = function
          | Avatar_checker.Split i -> app "A.Split" [ nat i ]
          | Conflict i -> app "A.Conflict" [ nat i ]
          | Boolean_resolve (p, pivot, q) -> app "A.Boolean_resolve" [ nat p; nat pivot; nat q ]
        in
        "Definition avatar_proof : A.certificate := {| A.components := "
        ^ list (list literal) a.components
        ^ "; A.fo_steps := "
        ^ list (pair fo_rule (list literal)) a.fo_steps
        ^ "; A.splits := "
        ^ list (pair nat (list nat)) a.splits
        ^ "; A.boolean_steps := "
        ^ list (pair sat_rule (list (pair bool nat))) a.boolean_steps
        ^ "; A.boolean_root := " ^ nat a.boolean_root ^ " |}.\n"
  in
  (* A callback cannot be serialized as a Rocq proof. For registered schemas the
     independent artifact proves exactly the displayed finite Source axioms. *)
  let builtin_manifest =
    not
      (List.exists
         (function Registered _ -> true | _ -> false)
         manifest.Source_checker.allowed_schemas)
  in
  let theory_text =
    if builtin_manifest then
      "Definition theory_manifest : V.theory := {| V.theory_name := " ^ string manifest.theory_name
      ^ "; V.unrestricted_signature := "
      ^ string_of_bool manifest.unrestricted_signature
      ^ "; V.function_symbols := "
      ^ list (pair string nat) manifest.function_symbols
      ^ "; V.predicate_symbols := "
      ^ list (pair string nat) manifest.predicate_symbols
      ^ "; V.fixed_axioms := " ^ list axiom manifest.fixed_axioms ^ "; V.allowed_schemas := "
      ^ list schema manifest.allowed_schemas
      ^ "; V.registered_check := fun _ _ _ _ => false |}.\n"
    else ""
  in
  if !largest_index > max_int - !nodes - 8 then
    invalid_arg "Rocq export: source index resource limit";
  let limit = !largest_index + !nodes + 8 in
  let header =
    "(* Checked from the original Source axioms, including quantifiers and CNF. *)\n\
     From Stdlib Require Import List String Ascii.\n\
     Require Import AxiomFuzzer.Source.Kernel.\n\
     Require Import AxiomFuzzer.Source.Standard AxiomFuzzer.Clause.Avatar.\n\
     Import ListNotations.\n\
     Module NK := AxiomFuzzer.Clause.Kernel.\n\
     Module W := AxiomFuzzer.Wire.Syntax.\n\
     Module L := AxiomFuzzer.Source.Language.\n\
     Module V := AxiomFuzzer.Source.Validation.\n\
     Module N := AxiomFuzzer.Preprocess.NormalForms.\n\
     Module SK := AxiomFuzzer.Source.Kernel.\n\
     Module A := AxiomFuzzer.Clause.Avatar.\n\
     Definition bytes (xs : list nat) : string :=\n\
     fold_right (fun n s => String (Ascii.ascii_of_nat n) s) EmptyString xs.\n"
  in
  let environment =
    "Module Ranking.\nDefinition literals : list (W.wire_literal string string) := "
    ^ list wire_literal ranks
    ^ ".\n\
       End Ranking.\n\
       Module Order := SK.RankedOrder Ranking.\n\
       Module Checked := SK.Kernel Order.\n\
       Module StandardChecked := AxiomFuzzer.Source.Standard.Connection Order.\n\
       Definition visit (_ : unit) := true.\n\
       Definition variable_table : list ((nat * nat) * nat) := "
    ^ list (pair variable nat) variable_table
    ^ ".\n\
       Definition encode_variable v := match find (fun entry => \
       AxiomFuzzer.Wire.Refutation.variable_equal v (fst entry)) variable_table with\n\
       | Some entry => snd entry | None => 0 end.\n\
       Definition functions : list (W.wire_symbol string) := "
    ^ list symbol (table t.functions)
    ^ ".\nDefinition predicates : list (W.wire_predicate string) := "
    ^ list predicate (table t.predicates)
    ^ ".\n\
       Definition decode_function := @nth_error _ functions.\n\
       Definition decode_predicate := @nth_error _ predicates.\n\
       Definition proof : SK.certificate := " ^ data ^ ".\n" ^ avatar_text
    ^ Printf.sprintf "Definition limit := %d.\nDefinition budget := (1000 * 100)%%nat.\n" limit
    ^ "Definition source_axioms := map (fun a => V.axiom_formula (SK.original_axiom a)) \
       (SK.certificate_axioms proof).\n" ^ theory_text
  in
  let parameters = "visit limit budget encode_variable decode_function decode_predicate" in
  let context =
    " (D : Type) (d : D) (f : string -> list D -> D) (p : string -> list D -> Prop)\n\
     (excluded_middle : forall Q : Prop, Q \\/ ~ Q)\n\
     (functional_choice : forall R : list D -> D -> Prop,\n\
     (forall args, exists x, R args x) -> exists g, forall args, R args (g args))"
  in
  let source_theorem =
    let check, sound, suffix =
      match avatar with
      | None -> ("check_sources", "check_sources_sound", " proof")
      | Some _ -> ("avatar_check_sources", "avatar_check_sources_sound", " proof avatar_proof")
    in
    "Example proof_checked : Checked." ^ check ^ " " ^ parameters ^ suffix
    ^ " = true.\nProof. vm_compute. reflexivity. Qed.\nTheorem source_axioms_unsatisfiable"
    ^ context
    ^ " :\n\
       ~ Forall (L.source_holds f p (fun _ => d) (fun _ => d)) source_axioms.\n\
       Proof. unfold source_axioms. rewrite Forall_map. exact (Checked." ^ sound ^ " " ^ parameters
    ^ " f p d excluded_middle functional_choice" ^ suffix
    ^ " proof_checked). Qed.\nPrint Assumptions source_axioms_unsatisfiable.\n"
  in
  let theory_theorem =
    if builtin_manifest then
      let check, sound, suffix, refutation =
        match avatar with
        | None ->
            ( "check",
              "check_sound",
              " proof",
              "Theorem theory_refuted : Checked.derives_false limit encode_variable \
               decode_function decode_predicate theory_manifest.\n\
               Proof. exact (Checked.check_derives_false " ^ parameters
              ^ " theory_manifest proof kernel_checked). Qed.\n" )
        | Some _ ->
            ( "avatar_check",
              "avatar_check_sound",
              " proof avatar_proof",
              "Theorem theory_refuted : AxiomFuzzer.Logic.Deduction.tprv \
               (AxiomFuzzer.Source.Standard.source_theory theory_manifest) \
               AxiomFuzzer.Logic.Syntax.Bot.\n\
               Proof. exact (StandardChecked.avatar_check_is_standard " ^ parameters
              ^ " theory_manifest proof avatar_proof kernel_checked). Qed.\n" )
      in
      "Example kernel_checked : Checked." ^ check ^ " " ^ parameters ^ " theory_manifest" ^ suffix
      ^ " = true.\nProof. vm_compute. reflexivity. Qed.\n" ^ refutation
      ^ "Print Assumptions theory_refuted.\nTheorem theory_unsatisfiable" ^ context
      ^ " :\n~ V.theory_holds f p d theory_manifest.\nProof. exact (Checked." ^ sound ^ " "
      ^ parameters ^ " f p d excluded_middle functional_choice theory_manifest" ^ suffix
      ^ " kernel_checked). Qed.\nPrint Assumptions theory_unsatisfiable.\n"
    else ""
  in
  (* A theory made from definitions: the originals, closed in the extended language, expand to
     formulas equivalent to the source axioms, so the definitions together with the originals
     have no model either (Source.Definitions.expansions_match_sound). *)
  let definitions_theorem =
    match definitions with
    | None -> ""
    | Some (functions, predicates, originals) ->
        "Require AxiomFuzzer.Source.Definitions.\nModule DF := AxiomFuzzer.Source.Definitions.\n"
        ^ "Definition defined_functions : DF.function_definitions := "
        ^ list (pair string (pair nat source_term)) functions
        ^ ".\nDefinition defined_predicates : DF.predicate_definitions := "
        ^ list (pair string (pair nat source)) predicates
        ^ ".\nDefinition original_axioms : list (L.source_formula string string) := "
        ^ list source originals
        ^ ".\n\
           Example definitions_checked : DF.expansions_match defined_functions defined_predicates \
           original_axioms source_axioms = true.\n\
           Proof. vm_compute. reflexivity. Qed.\n\
           Theorem defined_theory_unsatisfiable" ^ context
        ^ " :\n\
           ~ (Forall (DF.satisfies f p) (DF.defining_axioms defined_functions defined_predicates)\n\
          \   /\\ Forall (DF.satisfies f p) original_axioms).\n\
           Proof. exact (DF.expansions_match_sound f p excluded_middle defined_functions \
           defined_predicates original_axioms source_axioms (fun _ => d) (fun _ => d) \
           definitions_checked (source_axioms_unsatisfiable D d f p excluded_middle \
           functional_choice)). Qed.\n\
           Print Assumptions defined_theory_unsatisfiable.\n"
  in
  header ^ environment ^ source_theorem ^ definitions_theorem ^ theory_theorem
