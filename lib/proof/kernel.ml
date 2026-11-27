open Wire

type report = { steps : int; axioms : int; seconds : float }

exception Reject = Checked_clauses.Reject

let require b message = if not b then raise (Reject message)

let at xs i =
  require (i >= 0) "invalid literal/term index";
  match List.nth_opt xs i with Some x -> x | None -> raise (Reject "invalid literal/term index")

let rec change_var f = function V v -> f v | Fn (s, ts) -> Fn (s, List.map (change_var f) ts)

let change_atom f = function
  | P (s, ts) -> P (s, List.map f ts)
  | D (s, ts) -> D (s, List.map f ts)
  | E (x, y) ->
      let x = f x in
      let y = f y in
      E (x, y)

let change_lit f l = { positive = l.positive; atom = change_atom f l.atom }
let normalize = Checked_clauses.normalize
let scope s c = List.map (change_lit (change_var (fun (_, i) -> V (s, i)))) c

let without i xs =
  ignore (at xs i);
  List.filteri (fun j _ -> j <> i) xs

let atom_equal a b = a = b || match (a, b) with E (x, y), E (u, v) -> x = v && y = u | _ -> false

let substitution sigma =
  let keys = List.map fst sigma in
  require
    (List.length keys = List.length (List.sort_uniq compare keys))
    "duplicate substitution binding";
  List.iter (fun (s, i) -> require (s >= 0 && i >= 0) "negative substitution variable") keys;
  let rec apply visited = function
    | V v -> (
        require (not (List.mem v visited)) "cyclic substitution";
        match List.assoc_opt v sigma with None -> V v | Some t -> apply (v :: visited) t)
    | Fn (s, ts) -> Fn (s, List.map (apply visited) ts)
  in
  List.iter (fun (v, _) -> ignore (apply [] (V v))) sigma;
  apply []

let input_clauses = Checked_clauses.input_clauses

let rec replace_term t path replacement =
  match (path, t) with
  | [], _ -> (t, replacement)
  | i :: rest, Fn (s, args) ->
      let old, new_ = replace_term (at args i) rest replacement in
      (old, Fn (s, List.mapi (fun j t -> if i = j then new_ else t) args))
  | _ -> raise (Reject "invalid paramodulation term path")

let replace_literal l path rhs =
  let args = match l.atom with P (_, ts) | D (_, ts) -> ts | E (x, y) -> [ x; y ] in
  match path with
  | [] -> raise (Reject "empty paramodulation path")
  | i :: rest ->
      let old, new_ = replace_term (at args i) rest rhs in
      let args = List.mapi (fun j t -> if i = j then new_ else t) args in
      let atom =
        match (l.atom, args) with
        | P (s, _), ts -> P (s, ts)
        | D (s, _), ts -> D (s, ts)
        | E _, [ x; y ] -> E (x, y)
        | _ -> assert false
      in
      (old, { l with atom })

let reconstruct ?(component = fun _ -> raise (Reject "component outside AVATAR proof")) ~input
    ~parent ~apply:app rule =
  match rule with
  | Input (a, i) -> input a i
  | Component id -> component id
  | Resolve (p, i, q, j, _) ->
      let xs = List.map (change_lit app) (parent p 1)
      and ys = List.map (change_lit app) (parent q 2) in
      let l = at xs i and r = at ys j in
      require
        (l.positive <> r.positive && atom_equal l.atom r.atom)
        "resolution pivots are not complementary";
      without i xs @ without j ys
  | Factor (p, i, j, _) ->
      require (i <> j) "factoring needs distinct literals";
      let xs = List.map (change_lit app) (parent p 1) in
      let l = at xs i and r = at xs j in
      require (l.positive = r.positive && atom_equal l.atom r.atom) "invalid factoring pivots";
      without j xs
  | Equality_resolve (p, i, _) ->
      let xs = List.map (change_lit app) (parent p 1) in
      let l = at xs i in
      require
        (match (l.positive, l.atom) with false, E (s, t) -> s = t | _ -> false)
        "equality resolution requires reflexive disequality";
      without i xs
  | Equality_factor (p, i, reverse_i, j, reverse_j, _) ->
      require (i <> j) "equality factoring needs distinct literals";
      let xs = List.map (change_lit app) (parent p 1) in
      let oriented index reverse =
        match ((at xs index).positive, (at xs index).atom) with
        | true, E (s, t) -> if reverse then (t, s) else (s, t)
        | _ -> raise (Reject "equality factoring requires positive equalities")
      in
      let lhs, rhs = oriented i reverse_i and lhs', rhs' = oriented j reverse_j in
      require (lhs = lhs') "equality factoring sides do not match";
      { positive = false; atom = E (rhs, rhs') } :: at xs j :: without i xs
  | Paramodulate (p, i, reverse, q, j, path, _) ->
      let xs = parent p 1 and ys = parent q 2 in
      let eq = at xs i in
      let lhs, rhs =
        match (eq.positive, eq.atom) with
        | true, E (s, t) -> if reverse then (t, s) else (s, t)
        | _ -> raise (Reject "paramodulation source is not a positive equality")
      in
      let old, replacement = replace_literal (at ys j) path rhs in
      require (app lhs = app old) "paramodulation does not match the selected subterm";
      List.map (change_lit app)
        (without i xs @ List.mapi (fun k l -> if k = j then replacement else l) ys)

(* Reconstruct one candidate without any search data structures. This is not
   certificate acceptance: [check] also validates provenance, signatures and the
   extracted checker. Reference enumeration uses this only to build candidates. *)
let derive ~inputs ~steps rule =
  try
    let input a i =
      match List.assoc_opt a inputs with
      | Some cs -> at cs i
      | None -> raise (Reject "unknown axiom")
    in
    let parent id scope_id =
      match List.find_opt (fun (s : step) -> s.id = id) steps with
      | Some s -> scope scope_id s.clause
      | None -> raise (Reject "missing parent")
    in
    let apply = substitution (rule_substitution rule) in
    Ok (normalize (reconstruct ~input ~parent ~apply rule))
  with Reject e | Invalid_argument e -> Error e

let validate ?(guard = fun () -> ()) theory (cert : certificate) =
  let started = Telemetry.now () in
  try
    require (cert.theory = Theory.name theory) "theory manifest mismatch";
    let inputs = Hashtbl.create 32
    and symbols = Hashtbl.create 32
    and definitions = Hashtbl.create 32 in
    let prepared = ref [] in
    List.iter
      (fun (a : axiom) ->
        guard ();
        require (not (Hashtbl.mem inputs a.axiom_id)) "duplicate axiom id";
        require
          (Wire.source_scoped ~closed:true a.formula)
          "axiom is not a scoped closed source formula";
        require (Theory.validate_axiom theory a) ("invalid axiom provenance: " ^ a.name);
        let source, cs = Checked_clauses.prepare_input ~guard ~mode:cert.cnf_mode a in
        prepared := source :: !prepared;
        let rec record = function
          | V _ -> ()
          | Fn (Original _, ts) -> List.iter record ts
          | Fn ((Skolem _ as s), ts) ->
              (match Hashtbl.find_opt symbols s with
              | None -> Hashtbl.add symbols s (List.length ts)
              | Some n -> require (n = List.length ts) "inconsistent Skolem arity");
              List.iter record ts
        in
        List.iter
          (List.iter (fun l ->
               match l.atom with
               | D (id, args) ->
                   Hashtbl.replace definitions id (List.length args);
                   List.iter record args
               | P (_, args) -> List.iter record args
               | E (x, y) ->
                   record x;
                   record y))
          cs;
        Hashtbl.add inputs a.axiom_id cs)
      cert.axioms;
    let components = match cert.avatar with None -> [] | Some a -> a.components in
    let component_array = Array.of_list components in
    let verified =
      Verified.create ~components
        (List.map (fun (ax : axiom) -> (ax.axiom_id, Hashtbl.find inputs ax.axiom_id)) cert.axioms)
    in
    let signature = Source.signature (Theory.arena theory) in
    let rec valid_term = function
      | V (s, i) -> require (s >= 0 && i >= 0) "negative variable"
      | Fn (Original s, ts) ->
          Signature.check_function signature s (List.length ts);
          List.iter valid_term ts
      | Fn ((Skolem _ as s), ts) ->
          require
            (Hashtbl.find_opt symbols s = Some (List.length ts))
            "unknown Skolem symbol or arity";
          List.iter valid_term ts
    in
    let valid_clause c =
      List.iter
        (fun l ->
          match l.atom with
          | P (s, ts) ->
              Signature.check_predicate signature s (List.length ts);
              List.iter valid_term ts
          | D (id, ts) ->
              require
                (Hashtbl.find_opt definitions id = Some (List.length ts))
                "unknown definition predicate or arity";
              List.iter valid_term ts
          | E (x, y) ->
              valid_term x;
              valid_term y)
        c
    in
    List.iter
      (fun c ->
        guard ();
        valid_clause c;
        require
          (List.for_all (fun (scope, _) -> scope = 0) (variables c))
          "component contains a nonlocal variable")
      components;
    let nodes = Hashtbl.create 256 in
    let parent id scope_id current =
      require (id >= 0 && id < current) "parent is not earlier than child";
      match Hashtbl.find_opt nodes id with
      | Some c -> scope scope_id c
      | None -> raise (Reject "missing parent")
    in
    List.iter
      (fun (step : step) ->
        guard ();
        require (step.id >= 0 && not (Hashtbl.mem nodes step.id)) "duplicate/negative step id";
        valid_clause step.clause;
        let sigma = rule_substitution step.rule in
        List.iter (fun (_, t) -> valid_term t) sigma;
        let apply = substitution sigma in
        let expected =
          reconstruct
            ~component:(fun id ->
              require (Option.is_some cert.avatar) "component outside AVATAR proof";
              require (id >= 0 && id < Array.length component_array) "unknown AVATAR component";
              component_array.(id))
            ~input:(fun a i ->
              match Hashtbl.find_opt inputs a with
              | Some cs -> at cs i
              | None -> raise (Reject "unknown axiom"))
            ~parent:(fun id scope -> parent id scope step.id)
            ~apply step.rule
        in
        require
          (normalize expected = step.clause)
          (Printf.sprintf "step %d: conclusion mismatch" step.id);
        (try Verified.record verified step ~expected ~apply
         with Invalid_argument msg -> raise (Reject (Printf.sprintf "step %d: %s" step.id msg)));
        Hashtbl.add nodes step.id step.clause)
      cert.steps;
    (match cert.avatar with
    | None ->
        require (Hashtbl.find_opt nodes cert.root = Some []) "root is not a derived empty clause"
    | Some avatar ->
        require (cert.root = 0) "AVATAR certificate has a noncanonical FO root";
        ignore (Avatar_proof.validate ~guard cert.steps avatar : int -> int list));
    guard ();
    let prepared = List.rev !prepared in
    require
      (Verified.check_theory ?avatar:cert.avatar ~guard ~manifest:(Theory.manifest theory)
         ~name:cert.theory prepared verified)
      "Rocq-extracted Source kernel rejected proof";
    Ok
      ( {
          steps = fst (Proof.statistics cert);
          axioms = List.length cert.axioms;
          seconds = Telemetry.now () -. started;
        },
        (verified, prepared) )
  with
  | Reject msg | Invalid_argument msg | Failure msg -> Error msg
  | Stack_overflow -> Error "kernel recursion limit"

let check ?(guard = fun () -> ()) theory cert =
  match cert.natural with
  | None -> Result.map fst (validate ~guard theory cert)
  | Some proof -> (
      let started = Telemetry.now () in
      try
        require (cert.theory = Theory.name theory) "theory manifest mismatch";
        require
          (cert.avatar = None && cert.axioms = [] && cert.steps = [] && cert.root = 0
         && cert.cnf_mode = Hybrid)
          "mixed natural and clausal certificate";
        require (Natural.check ~guard theory proof) "Rocq natural-deduction checker rejected proof";
        let steps, axioms = Natural.statistics proof in
        Ok { steps; axioms; seconds = Telemetry.now () -. started }
      with
      | Reject msg | Invalid_argument msg | Failure msg -> Error msg
      | Stack_overflow -> Error "natural-deduction recursion limit")

let rocq_document theory cert =
  match cert.natural with
  | Some proof -> (
      match check theory cert with
      | Error e -> Error e
      | Ok _ -> (
          try Ok (Natural.document theory proof) with
          | Invalid_argument e | Failure e -> Error e
          | Stack_overflow -> Error "natural-deduction export recursion limit"))
  | None -> (
      match validate theory cert with
      | Error error -> Error error
      | Ok (_, (v, prepared)) -> (
          try
            Ok
              (Verified.document ?avatar:cert.avatar ~manifest:(Theory.manifest theory)
                 ~name:cert.theory prepared v)
          with
          | Invalid_argument error -> Error error
          | Stack_overflow -> Error "Rocq export recursion limit"))
