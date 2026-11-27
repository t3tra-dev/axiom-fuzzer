open Wire

type t = {
  base : Signature.t;
  signature : Signature.t;
  functions : (string * (int * source_term)) list;
  predicates : (string * (int * source)) list;
}

let create base =
  if Signature.is_unrestricted base then
    invalid_arg "Definitions: an explicit finite signature is required";
  { base; signature = base; functions = []; predicates = [] }

let signature t = t.signature
let base_signature t = t.base

let rec lift visit depth t =
  visit ();
  match t with
  | B i ->
      if i > max_int - depth then invalid_arg "Definitions: variable overflow" else B (i + depth)
  | App (s, ts) -> App (s, List.map (lift visit depth) ts)
  | t -> t

(* Arguments belong to the caller's scope. Substituting beneath a binder in
   the definition must lift their bound indices; substitution is simultaneous. *)
let instantiate_term visit arguments depth =
  let rec term t =
    visit ();
    match t with
    | F i ->
        if i < 0 || i >= Array.length arguments then invalid_arg "Definitions: undeclared parameter";
        lift visit depth arguments.(i)
    | App (s, ts) -> App (s, List.map term ts)
    | t -> t
  in
  term

let instantiate_formula visit arguments body =
  let arguments = Array.of_list arguments in
  let rec formula depth f =
    visit ();
    match f with
    | Pred (s, ts) -> Pred (s, List.map (instantiate_term visit arguments depth) ts)
    | Eq (x, y) ->
        let sub = instantiate_term visit arguments depth in
        Eq (sub x, sub y)
    | Neg f -> Neg (formula depth f)
    | Conj fs -> Conj (List.map (formula depth) fs)
    | Disj fs -> Disj (List.map (formula depth) fs)
    | All f -> All (formula (depth + 1) f)
    | Ex f -> Ex (formula (depth + 1) f)
    | f -> f
  in
  formula 0 body

let expand ?(budget = 100000) t source =
  if budget < 1 || not (source_scoped source) then
    invalid_arg "Definitions: invalid scope or budget";
  let remaining = ref budget in
  let visit () =
    decr remaining;
    if !remaining < 0 then invalid_arg "Definitions: expansion budget"
  in
  let rec term = function
    | App (s, ts) -> (
        visit ();
        Signature.check_function t.signature s (List.length ts);
        let ts = List.map term ts in
        match List.assoc_opt s t.functions with
        | None -> App (s, ts)
        | Some (_, body) -> instantiate_term visit (Array.of_list ts) 0 body)
    | x ->
        visit ();
        x
  and formula = function
    | Pred (s, ts) -> (
        visit ();
        Signature.check_predicate t.signature s (List.length ts);
        let ts = List.map term ts in
        match List.assoc_opt s t.predicates with
        | None -> Pred (s, ts)
        | Some (_, body) -> instantiate_formula visit ts body)
    | Eq (x, y) ->
        visit ();
        Eq (term x, term y)
    | Neg f ->
        visit ();
        Neg (formula f)
    | Conj fs ->
        visit ();
        Conj (List.map formula fs)
    | Disj fs ->
        visit ();
        Disj (List.map formula fs)
    | All f ->
        visit ();
        All (formula f)
    | Ex f ->
        visit ();
        Ex (formula f)
    | f ->
        visit ();
        f
  in
  let result = formula source in
  if not (source_scoped result) then invalid_arg "Definitions: expansion escaped its scope";
  result

let fresh symbols name arity =
  if name = "" || arity < 0 || List.mem_assoc name symbols then
    invalid_arg "Definitions: invalid, duplicate or existing symbol"

let predicate ?budget t ~name ~arity body =
  fresh (Signature.predicates t.signature) name arity;
  if not (Source_checker.parameters_below arity body) then
    invalid_arg "Definitions: undeclared parameter";
  let body = expand ?budget t body in
  let signature =
    Signature.make ~functions:(Signature.functions t.signature)
      ~predicates:((name, arity) :: Signature.predicates t.signature)
  in
  { t with signature; predicates = (name, (arity, body)) :: t.predicates }

let function_ ?budget t ~name ~arity body =
  fresh (Signature.functions t.signature) name arity;
  if not (Source_checker.term_parameters_below arity body) then
    invalid_arg "Definitions: undeclared parameter";
  let body =
    match expand ?budget t (Eq (body, body)) with Eq (body, _) -> body | _ -> assert false
  in
  let signature =
    Signature.make
      ~functions:((name, arity) :: Signature.functions t.signature)
      ~predicates:(Signature.predicates t.signature)
  in
  { t with signature; functions = (name, (arity, body)) :: t.functions }
