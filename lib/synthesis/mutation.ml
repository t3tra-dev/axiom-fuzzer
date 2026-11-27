open Wire

type change = { operator : string; path : int list; formula : source }

let rec term_size = function
  | B _ | F _ -> 1
  | App (_, ts) -> 1 + List.fold_left (fun n t -> n + term_size t) 0 ts

let rec size = function
  | Top | Bot -> 1
  | Pred (_, ts) -> 1 + List.fold_left (fun n t -> n + term_size t) 0 ts
  | Eq (x, y) -> 1 + term_size x + term_size y
  | Neg f | All f | Ex f -> 1 + size f
  | Conj fs | Disj fs -> 1 + List.fold_left (fun n f -> n + size f) 0 fs

(* Instantiate the innermost removed binder with the principal free parameter.
   Bound indices under other quantifiers are shifted down without capture. *)
let open_binder f =
  let rec term depth = function
    | B i when i = depth -> F 0
    | B i when i > depth -> B (i - 1)
    | App (s, ts) -> App (s, List.map (term depth) ts)
    | t -> t
  in
  let rec visit depth = function
    | Pred (s, ts) -> Pred (s, List.map (term depth) ts)
    | Eq (x, y) -> Eq (term depth x, term depth y)
    | Neg f -> Neg (visit depth f)
    | Conj fs -> Conj (List.map (visit depth) fs)
    | Disj fs -> Disj (List.map (visit depth) fs)
    | All f -> All (visit (depth + 1) f)
    | Ex f -> Ex (visit (depth + 1) f)
    | f -> f
  in
  visit 0 f

let replace i x xs = List.mapi (fun j y -> if i = j then x else y) xs
let remove i xs = List.filteri (fun j _ -> i <> j) xs

let rec smaller_terms = function
  | B _ | F _ -> Seq.empty
  | App (s, ts) ->
      Seq.append (List.to_seq ts)
        (List.to_seq ts
        |> Seq.mapi (fun i t -> Seq.map (fun t -> App (s, replace i t ts)) (smaller_terms t))
        |> Seq.concat)

let candidates ~shrinking ~closed formula =
  if not (source_scoped ~closed formula) then invalid_arg "Mutation: invalid source scope";
  let rec walk path f () =
    let local =
      Seq.append
        (List.to_seq
           (if shrinking then [ ("constant", Top); ("constant", Bot) ]
            else [ ("negation", match f with Neg g -> g | _ -> Neg f) ]))
        (match f with
        | Neg g -> Seq.return ("drop-negation", g)
        | All g -> List.to_seq [ ("quantifier", Ex g); ("instantiate", open_binder g) ]
        | Ex g -> List.to_seq [ ("quantifier", All g); ("instantiate", open_binder g) ]
        | Conj fs | Disj fs ->
            let constructor = match f with Conj _ -> fun fs -> Conj fs | _ -> fun fs -> Disj fs in
            Seq.cons
              ("connective", match f with Conj _ -> Disj fs | _ -> Conj fs)
              (Seq.append
                 (Seq.map (fun f -> ("subformula", f)) (List.to_seq fs))
                 (Seq.mapi
                    (fun i _ -> ("drop-operand", constructor (remove i fs)))
                    (List.to_seq fs)))
        | _ -> Seq.empty)
    in
    let here = Seq.map (fun (operator, formula) -> { operator; path; formula }) local in
    let children, rebuild =
      match f with
      | Neg g -> ([ g ], function [ g ] -> Neg g | _ -> assert false)
      | All g -> ([ g ], function [ g ] -> All g | _ -> assert false)
      | Ex g -> ([ g ], function [ g ] -> Ex g | _ -> assert false)
      | Conj gs -> (gs, fun gs -> Conj gs)
      | Disj gs -> (gs, fun gs -> Disj gs)
      | _ -> ([], fun _ -> f)
    in
    let descendants =
      List.to_seq children
      |> Seq.mapi (fun i g ->
          Seq.map
            (fun edit -> { edit with formula = rebuild (replace i edit.formula children) })
            (walk (path @ [ i ]) g))
      |> Seq.concat
    in
    let terms, rebuild_terms =
      match f with
      | Pred (s, ts) -> (ts, fun ts -> Pred (s, ts))
      | Eq (x, y) -> ([ x; y ], function [ x; y ] -> Eq (x, y) | _ -> assert false)
      | _ -> ([], fun _ -> f)
    in
    let term_changes =
      List.to_seq terms
      |> Seq.mapi (fun i t ->
          smaller_terms t
          |> Seq.map (fun t ->
              {
                operator = "subterm";
                path = path @ [ i ];
                formula = rebuild_terms (replace i t terms);
              }))
      |> Seq.concat
    in
    Seq.append here (Seq.append descendants term_changes) ()
  in
  let seen = Hashtbl.create 32 in
  walk [] formula
  |> Seq.filter (fun edit ->
      if
        edit.formula = formula
        || (not (source_scoped ~closed edit.formula))
        || (shrinking && size edit.formula >= size formula)
        || Hashtbl.mem seen edit.formula
      then false
      else (
        Hashtbl.add seen edit.formula ();
        true))

let mutations ?(closed = true) formula = candidates ~shrinking:false ~closed formula
let shrinks formula = candidates ~shrinking:true ~closed:false formula

(* A finite observation of a theory is explicit: no conclusion about the
   original theory follows from a mutated snapshot's refutation. *)
let snapshot ?(observations = 8) theory =
  if observations < 0 then invalid_arg "Mutation: negative observation budget";
  let axioms = ref (List.rev (Theory.fixed theory)) in
  let next = ref (List.length !axioms) in
  let streams =
    List.map (fun schema -> (schema, ref (Theory.enumerate theory schema))) (Theory.schemas theory)
  in
  for _ = 1 to observations do
    List.iter
      (fun (schema, stream) ->
        match !stream () with
        | Seq.Nil -> ()
        | Seq.Cons (parameter, rest) ->
            stream := rest;
            Option.iter
              (fun p ->
                let axiom = Theory.instantiate_parameter theory ~id:!next schema p in
                if not (Theory.validate_axiom theory axiom) then
                  invalid_arg "Mutation: unauthorized snapshot axiom";
                incr next;
                axioms := axiom :: !axioms)
              parameter)
      streams
  done;
  List.rev !axioms

type mutant = { axiom_id : int; change : change; problem : string }

let theories axioms =
  List.to_seq axioms
  |> Seq.mapi (fun i (a : axiom) ->
      mutations a.formula
      |> Seq.map (fun change ->
          let changed = { a with formula = change.formula } in
          { axiom_id = a.axiom_id; change; problem = Tptp.problem (replace i changed axioms) }))
  |> Seq.concat
