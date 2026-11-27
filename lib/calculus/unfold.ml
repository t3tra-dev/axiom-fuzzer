open Wire
(** Equational-definition unfolding (E 3.5.9 CLAUSES/ccl_unfold_defs.c), a search-side preprocessing
    step of the initial clause set.

    A definition is a positive unit equation [f(X1,...,Xn) = r] (n >= 1) whose defined side has
    pairwise distinct variables as arguments, where [f] does not occur in [r] and every variable of
    [r] is one of the [Xi] (E's EqnIsDefinition with min_arity 1). The left side is tried first, as
    E does. A definition is used when [r] is at most [limit] heavier than [f(X1,...,Xn)] in E's
    standard weight (functions 2, variables 1): E's eq-unfold-limit, 20 by default and in every
    ported heuristic. It rewrites every other clause, one leftmost-innermost traversal whose every
    application is one ordinary paramodulation step from the definition, and leaves the search set;
    its symbol no longer occurs there. The definitions are found in E's order: the clauses sorted as
    E's canonical order sorts them (positive before mixed before negative, fewer negative literals,
    fewer positive literals, smaller standard weight; ties by input position instead of E's
    structural and lexical comparison), each tested in its current form, once.

    The step changes only what the search sees. The removed definitions stay proof nodes, every
    rewritten clause is derived from the original input clauses by [Paramodulate] steps, and
    removing [f = r] once [f] occurs nowhere else preserves satisfiability (interpret [f] as [r]),
    so the kernel and the certificate format are unchanged. Not ported: E's predicate definitions
    ([P(X1,...,Xn)] as [P(..) = $true]), which unit simplification and subsumption cover. *)

(* E's DEFAULT_EQDEF_INCRLIMIT (ccl_unfold_defs.h:41); schedule.vars sets it to 20 for e208,
   y1346 and sat001. *)
let default_limit = 20

(* E's DEFAULT_EQDEF_MAXCLAUSES (ccl_unfold_defs.h:44): no unfolding above this many clauses. *)
let max_clauses = 20000

(* Deterministic caps of this port (E has none): a plan whose rewriting would store more than
   [max_steps] paramodulation steps, or more than [max_symbols] symbols over all of them, or a
   clause heavier than [max_weight], is not applied. Nested occurrences under a rhs that repeats a
   variable can grow a term exponentially; the caps bound the proof nodes the step can add. *)
let max_steps = 100_000
let max_symbols = 4_000_000
let max_weight = 200_000

type definition = { symbol : symbol; arity : int; reverse : bool }
(** The defined symbol and whether the defined term is the right side of the stored equation (the
    [reverse] flag of the [Paramodulate] steps that use it). *)

let rec standard_weight = function
  | V _ -> 1
  | Fn (_, ts) -> List.fold_left (fun n t -> n + standard_weight t) 2 ts

let rec occurs symbol arity = function
  | V _ -> false
  | Fn (g, ts) -> (g = symbol && List.length ts = arity) || List.exists (occurs symbol arity) ts

let rec variables acc = function
  | V v -> if List.mem v acc then acc else v :: acc
  | Fn (_, ts) -> List.fold_left variables acc ts

(* E's TermIsDefTerm (min_arity 1), the f-not-in-rhs test and EqnHasUnboundVars. *)
let defines ~defined ~other =
  match defined with
  | Fn (f, (_ :: _ as args)) -> (
      let rec distinct seen = function
        | [] -> Some seen
        | V v :: rest -> if List.mem v seen then None else distinct (v :: seen) rest
        | Fn _ :: _ -> None
      in
      match distinct [] args with
      | None -> None
      | Some bound ->
          let n = List.length args in
          if occurs f n other then None
          else if List.for_all (fun v -> List.mem v bound) (variables [] other) then Some (f, n)
          else None)
  | _ -> None

let definition clause =
  match clause with
  | [ { positive = true; atom = E (s, t) } ] -> (
      match defines ~defined:s ~other:t with
      | Some (symbol, arity) -> Some { symbol; arity; reverse = false }
      | None -> (
          match defines ~defined:t ~other:s with
          | Some (symbol, arity) -> Some { symbol; arity; reverse = true }
          | None -> None))
  | _ -> None

let sides d clause =
  match clause with
  | [ { positive = true; atom = E (s, t) } ] -> if d.reverse then (t, s) else (s, t)
  | _ -> invalid_arg "Unfold.sides: not a unit equation"

(* How much heavier the definition's right side is than its defined term. *)
let increment d clause =
  let lhs, rhs = sides d clause in
  standard_weight rhs - standard_weight lhs

let literal_weight l =
  match l.atom with
  | E (x, y) -> standard_weight x + standard_weight y
  (* E stores a predicate literal as an equation with $true (weight 2). *)
  | P (_, ts) | D (_, ts) -> List.fold_left (fun n t -> n + standard_weight t) 4 ts

let clause_weight c = List.fold_left (fun n l -> n + literal_weight l) 0 c

(* E's ClauseStructWeightCompare up to its structural and lexical tie-breaks. *)
let canonical_key c =
  let negative = List.length (List.filter (fun l -> not l.positive) c) in
  let positive = List.length c - negative in
  let kind = if negative = 0 then 0 else if positive = 0 then 2 else 1 in
  (kind, negative, positive, clause_weight c)

let apply sigma t =
  let rec go = function
    | V v as t -> ( match List.assoc_opt v sigma with Some s -> s | None -> t)
    | Fn (g, ts) -> Fn (g, List.map go ts)
  in
  go t

let bindings lhs args =
  match lhs with
  | Fn (_, xs) -> List.map2 (fun x a -> match x with V v -> (v, a) | Fn _ -> assert false) xs args
  | V _ -> assert false

(* Rewrite every occurrence in a term, innermost first; [count] counts the applications. *)
let rec unfold_term d lhs rhs count = function
  | V _ as t -> t
  | Fn (g, args) ->
      let args = List.map (unfold_term d lhs rhs count) args in
      if g = d.symbol && List.length args = d.arity then (
        incr count;
        apply (bindings lhs args) rhs)
      else Fn (g, args)

let unfold_clause d (lhs, rhs) count c =
  List.map (fun l -> Clause.map_literal (unfold_term d lhs rhs count) l) c

type plan = {
  removed : (int * definition) list;
      (** Positions of the removed definitions in the input list, in removal order. *)
  clauses : clause array;
      (** Every input clause in its final form; a removed definition in its form when removed. *)
  conjecture : bool array;
      (** Clauses rewritten by a definition at a [goal] position (E makes them conjectures). *)
  steps : int;  (** Paramodulation steps of the rewriting. *)
  rewritten : int;  (** Clauses (other than removed definitions) that changed. *)
}

(* Drop repeated literals, keeping the input order (E's ClauseRemoveSuperfluousLiterals for the
   duplicates; Clause.normalize drops them from the stored clause as well). *)
let dedup c =
  let rec go seen = function
    | [] -> List.rev seen
    | l :: rest -> if List.mem l seen then go seen rest else go (l :: seen) rest
  in
  go [] c

(** E's ClauseSetUnfoldAllEqDefs over [clauses] (input order). [goal i] tells whether position [i]
    belongs to a negated-conjecture axiom. [None]: nothing to unfold, more than [max_clauses]
    clauses, or a cap of the port reached. *)
let plan ?(guard = fun () -> ()) ?(goal = fun _ -> false) ?order ~limit clauses =
  let current = Array.of_list (List.map dedup clauses) in
  let n = Array.length current in
  if n = 0 || n > max_clauses then None
  else
    (* [order]: E's canonical order of the positions (ClauseSetCanonize, before E unfolds), when
       the caller has E's view of the input (E_initial); otherwise the structural key, ties by
       input position. *)
    let order =
      match order with
      | Some o when List.length o = n -> o
      | _ ->
          List.stable_sort
            (fun i j -> compare (canonical_key current.(i)) (canonical_key current.(j)))
            (List.init n Fun.id)
    in
    let removed = Array.make n false and conjecture = Array.make n false in
    let changed = Array.make n false in
    let exception Capped in
    let steps = ref 0 and symbols = ref 0 and found = ref [] in
    let try_position p =
      guard ();
      if not removed.(p) then
        match definition current.(p) with
        | Some d when increment d current.(p) <= limit ->
            removed.(p) <- true;
            found := (p, d) :: !found;
            let lhs, rhs = sides d current.(p) in
            Array.iteri
              (fun q c ->
                guard ();
                if not removed.(q) then
                  let count = ref 0 in
                  let c' = unfold_clause d (lhs, rhs) count c in
                  if !count > 0 then (
                    let c' = dedup c' in
                    let w = clause_weight c' in
                    steps := !steps + !count;
                    symbols := !symbols + (!count * max w (clause_weight c));
                    if !steps > max_steps || !symbols > max_symbols || w > max_weight then
                      raise Capped;
                    current.(q) <- c';
                    changed.(q) <- true;
                    if goal p || conjecture.(p) then conjecture.(q) <- true))
              current
        | _ -> ()
    in
    match List.iter try_position order with
    | exception Capped -> None
    | () when !found = [] -> None
    | () ->
        let removed_list = List.rev !found in
        let rewritten = ref 0 in
        Array.iteri (fun i c -> if c && not removed.(i) then incr rewritten) changed;
        Some
          {
            removed = removed_list;
            clauses = current;
            conjecture;
            steps = !steps;
            rewritten = !rewritten;
          }

type source = { parent : int; clause : clause; definition : definition }
(** A removed definition as a proof node: its id, its stored clause and the definition it states. *)

(** The stored definition [step] as a rewrite source, if it still states [d]. *)
let source (step : step) d =
  match definition step.clause with
  | Some d' when d'.symbol = d.symbol && d'.arity = d.arity && d'.reverse = d.reverse ->
      Some { parent = step.id; clause = step.clause; definition = d }
  | _ -> None

(** One unfolding step of a stored clause: its leftmost-innermost occurrence of the defined symbol
    rewritten by an ordinary paramodulation from the definition (scope 1 into scope 2, the
    definition's variables bound by matching), or [None] when the symbol does not occur. *)
let rewrite_once (s : source) (target : step) =
  let d = s.definition in
  let lhs, rhs = sides d (Clause.scope 1 s.clause) in
  let clause = Clause.scope 2 target.clause in
  (* The innermost occurrence below [t]: its path (root to node) and arguments. *)
  let rec find reverse_path = function
    | V _ -> None
    | Fn (g, args) -> (
        let rec below j = function
          | [] -> None
          | a :: rest -> (
              match find (j :: reverse_path) a with Some _ as r -> r | None -> below (j + 1) rest)
        in
        match below 0 args with
        | Some _ as r -> r
        | None ->
            if g = d.symbol && List.length args = d.arity then Some (List.rev reverse_path, args)
            else None)
  in
  let rec literals i = function
    | [] -> None
    | (literal : literal) :: rest -> (
        let rec terms j = function
          | [] -> None
          | t :: more -> ( match find [ j ] t with Some _ as r -> r | None -> terms (j + 1) more)
        in
        match terms 0 (Clause.atom_terms literal.atom) with
        | Some (path, args) ->
            let sigma = bindings lhs args in
            let changed = Clause.put literal path (apply sigma rhs) in
            Some
              ( Clause.replace i changed clause,
                Paramodulate (s.parent, 0, d.reverse, target.id, i, path, sigma) )
        | None -> literals (i + 1) rest)
  in
  literals 0 clause

(** The first source in [sources] that rewrites [target], with the sources from it on. *)
let rec next sources target =
  match sources with
  | [] -> None
  | s :: rest -> (
      match rewrite_once s target with
      | Some result -> Some (result, sources)
      | None -> next rest target)

let describe d =
  let name =
    match d.symbol with Original f -> f | Skolem (a, i) -> Printf.sprintf "sk%d_%d" a i
  in
  Printf.sprintf "%s/%d" name d.arity
