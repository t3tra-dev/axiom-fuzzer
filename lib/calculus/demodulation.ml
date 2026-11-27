open Wire
(** Rewriting is one-way matching, never unification of the target variables. Each rewrite carries
    an ordinary paramodulation certificate step. *)

type rewrite = {
  parent : int;
  reverse : bool;
  lhs : term;
  rhs : term;
  extra : variable list;
      (** Variables of [rhs] that [lhs] lacks. A rewrite binds them to the minimal constant
          ([minimal]): E's rewrite_strong_rhs_inst, for an unorientable equation of an
          ordered-rewriting worker with [instances]. Empty for every other rule. *)
  oriented : bool;
      (** [lhs] > [rhs] in the term ordering, so every instance decreases; false for a direction of
          an unorientable equation (ordered rewriting), whose instances are checked one by one. *)
}

type indexed_rewrite = { rewrite : rewrite; generation : int; cell : Index.cell; sequence : int }
(** [cell] is the liveness of the [add] that made the rule, as in Index. [sequence] numbers the
    rules in the order [add] makes them, so a head's live rules oldest first ([candidates]) are its
    live rules in increasing [sequence]. *)

(* A perfect discrimination tree over the arguments of one head's left sides (the head itself is
   the [trees] key): a path spells the preorder of a left side's arguments, a function symbol
   with its arity per edge ([next]) and [any] for a variable; a node reached when the whole left
   side is spelled holds its rules ([here], with their [sequence]). The rules found for a term are
   exactly those whose left side [Subsumption.matchable] accepts on it: the same symbols and
   arities at every non-variable position, any subterm at a variable. *)
type tree = {
  mutable here : indexed_rewrite list;
  mutable any : tree option;
  mutable next : (symbol * int * tree) list;
}

type t = {
  rules : indexed_rewrite list Tbl.Head.t;
  live : int Tbl.Int.t;
  cells : Index.cell Tbl.Int.t;  (** the cell of each live parent's current generation *)
  mutable dirty : (symbol * int) list;  (** as Index.dirty *)
  mutable stale : int;  (** adds removed or superseded since the last [compact] *)
  mutable generation : int;
  order : Ordering.order;
  ordered_rewriting : bool;
  cache : (int * rewrite array) Tbl.Head.t;
      (** [rewrite_first]'s live rules of a head, oldest first, valid while [version] is unchanged
      *)
  mutable version : int;  (** changes whenever a rule is added or removed *)
  instances : bool;
      (** With [ordered_rewriting]: also the directions of an unorientable unit equation whose sides
          have different variables. A direction whose right side has a variable that the left side
          lacks binds it to [minimal] (instance rewriting); the instance must still decrease. *)
  mutable minimal : term option;
      (** The least constant of the problem in the term ordering ([set_minimal]); [None] keeps the
          rules with [extra] variables out of the index. *)
  mutable instance_rewrites : int;  (** rewrites found by a rule with [extra] variables *)
  unoriented_cache : (int * rewrite array) Tbl.Head.t;
      (** [unoriented]'s rules of a head, valid while [version] is unchanged *)
  trees : tree Tbl.Head.t;
      (** per head, the tree of the rules in [rules] (dead ones until [compact] drops them) *)
  mutable sequence : int;  (** the next rule's [sequence] *)
}

let create ?(order = Ordering.standard) ?(ordered_rewriting = false) ?(instances = false) () =
  {
    rules = Tbl.Head.create 16;
    live = Tbl.Int.create 32;
    cells = Tbl.Int.create 32;
    dirty = [];
    stale = 0;
    generation = 0;
    order;
    ordered_rewriting;
    cache = Tbl.Head.create 16;
    version = 0;
    instances;
    minimal = None;
    instance_rewrites = 0;
    unoriented_cache = Tbl.Head.create 16;
    trees = Tbl.Head.create 16;
    sequence = 0;
  }

let leaf () = { here = []; any = None; next = [] }

let rec child (f : symbol) n = function
  | [] -> None
  | (g, m, node) :: rest -> if Int.equal n m && Sym.equal f g then Some node else child f n rest

(* The node that spells [pending] (a left side's remaining arguments) from [node], created as
   needed. *)
let rec spell node pending =
  match pending with
  | [] -> node
  | V _ :: rest ->
      let next =
        match node.any with
        | Some next -> next
        | None ->
            let next = leaf () in
            node.any <- Some next;
            next
      in
      spell next rest
  | Fn (f, ts) :: rest ->
      let n = List.length ts in
      let next =
        match child f n node.next with
        | Some next -> next
        | None ->
            let next = leaf () in
            node.next <- (f, n, next) :: node.next;
            next
      in
      spell next (ts @ rest)

let insert t (rule : indexed_rewrite) =
  match rule.rewrite.lhs with
  | Fn (f, args) ->
      let key = (f, List.length args) in
      let root =
        match Tbl.Head.find_opt t.trees key with
        | Some root -> root
        | None ->
            let root = leaf () in
            Tbl.Head.replace t.trees key root;
            root
      in
      let node = spell root args in
      node.here <- rule :: node.here
  | V _ -> ()

(* Removes [rule] from the node its left side spells; nodes left empty are pruned. Returns whether
   [node] itself is now empty. *)
let rec unspell (rule : indexed_rewrite) node pending =
  (match pending with
  | [] -> node.here <- List.filter (fun r -> r != rule) node.here
  | V _ :: rest -> (
      match node.any with
      | Some next -> if unspell rule next rest then node.any <- None
      | None -> ())
  | Fn (f, ts) :: rest -> (
      let n = List.length ts in
      match child f n node.next with
      | Some next ->
          if unspell rule next (ts @ rest) then
            node.next <- List.filter (fun (_, _, x) -> x != next) node.next
      | None -> ()));
  node.here = [] && node.any = None && node.next = []

let delete t (rule : indexed_rewrite) =
  match rule.rewrite.lhs with
  | Fn (f, args) -> (
      let key = (f, List.length args) in
      match Tbl.Head.find_opt t.trees key with
      | Some root -> if unspell rule root args then Tbl.Head.remove t.trees key
      | None -> ())
  | V _ -> ()

(* The least constant among [constants] in the term ordering: the instance E's
   rewrite_strong_rhs_inst gives an extra right-hand-side variable (OCBDesignatedMinTerm). E creates
   a fresh constant when the signature has none; a fresh symbol would be outside the signature the
   kernel checks, so then no rule with extra variables is used. *)
let minimal_constant ?(order = Ordering.standard) constants =
  List.fold_left
    (fun best c ->
      match best with Some b when not (Ordering.greater ~order b c) -> best | _ -> Some c)
    None constants

(* The distinct constants of [clauses], in order of first occurrence (a table: inputs with
   thousands of constants, as CSR044-10, must not cost a quadratic scan). *)
let constants_of (clauses : clause list) =
  let seen = Hashtbl.create 64 and found = ref [] in
  let rec visit = function
    | V _ -> ()
    | Fn (f, []) as c ->
        if not (Hashtbl.mem seen f) then (
          Hashtbl.add seen f ();
          found := c :: !found)
    | Fn (_, ts) -> List.iter visit ts
  in
  List.iter (List.iter (fun l -> List.iter visit (Clause.atom_terms l.atom))) clauses;
  List.rev !found

let set_minimal t constants = t.minimal <- minimal_constant ~order:t.order constants

(* Whether [live] still maps the rule's parent to its generation, read from its cell. *)
let[@inline] current (_ : t) rule = rule.cell.Index.alive

let orient ?(order = Ordering.standard) (s : step) =
  match Clause.scope 1 s.clause with
  | [ { positive = true; atom = E (left, right) } ] -> (
      let direction =
        if Ordering.greater ~order left right then Some (false, left, right)
        else if Ordering.greater ~order right left then Some (true, right, left)
        else None
      in
      match direction with
      | Some (reverse, (Fn _ as lhs), rhs) ->
          Some { parent = s.id; reverse; lhs; rhs; extra = []; oriented = true }
      | _ -> None)
  | _ -> None

let term_variables t = Wire.variables [ { positive = true; atom = E (t, t) } ]

(* Ordered rewriting keeps both directions of an unorientable unit equation
   whose sides have the same variables; rewrite_once requires every instance to
   decrease in KBO, the standard ordered-rewriting side condition. With [instances]
   the sides may have different variables (E's forward_demod 2 with
   rewrite_strong_rhs_inst): a direction whose right side lacks some left variables is an
   ordinary ordered rule, and one whose right side has extra variables binds them to the
   minimal constant when it rewrites. *)
let orient_all t (s : step) =
  match orient ~order:t.order s with
  | Some rule -> [ rule ]
  | None when t.ordered_rewriting -> (
      match Clause.scope 1 s.clause with
      | [ { positive = true; atom = E (left, right) } ] when left <> right ->
          let lv = List.sort_uniq compare (term_variables left)
          and rv = List.sort_uniq compare (term_variables right) in
          let same = lv = rv in
          if (not same) && not t.instances then []
          else
            List.filter_map
              (fun (reverse, lhs, rhs, lhs_vars, rhs_vars) ->
                match lhs with
                | V _ -> None
                | Fn _ -> (
                    match List.filter (fun v -> not (List.mem v lhs_vars)) rhs_vars with
                    | [] -> Some { parent = s.id; reverse; lhs; rhs; extra = []; oriented = false }
                    | extra ->
                        if t.minimal = None then None
                        else Some { parent = s.id; reverse; lhs; rhs; extra; oriented = false }))
              [ (false, left, right, lv, rv); (true, right, left, rv, lv) ]
      | _ -> [])
  | None -> []

(* The matcher [sigma] of a rule's left side, completed with the minimal constant for its
   [extra] variables. *)
let complete t (rule : rewrite) sigma =
  match (rule.extra, t.minimal) with
  | [], _ -> sigma
  | extra, Some c -> List.fold_left (fun sigma v -> (v, c) :: sigma) sigma extra
  | _ :: _, None -> sigma

(* A rule set leaves the index (its parent is removed or added again): its rules become stale.
   Their buckets are the heads of the parent's equation sides (a superset of the rules' sides),
   recomputed from the clause. *)
let retire t (cell : Index.cell) =
  cell.alive <- false;
  t.stale <- t.stale + 1;
  List.iter
    (fun l ->
      match l.atom with
      | E (x, y) ->
          List.iter
            (function Fn (f, args) -> t.dirty <- (f, List.length args) :: t.dirty | V _ -> ())
            [ x; y ]
      | P _ | D _ -> ())
    cell.clause

let add t step =
  match orient_all t step with
  | [] -> ()
  | rules ->
      if t.generation = max_int then invalid_arg "Demodulation: generation overflow";
      t.generation <- t.generation + 1;
      t.version <- t.version + 1;
      let generation = t.generation in
      Tbl.Int.replace t.live step.id generation;
      Option.iter (retire t) (Tbl.Int.find_opt t.cells step.id);
      let cell = { Index.alive = true; clause = step.clause; postings = 0 } in
      List.iter
        (fun rule ->
          match rule.lhs with
          | Fn (f, args) ->
              let key = (f, List.length args) in
              let indexed = { rewrite = rule; generation; cell; sequence = t.sequence } in
              t.sequence <- t.sequence + 1;
              Tbl.Head.replace t.rules key
                (indexed :: Option.value ~default:[] (Tbl.Head.find_opt t.rules key));
              insert t indexed
          | V _ -> ())
        rules;
      Tbl.Int.replace t.cells step.id cell

let remove t id =
  if Tbl.Int.mem t.live id then t.version <- t.version + 1;
  Tbl.Int.remove t.live id;
  Option.iter (retire t) (Tbl.Int.find_opt t.cells id);
  Tbl.Int.remove t.cells id

(* The rules of a bucket that compaction drops leave their tree. *)
let prune t xs = List.iter (fun r -> if not (current t r) then delete t r) xs

(* Every bucket filtered: the reference for [compact] in the unit tests. *)
let compact_all t =
  t.dirty <- [];
  t.stale <- 0;
  Tbl.Head.filter_map_inplace
    (fun _ xs ->
      prune t xs;
      match Shared.filter (current t) xs with [] -> None | xs -> Some xs)
    t.rules

(* As Index.compact: only the buckets of removed or superseded rules can change. *)
let compact t =
  if t.stale > 0 then (
    if
      (* With at least as many dirty marks as buckets, the full sweep costs no more. *)
      List.compare_length_with t.dirty (Tbl.Head.length t.rules) >= 0
    then compact_all t
    else
      let dirty = t.dirty and seen = Tbl.Head.create 16 in
      t.dirty <- [];
      t.stale <- 0;
      List.iter
        (fun k ->
          if not (Tbl.Head.mem seen k) then (
            Tbl.Head.add seen k ();
            match Tbl.Head.find_opt t.rules k with
            | None -> ()
            | Some xs -> (
                match Shared.filter (current t) xs with
                | [] ->
                    prune t xs;
                    Tbl.Head.remove t.rules k
                | ys ->
                    if ys != xs then (
                      prune t xs;
                      Tbl.Head.replace t.rules k ys))))
        dirty)

(* The live rules of a head in the order [rewrite_once] tries them (oldest first). *)
let candidates t key =
  match Tbl.Head.find_opt t.cache key with
  | Some (version, rules) when version = t.version -> rules
  | _ ->
      let rules =
        Option.value ~default:[] (Tbl.Head.find_opt t.rules key)
        |> List.filter_map (fun r -> if current t r then Some r.rewrite else None)
        |> List.rev |> Array.of_list
      in
      Tbl.Head.replace t.cache key (t.version, rules);
      rules

exception Rewrite of int * int list * rewrite * (variable * term) list

(* The live rules of the head [key] whose left side [Subsumption.matchable] accepts on the term
   with arguments [args], oldest first: the rules of [candidates] that pass its structural test,
   in the same order. *)
let matching t key args =
  match Tbl.Head.find_opt t.trees key with
  | None -> []
  | Some root -> (
      let found = ref [] in
      let rec go node pending =
        match pending with
        | [] -> List.iter (fun r -> if current t r then found := r :: !found) node.here
        | term :: rest -> (
            (match node.any with Some next -> go next rest | None -> ());
            match term with
            | V _ -> ()
            | Fn (f, ts) -> (
                match child f (List.length ts) node.next with
                | Some next -> go next (ts @ rest)
                | None -> ()))
      in
      go root args;
      match !found with
      | ([] | [ _ ]) as rules -> rules
      | rules -> List.sort (fun (a : indexed_rewrite) b -> Int.compare a.sequence b.sequence) rules)

let rewrite_once ?using ?(guard = fun () -> ()) ?(oriented_only = false) t (target : step) =
  let work = ref 0 in
  let match_guard () =
    incr work;
    if !work mod 64 = 0 then guard ()
  in
  let checked = Option.is_some using in
  let using = Option.map (fun rule -> [| rule |]) using in
  let rec scope term =
    match_guard ();
    match term with V (_, i) -> V (2, i) | Fn (f, args) -> Fn (f, List.map scope args)
  in
  let rec apply sigma term =
    match_guard ();
    match term with
    | V v as term -> Option.value ~default:term (List.assoc_opt v sigma)
    | Fn (f, args) -> Fn (f, List.map (apply sigma) args)
  in
  (* The rewrite is searched for on the target's own terms when all of its variables are (0, i):
     renaming them into scope 2 is then a bijection, under which matching gives the renamed
     bindings and the term ordering gives the same answers, so only the found rewrite is copied
     into scope 2 (as [rewrite_first] does). Otherwise the target is copied into scope 2 first, as
     it always was. *)
  let unscoped = List.for_all (fun ((a, _) : variable) -> a = 0) (Wire.variables target.clause) in
  let clause =
    if unscoped then target.clause else List.map (Clause.map_literal scope) target.clause
  in
  (* Preorder over the literals, their atom's terms and their subterms, as in Clause.positions: at
     each non-variable subterm, the head's live rules oldest first ([candidates]' cached array:
     the same rules in the same order as filtering the head's list and reversing it), the first
     rule whose instance decreases. *)
  (* A rule that passed the structural test: the matching attempt, then the decrease. *)
  let attempt i reverse_path term (rule : rewrite) =
    guard ();
    (* The rules of [matching] are live; only a [using] rule is looked up. *)
    if not (rule.parent = target.id || (checked && not (Tbl.Int.mem t.live rule.parent))) then
      match Subsumption.term ~guard:match_guard [] rule.lhs term with
      | exception Subsumption.No_match -> ()
      | sigma ->
          let sigma = complete t rule sigma in
          if Ordering.greater ~order:t.order term (apply sigma rule.rhs) then
            raise (Rewrite (i, reverse_path, rule, sigma))
  in
  let rec visit i reverse_path term =
    match_guard ();
    match term with
    | V _ -> ()
    | Fn (f, args) ->
        (match using with
        | Some candidates ->
            for k = 0 to Array.length candidates - 1 do
              let rule = Array.unsafe_get candidates k in
              (* [oriented_only] (E's RuleRewrite level) passes over the directions of
                 unorientable equations. A rule whose left side cannot match here
                 (Subsumption.matchable) is passed over as a failed match would be, without the
                 attempt; it is counted as matching work. *)
              if oriented_only && not rule.oriented then ()
              else if not (Subsumption.matchable rule.lhs term) then match_guard ()
              else attempt i reverse_path term rule
            done
        | None ->
            (* The head's live rules oldest first, restricted to those whose left side can match
               here ([matching], the discrimination tree): the rules the head's array scan tried,
               in the same order, so the first decreasing rule is the same. [oriented_only] passes
               over the directions of unorientable equations, as the scan did. *)
            List.iter
              (fun (r : indexed_rewrite) ->
                let rule = r.rewrite in
                if oriented_only && not rule.oriented then () else attempt i reverse_path term rule)
              (matching t (f, List.length args) args));
        List.iteri (fun j a -> visit i (j :: reverse_path) a) args
  in
  match
    List.iteri
      (fun i (literal : literal) ->
        List.iteri (fun j term -> visit i [ j ] term) (Clause.atom_terms literal.atom))
      clause
  with
  | () -> None
  | exception Rewrite (i, reverse_path, rule, sigma) ->
      let clause, sigma =
        if unscoped then
          ( List.map (Clause.map_literal scope) target.clause,
            List.map (fun (v, term) -> (v, scope term)) sigma )
        else (clause, sigma)
      in
      let path = List.rev reverse_path in
      let changed = Clause.put (List.nth clause i) path (apply sigma rule.rhs) in
      if rule.extra <> [] then t.instance_rewrites <- t.instance_rewrites + 1;
      Some
        ( Clause.replace i changed clause,
          Paramodulate (rule.parent, 0, rule.reverse, target.id, i, path, sigma) )

(* [candidates] without the oriented rules: the directions of unorientable equations, whose
   instances may decrease under an order of the variables (Joinability) where they do not
   decrease in every instance. *)
let unoriented t key =
  match Tbl.Head.find_opt t.unoriented_cache key with
  | Some (version, rules) when version = t.version -> rules
  | _ ->
      let rules =
        Array.of_list (List.filter (fun r -> not r.oriented) (Array.to_list (candidates t key)))
      in
      Tbl.Head.replace t.unoriented_cache key (t.version, rules);
      rules

exception Found of int * int list * rewrite * (variable * term) list

(** [rewrite_once]'s rewrite, found faster, for a lean worker's normal-form rewriting: the same
    position (leftmost-outermost, preorder over the literals) and the same rule (the oldest live
    rule whose instance decreases), so the same result. It walks the target's own terms and copies
    only the found rewrite into scope 2, takes a head's live rules from a cache, skips a subterm for
    which [skip] holds (the caller knows it is in normal form) and passes every subterm it finds in
    normal form to [irreducible]. KBO, and so the decrease check, is invariant under the renaming of
    the target's variables into scope 2. [oriented_only] (as in [rewrite_once]) skips the directions
    of unorientable equations: E's RuleRewrite level, for a worker whose rule set also serves E's
    FullRewrite level. *)
let rewrite_first ?(guard = fun () -> ()) ?(oriented_only = false) ?(skip = fun _ -> false)
    ?(irreducible = fun _ -> ()) t (target : step) =
  let work = ref 0 in
  let match_guard () =
    incr work;
    if !work mod 64 = 0 then guard ()
  in
  let rec apply sigma term =
    match_guard ();
    match term with
    | V v as term -> Option.value ~default:term (List.assoc_opt v sigma)
    | Fn (f, args) -> Fn (f, List.map (apply sigma) args)
  in
  let rec visit i reverse_path term =
    match_guard ();
    match term with
    | V _ -> ()
    | Fn (f, args) ->
        if not (skip term) then (
          (* As in [rewrite_once]: the head's live rules whose left side can match, oldest first,
             and [oriented_only] passes over the directions of unorientable equations. *)
          List.iter
            (fun (r : indexed_rewrite) ->
              let rule = r.rewrite in
              if oriented_only && not rule.oriented then ()
              else (
                guard ();
                if rule.parent <> target.id then
                  match Subsumption.term ~guard:match_guard [] rule.lhs term with
                  | exception Subsumption.No_match -> ()
                  | sigma ->
                      let sigma = complete t rule sigma in
                      if Ordering.greater ~order:t.order term (apply sigma rule.rhs) then
                        raise (Found (i, reverse_path, rule, sigma))))
            (matching t (f, List.length args) args);
          List.iteri (fun j a -> visit i (j :: reverse_path) a) args;
          irreducible term)
  in
  match
    List.iteri
      (fun i (literal : literal) ->
        List.iteri (fun j term -> visit i [ j ] term) (Clause.atom_terms literal.atom))
      target.clause
  with
  | () -> None
  | exception Found (i, reverse_path, rule, sigma) ->
      if rule.extra <> [] then t.instance_rewrites <- t.instance_rewrites + 1;
      let rec scope term =
        match_guard ();
        match term with V (_, i) -> V (2, i) | Fn (f, args) -> Fn (f, List.map scope args)
      in
      let clause = List.map (Clause.map_literal scope) target.clause in
      let sigma = List.map (fun (v, term) -> (v, scope term)) sigma in
      let path = List.rev reverse_path in
      let changed = Clause.put (List.nth clause i) path (apply sigma rule.rhs) in
      Some
        ( Clause.replace i changed clause,
          Paramodulate (rule.parent, 0, rule.reverse, target.id, i, path, sigma) )
