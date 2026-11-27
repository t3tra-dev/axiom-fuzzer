open Wire
(** Branch state is separate from the immutable FO proof and from Active/Passive. Alpha-equivalent
    components share representatives with disjoint variables. Replay checks the instance from each
    splitting occurrence before verifying the component union. *)

type support = int list
type role = Candidate | Retired | Contradiction

type entry = {
  step : step;
  support : support;
  mutable role : role;
  mutable lock : (support * int list) option;
  mutable lock_count : int;
  mutable split_queued : bool;
  mutable split_done : bool;
}

type component = { clause : clause; mutable node : int option }

type 'a hashed = { hash : int; value : 'a }
(** A key with its hash computed once ([Tbl.Hash.clause] or [Tbl.Hash.clause_ints], the hashes of
    [Tbl.Clause] and [Tbl.Clause_ints]): the tables below place and find keys exactly as those
    tables do, without hashing a clause again at every lookup. *)

module Seen = Hashtbl.Make (struct
  type t = clause hashed

  let equal a b = a == b || (Int.equal a.hash b.hash && Tbl.Equal.clause a.value b.value)
  let hash k = k.hash
end)

module Variants = Hashtbl.Make (struct
  type t = (clause * int list) hashed

  let equal a b = a == b || (Int.equal a.hash b.hash && Tbl.Equal.clause_ints a.value b.value)
  let hash k = k.hash
end)

type probe = {
  clause : clause;
  exact : clause hashed;
  mutable variant : (clause * int list) hashed option;  (** computed at its first use *)
}
(** A clause's keys in [seen] and [variants], computed once for the duplicate test of an emitted
    clause, its [remember] and its admission's duplicate test. *)

let probe clause =
  { clause; exact = { hash = Tbl.Hash.clause clause; value = clause }; variant = None }

let variant_key p =
  match p.variant with
  | Some k -> k
  | None ->
      let value = Variant_index.key p.clause in
      let k = { hash = Tbl.Hash.clause_ints value; value } in
      p.variant <- Some k;
      k

type t = {
  solver : Boolean.t;
  entries : entry Tbl.Int.t;
  support_users : int list Tbl.Int.t;
  lock_users : int list Tbl.Int.t;
  seen : int list Seen.t;
  variants : int list Variants.t;
  names : int Tbl.Clause.t;
  component_variants : int list Tbl.Clause_ints.t;
  mutable next_variable : int;
  pending_splits : int Queue.t;
  mutable splits_ready : bool;
  components : component Tbl.Int.t;
  splits : (int * int list) Tbl.Int.t;
  constraints : unit Tbl.Ints.t;
  mutable constraints_rev : int list list;
  mutable conflict_cores : support list;
  mutable model : bool array;
  mutable dirty : bool;
  mutable unsat : bool;
  mutable component_reused : int;
  mutable conflicts : int;
  mutable sat_calls : int;
  mutable model_changes : int;
  mutable model_examined : int;
  mutable minimized : int;
  mutable deactivated : int;
  mutable reactivated : int;
  mutable locked : int;
  mutable unlocked : int;
  mutable lock_limited : int;
  mutable max_support : int;
}

let create () =
  {
    solver = Boolean.create ();
    entries = Tbl.Int.create 256;
    support_users = Tbl.Int.create 64;
    lock_users = Tbl.Int.create 64;
    seen = Seen.create 256;
    variants = Variants.create 128;
    names = Tbl.Clause.create 64;
    component_variants = Tbl.Clause_ints.create 64;
    next_variable = 0;
    pending_splits = Queue.create ();
    splits_ready = false;
    components = Tbl.Int.create 64;
    splits = Tbl.Int.create 64;
    constraints = Tbl.Ints.create 64;
    constraints_rev = [];
    conflict_cores = [];
    model = [||];
    dirty = false;
    unsat = false;
    component_reused = 0;
    conflicts = 0;
    sat_calls = 0;
    model_changes = 0;
    model_examined = 0;
    minimized = 0;
    deactivated = 0;
    reactivated = 0;
    locked = 0;
    unlocked = 0;
    lock_limited = 0;
    max_support = 0;
  }

let rec subset xs ys =
  match (xs, ys) with
  | [], _ -> true
  | _, [] -> false
  | x :: xs, y :: ys -> if x = y then subset xs ys else if x > y then subset (x :: xs) ys else false

let union xs ys = List.sort_uniq compare (xs @ ys)
let dependency t id = (Tbl.Int.find t.entries id).support

let dependencies t = function
  | Component id -> [ id ]
  | rule -> List.fold_left (fun acc id -> union acc (dependency t id)) [] (Wire.parents rule)

let register_users users support id =
  List.iter
    (fun component ->
      Tbl.Int.replace users component
        (id :: Option.value ~default:[] (Tbl.Int.find_opt users component)))
    support

let remember ?probe:given t ~variants (step : step) =
  let p = match given with Some p when p.clause == step.clause -> p | _ -> probe step.clause in
  let support = dependencies t step.rule in
  t.max_support <- max t.max_support (List.length support);
  let entry =
    {
      step;
      support;
      role = Candidate;
      lock = None;
      lock_count = 0;
      split_queued = false;
      split_done = false;
    }
  in
  Tbl.Int.add t.entries step.id entry;
  register_users t.support_users support step.id;
  Seen.replace t.seen p.exact (step.id :: Option.value ~default:[] (Seen.find_opt t.seen p.exact));
  (if variants then
     let key = variant_key p in
     Variants.replace t.variants key
       (step.id :: Option.value ~default:[] (Variants.find_opt t.variants key)));
  (match step.rule with
  | Component id -> (Tbl.Int.find t.components id).node <- Some step.id
  | _ -> ());
  entry

(* Explanation intermediates are immutable proof ancestors, not searchable
   candidates. Keep their branch dependency for later inferences/conflicts and
   collection, without building indices that immediately ignore Retired nodes. *)
let remember_explanation t ~support (step : step) =
  (match step.rule with
  | Component _ -> invalid_arg "Avatar.remember_explanation: component assumption"
  | _ -> ());
  if support <> dependencies t step.rule then
    invalid_arg "Avatar.remember_explanation: inconsistent support";
  let entry =
    {
      step;
      support;
      role = Retired;
      lock = None;
      lock_count = 0;
      split_queued = false;
      split_done = false;
    }
  in
  t.max_support <- max t.max_support (List.length support);
  Tbl.Int.add t.entries step.id entry;
  entry

(* [probe]: the clause's keys, when the caller holds them ([probe] of this clause). *)
let duplicate ?probe:given t ~guard ~variants ~except support clause =
  let p = match given with Some p when p.clause == clause -> p | _ -> probe clause in
  let eligible id =
    id <> except
    &&
    match Tbl.Int.find_opt t.entries id with
    | Some e -> e.role = Candidate && subset e.support support
    | None -> false
  in
  let exact = Option.value ~default:[] (Seen.find_opt t.seen p.exact) in
  List.exists eligible exact
  || variants
     && List.exists
          (fun id ->
            guard ();
            eligible id && Variant_index.variants clause (Tbl.Int.find t.entries id).step.clause)
          (Option.value ~default:[] (Variants.find_opt t.variants (variant_key p)))

(* The clauses that make [duplicate] hold: the eligible exact copies, then the eligible variants.
   Only the orphan bookkeeping of Engine ([Heuristic.loop.orphans]) asks for them, after
   [duplicate] has dropped [clause]. The test is [duplicate]'s, repeated here so that [duplicate],
   which every emitted clause of every worker runs, stays as it is. *)
let duplicates t ~guard ~variants ~except support clause =
  let eligible id =
    id <> except
    &&
    match Tbl.Int.find_opt t.entries id with
    | Some e -> e.role = Candidate && subset e.support support
    | None -> false
  in
  let p = probe clause in
  let exact = List.filter eligible (Option.value ~default:[] (Seen.find_opt t.seen p.exact)) in
  if not variants then exact
  else
    exact
    @ List.filter
        (fun id ->
          guard ();
          (not (List.mem id exact))
          && eligible id
          && Variant_index.variants clause (Tbl.Int.find t.entries id).step.clause)
        (Option.value ~default:[] (Variants.find_opt t.variants (variant_key p)))

let asserted t support = List.for_all (fun id -> id < Array.length t.model && t.model.(id)) support

let enabled t e =
  e.role = Candidate && asserted t e.support
  && match e.lock with None -> true | Some (condition, _) -> not (asserted t condition)

let ordered_entries t =
  Tbl.Int.fold (fun _ e entries -> e :: entries) t.entries []
  |> List.sort (fun a b -> compare a.step.id b.step.id)

let retire t id =
  let e = Tbl.Int.find t.entries id in
  e.role <- Retired;
  e.lock <- None

(* A finite lock budget prevents a clause being hidden forever by successively
   different local reductions. It is not a proof of branch-search completeness. *)
let can_reduce t ~target ~using =
  let e = Tbl.Int.find t.entries target in
  subset (dependency t using) e.support || (e.support <> [] && e.lock_count < 8)

let reduce_using t ~target ~using =
  let e = Tbl.Int.find t.entries target in
  let support = List.concat_map (dependency t) using |> List.sort_uniq compare in
  if subset support e.support then (
    retire t target;
    true)
  else if e.support = [] then
    (* Local simplification may add a consequence while preserving the global
       inference path, including the original parent of a split. *)
    false
  else if e.lock_count < 8 then (
    e.lock <- Some (support, using);
    register_users t.lock_users support target;
    e.lock_count <- e.lock_count + 1;
    t.locked <- t.locked + 1;
    true)
  else (
    t.lock_limited <- t.lock_limited + 1;
    false)

let reduce t ~target ~using = reduce_using t ~target ~using:[ using ]

let affected_entries t ~guard changed =
  let affected = Tbl.Int.create 32 in
  let gather users eligible component =
    List.iter
      (fun id ->
        guard ();
        match Tbl.Int.find_opt t.entries id with
        | Some e when e.role = Candidate && eligible e -> Tbl.Int.replace affected id e
        | _ -> ())
      (Option.value ~default:[] (Tbl.Int.find_opt users component))
  in
  List.iter
    (fun component ->
      gather t.support_users (fun _ -> true) component;
      (* Replaced and released locks leave bounded stale postings until collection. *)
      gather t.lock_users
        (fun e ->
          match e.lock with Some (condition, _) -> List.mem component condition | None -> false)
        component)
    changed;
  let entries =
    Tbl.Int.fold (fun _ e entries -> e :: entries) affected []
    |> List.sort (fun a b -> compare a.step.id b.step.id)
  in
  t.model_examined <- t.model_examined + List.length entries;
  entries

let unlock t ~guard entries =
  List.iter
    (fun e ->
      guard ();
      match e.lock with
      | Some (condition, _) when not (asserted t condition) ->
          e.lock <- None;
          t.unlocked <- t.unlocked + 1
      | _ -> ())
    entries

let components = Clause.components

let offer_split t ~guard step =
  let e = Tbl.Int.find t.entries step.id in
  if
    (not e.split_queued) && (not e.split_done)
    && List.length step.clause > 1
    && List.length (components ~guard step.clause) > 1
  then (
    e.split_queued <- true;
    t.splits_ready <- true;
    Queue.add step.id t.pending_splits)

let take_split t ~guard =
  let rec take remaining =
    if remaining = 0 then None
    else (
      guard ();
      let id = Queue.take t.pending_splits in
      match Tbl.Int.find_opt t.entries id with
      | Some e when e.role = Candidate && not e.split_done ->
          if enabled t e then (
            e.split_queued <- false;
            Some e.step)
          else (
            Queue.add id t.pending_splits;
            take (remaining - 1))
      | _ -> take (remaining - 1))
  in
  let result = take (Queue.length t.pending_splits) in
  if result = None then t.splits_ready <- false;
  result

let name t clause =
  let clause = Clause.normalize clause in
  let key = Variant_index.key clause in
  let existing =
    match Tbl.Clause.find_opt t.names clause with
    | Some id -> Some id
    | None ->
        List.find_opt
          (fun id ->
            Option.is_some (Variant_index.renaming clause (Tbl.Int.find t.components id).clause))
          (Option.value ~default:[] (Tbl.Clause_ints.find_opt t.component_variants key))
  in
  match existing with
  | Some id ->
      t.component_reused <- t.component_reused + 1;
      Tbl.Clause.replace t.names clause id;
      id
  | None ->
      let offset = t.next_variable in
      let count = List.length (Wire.variables clause) in
      if count > max_int - offset then invalid_arg "component variable limit";
      t.next_variable <- offset + count;
      let representative =
        List.map (Clause.map_literal (Clause.map_vars (fun (_, i) -> V (0, offset + i)))) clause
      in
      let id = Boolean.new_variable t.solver in
      Tbl.Clause.add t.names clause id;
      Tbl.Clause_ints.replace t.component_variants key
        (id :: Option.value ~default:[] (Tbl.Clause_ints.find_opt t.component_variants key));
      Tbl.Int.add t.components id { clause = representative; node = None };
      id

let constraint_ t ~guard origin clause =
  let clause = List.sort_uniq compare clause in
  if not (Tbl.Ints.mem t.constraints clause) then (
    guard ();
    ignore (Boolean.add_clause t.solver ~origin clause);
    Tbl.Ints.add t.constraints clause ();
    t.constraints_rev <- clause :: t.constraints_rev;
    t.dirty <- true)

let conflict t ~guard (step : step) =
  if step.clause <> [] then invalid_arg "Avatar.conflict: expected an empty derivation";
  let e = Tbl.Int.find t.entries step.id in
  e.role <- Contradiction;
  t.conflicts <- t.conflicts + 1;
  (* Only empty FO derivations reach this table. Keep a minimal antichain of
     sufficient component assumptions; search/resource failures never enter it. *)
  if not (List.exists (fun core -> subset core e.support) t.conflict_cores) then
    t.conflict_cores <-
      e.support :: List.filter (fun core -> not (subset e.support core)) t.conflict_cores;
  constraint_ t ~guard (Boolean.Conflict step.id) (List.map (fun id -> -(id + 1)) e.support)

let blocked t ~guard support =
  support <> []
  && List.exists
       (fun core ->
         guard ();
         subset core support)
       t.conflict_cores

let split t ~guard step =
  match step.rule with
  | Component _ -> false
  | _ ->
      let parts = components ~guard step.clause in
      if List.length parts < 2 then false
      else
        let e = Tbl.Int.find t.entries step.id in
        let ids =
          List.map
            (fun part ->
              guard ();
              name t part)
            parts
          |> List.sort_uniq compare
        in
        let index = Tbl.Int.length t.splits in
        Tbl.Int.add t.splits index (step.id, ids);
        e.split_done <- true;
        constraint_ t ~guard (Boolean.Split index)
          (List.map (fun id -> -(id + 1)) e.support @ List.map (( + ) 1) ids);
        true

(* Greedily turn unnecessary positive components off. Satisfaction counters and
   incidence lists make this linear in the stored Boolean input occurrences. *)
let minimize t ~guard model =
  let model = Array.copy model in
  let clauses = Array.of_list t.constraints_rev in
  let counts = Array.make (Array.length clauses) 0 in
  let positive = Array.make (Array.length model) []
  and negative = Array.make (Array.length model) [] in
  Array.iteri
    (fun i clause ->
      guard ();
      List.iter
        (fun literal ->
          let variable = abs literal - 1 in
          if model.(variable) = (literal > 0) then counts.(i) <- counts.(i) + 1;
          let occurrences = if literal > 0 then positive else negative in
          occurrences.(variable) <- i :: occurrences.(variable))
        clause)
    clauses;
  Array.iteri
    (fun variable enabled ->
      guard ();
      if enabled && List.for_all (fun i -> counts.(i) > 1) positive.(variable) then (
        model.(variable) <- false;
        t.minimized <- t.minimized + 1;
        List.iter (fun i -> counts.(i) <- counts.(i) - 1) positive.(variable);
        List.iter (fun i -> counts.(i) <- counts.(i) + 1) negative.(variable)))
    model;
  model

let solve t ~guard =
  t.sat_calls <- t.sat_calls + 1;
  match Boolean.solve t.solver ~guard with
  | Boolean.Unsat ->
      t.unsat <- true;
      t.dirty <- false;
      []
  | Boolean.Sat model ->
      let model = minimize t ~guard model in
      let changed = ref [] in
      Array.iteri
        (fun id value ->
          guard ();
          let previous = id < Array.length t.model && t.model.(id) in
          if value <> previous then changed := id :: !changed)
        model;
      if model <> t.model then t.model_changes <- t.model_changes + 1;
      t.model <- model;
      if !changed <> [] then t.splits_ready <- true;
      t.dirty <- false;
      List.rev !changed

let missing_components t changed =
  List.filter (fun id -> t.model.(id) && (Tbl.Int.find t.components id).node = None) changed

let roots t =
  let roots =
    Tbl.Int.fold
      (fun _ e roots ->
        if e.role <> Candidate then roots
        else e.step.id :: (match e.lock with None -> roots | Some (_, using) -> using @ roots))
      t.entries []
  in
  let roots =
    Tbl.Int.fold
      (fun _ component roots -> match component.node with None -> roots | Some id -> id :: roots)
      t.components roots
  in
  let roots = Tbl.Int.fold (fun _ (parent, _) roots -> parent :: roots) t.splits roots in
  Tbl.Int.fold
    (fun _ e roots -> if e.role = Contradiction then e.step.id :: roots else roots)
    t.entries roots

(* The ids of [roots], each passed to [push] (the same multiset), without building the list. *)
let iter_roots t push =
  Tbl.Int.iter
    (fun _ e ->
      if e.role = Candidate then (
        push e.step.id;
        match e.lock with None -> () | Some (_, using) -> List.iter push using))
    t.entries;
  Tbl.Int.iter
    (fun _ component -> match component.node with None -> () | Some id -> push id)
    t.components;
  Tbl.Int.iter (fun _ (parent, _) -> push parent) t.splits;
  Tbl.Int.iter (fun _ e -> if e.role = Contradiction then push e.step.id) t.entries

let collect t ~keep =
  Tbl.Int.filter_map_inplace (fun id e -> if keep id then Some e else None) t.entries;
  (* Keys were computed on admission. Prune IDs in place rather than rebuilding
     the same clause shapes and collision-heavy hash tables at every collection. *)
  let live _ ids =
    match List.filter (Tbl.Int.mem t.entries) ids with [] -> None | ids -> Some ids
  in
  Seen.filter_map_inplace live t.seen;
  Variants.filter_map_inplace live t.variants;
  (* Users are registered only for non-empty supports and lock conditions, and a lock is set only
     on a clause with a non-empty support: while no support was ever non-empty ([max_support] is
     0), both tables are empty and the rebuild would leave them so. *)
  if t.max_support > 0 then (
    Tbl.Int.reset t.support_users;
    Tbl.Int.reset t.lock_users;
    Tbl.Int.iter
      (fun id e ->
        if e.role = Candidate then (
          register_users t.support_users e.support id;
          Option.iter (fun (condition, _) -> register_users t.lock_users condition id) e.lock))
      t.entries)

(* [collect] after a proof sweep that dropped the nodes [dropped] (Proof.reclaim_with), when every
   entry's node was stored before it: the entries [keep] rejects are those of dropped nodes, so
   only theirs are removed (every binding, as the filter removes them), and their ids leave the
   exact and variant lists of their clauses (an id is listed only under its own clause's keys, by
   [remember]; an explanation entry is in no list). The lists of the other clauses hold no dropped
   id, so the filter would leave them as they are: the tables end binding for binding as after
   [collect], in the same bucket order (a list loses only the dropped ids, keeping its order; an
   emptied list loses its binding). *)
let collect_dropped t dropped =
  let without id ids = List.filter (fun x -> x <> id) ids in
  List.iter
    (fun id ->
      match Tbl.Int.find_all t.entries id with
      | [] -> ()
      | entries ->
          List.iter (fun _ -> Tbl.Int.remove t.entries id) entries;
          List.iter
            (fun e ->
              let p = probe e.step.clause in
              match Seen.find_opt t.seen p.exact with
              | Some ids when List.mem id ids -> (
                  (match without id ids with
                  | [] -> Seen.remove t.seen p.exact
                  | rest -> Seen.replace t.seen p.exact rest);
                  if Variants.length t.variants > 0 then
                    let k = variant_key p in
                    match Variants.find_opt t.variants k with
                    | Some ids when List.mem id ids -> (
                        match without id ids with
                        | [] -> Variants.remove t.variants k
                        | rest -> Variants.replace t.variants k rest)
                    | _ -> ())
              | _ -> ())
            entries)
    dropped;
  if t.max_support > 0 then (
    Tbl.Int.reset t.support_users;
    Tbl.Int.reset t.lock_users;
    Tbl.Int.iter
      (fun id e ->
        if e.role = Candidate then (
          register_users t.support_users e.support id;
          Option.iter (fun (condition, _) -> register_users t.lock_users condition id) e.lock))
      t.entries)

(* The incremental solver's refutation can rest on clauses it learned in earlier solves, so its
   proof grows with the whole run. [fresh] solves the same input clauses (split constraints and
   conflicts, in their order and with their origins) once more in a new solver and certifies that
   refutation instead (the same certificate format and inputs). It keeps the incremental one if
   the new solve does not refute within [fresh_budget] guard calls or does not give a smaller
   proof. *)
let fresh_budget = 1_000_000

exception Fresh_budget

(* The fresh refutation alone ([None] when the new solve does not refute within [fresh_budget]
   guard calls). *)
let fresh_refutation t =
  let proof = Boolean.proof t.solver in
  let solver = Boolean.create () in
  for _ = 1 to t.solver.variables do
    ignore (Boolean.new_variable solver : int)
  done;
  Array.iter
    (fun (node : Boolean.proof_node) ->
      match node.rule with
      | Boolean.Input origin -> ignore (Boolean.add_clause solver ~origin node.clause : int)
      | Boolean.Resolution _ -> ())
    proof.nodes;
  let calls = ref 0 in
  let guard () =
    incr calls;
    if !calls > fresh_budget then raise Fresh_budget
  in
  match Boolean.solve solver ~guard with
  | Boolean.Unsat -> (
      let again = Boolean.proof solver in
      match again.root with Some _ -> Some again | None -> None)
  | Boolean.Sat _ -> None
  | exception Fresh_budget -> None

let refutation ?(fresh = false) t =
  let proof = Boolean.proof t.solver in
  if not fresh then proof
  else
    let solver = Boolean.create () in
    for _ = 1 to t.solver.variables do
      ignore (Boolean.new_variable solver : int)
    done;
    Array.iter
      (fun (node : Boolean.proof_node) ->
        match node.rule with
        | Boolean.Input origin -> ignore (Boolean.add_clause solver ~origin node.clause : int)
        | Boolean.Resolution _ -> ())
      proof.nodes;
    let calls = ref 0 in
    let guard () =
      incr calls;
      if !calls > fresh_budget then raise Fresh_budget
    in
    match Boolean.solve solver ~guard with
    | Boolean.Unsat -> (
        let again = Boolean.proof solver in
        match again.root with
        | Some _ when Array.length again.nodes < Array.length proof.nodes -> again
        | _ -> proof)
    | Boolean.Sat _ -> proof
    | exception Fresh_budget -> proof

let certificate_of t (proof : Boolean.proof) =
  let boolean_steps =
    Array.to_list proof.nodes
    |> List.map (fun (node : Boolean.proof_node) ->
        let boolean_rule =
          match node.rule with
          | Boolean.Input (Boolean.Split index) -> Split index
          | Boolean.Input (Boolean.Conflict id) -> Conflict id
          | Boolean.Resolution { left; right; pivot } -> Boolean_resolve (left, pivot - 1, right)
        in
        { boolean_id = node.id; boolean_clause = node.clause; boolean_rule })
  in
  {
    components =
      List.init (Tbl.Int.length t.components) (fun id -> (Tbl.Int.find t.components id).clause);
    splits = List.init (Tbl.Int.length t.splits) (Tbl.Int.find t.splits);
    boolean_steps;
    boolean_root = Option.get proof.root;
  }

let certificate ?fresh t =
  if not t.unsat then invalid_arg "Avatar: no Boolean refutation";
  certificate_of t (refutation ?fresh t)

(* The certificate of the fresh refutation ([fresh_refutation]), whatever its size. *)
let fresh_certificate t =
  if not t.unsat then invalid_arg "Avatar: no Boolean refutation";
  Option.map (certificate_of t) (fresh_refutation t)
