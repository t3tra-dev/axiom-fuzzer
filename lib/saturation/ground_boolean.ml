open Wire

type statistics = {
  mutable inputs : int;
  mutable derived_inputs : int;
  mutable calls : int;
  mutable yields : int;
  mutable conflicts : int;
  mutable replayed : int;
  mutable released : int;
  mutable rebuilt : int;
  mutable solve_seconds : float;
  mutable replay_seconds : float;
}
(** An incremental propositional projection of unconditionally proved ground clauses. A satisfying
    assignment is only a scheduling result, never a model of the first-order theory. In particular
    equality atoms remain uninterpreted here; the existing ground congruence path remains
    responsible for equality.

    The context owns immutable proof leaves, not live search tickets. Retirement cannot make an
    unconditional theorem false. [roots] pins those leaves until collection rebuilds the context or
    [release] discards it. Conditional AVATAR facts are rejected even when their current branch
    happens to be enabled. *)

type t = {
  enabled : bool;
  capacity : int;
  mutable solver : Boolean.t;
  atoms : int Tbl.Atom.t;
  leaves : int Tbl.Int.t;
  seen : int Tbl.Clause.t;  (** the clause of each leaf, to its step id *)
  codes : int array Tbl.Int.t;
      (** per leaf step id, the literals its [note] gave [Boolean.add_clause] (in clause order, in
          the current numbering of [atoms]); read by [collect]'s rebuild only *)
  clauses : clause Tbl.Int.t;  (** per leaf step id, its clause *)
  mutable logged : int list;
      (** leaf step ids passed to [forget] (deactivated) since the last [collect_logged] *)
  mutable pending : bool;
      (** [collect_logged] dropped dead leaves and the rebuild is due: [codes], [clauses] and [seen]
          hold the surviving leaves, [solver], [atoms] and [leaves] are those of before until
          [materialize] (see [collect_logged]) *)
  mutable deferred : step list;
      (** leaves noted while [pending], newest first, that [materialize] adds after the rebuild (the
          ones still in [deferred_ids]); they are in [seen] and [clauses], not in [codes] *)
  deferred_ids : unit Tbl.Int.t;
  mutable deferred_literals : int;  (** the literals of [deferred], for [note]'s size bound *)
  mutable top : int;  (** the largest step id that became a leaf *)
  emitted : unit Tbl.Int.t;
  mutable dirty : bool;
  mutable exhausted : bool;
  mutable running : bool;
  mutable quantum : int;
  statistics : statistics;
}

exception Yield
exception Capacity

let create ?(enabled = true) ~capacity () =
  {
    enabled;
    capacity;
    solver = Boolean.create ();
    atoms = Tbl.Atom.create 128;
    leaves = Tbl.Int.create 128;
    seen = Tbl.Clause.create 128;
    codes = Tbl.Int.create 128;
    clauses = Tbl.Int.create 128;
    logged = [];
    pending = false;
    deferred = [];
    deferred_ids = Tbl.Int.create 16;
    deferred_literals = 0;
    top = -1;
    emitted = Tbl.Int.create 128;
    dirty = false;
    exhausted = false;
    running = false;
    quantum = 0;
    statistics =
      {
        inputs = 0;
        derived_inputs = 0;
        calls = 0;
        yields = 0;
        conflicts = 0;
        replayed = 0;
        released = 0;
        rebuilt = 0;
        solve_seconds = 0.;
        replay_seconds = 0.;
      };
  }

(* [reserve]: start the new context with room for as much as the old one held, which a rebuild
   from its surviving leaves never exceeds (no growth by doubling on every rebuild). *)
let clear ?(reserve = false) t =
  let old = t.solver in
  t.solver <-
    (if reserve then
       Boolean.create ~variables:old.variables ~nodes:old.node_count ~clauses:old.clause_count ()
     else Boolean.create ());
  Tbl.Atom.clear t.atoms;
  Tbl.Int.clear t.leaves;
  Tbl.Clause.clear t.seen;
  Tbl.Int.clear t.codes;
  Tbl.Int.clear t.clauses;
  t.logged <- [];
  t.pending <- false;
  t.deferred <- [];
  Tbl.Int.clear t.deferred_ids;
  t.deferred_literals <- 0;
  t.dirty <- false;
  t.quantum <- 0

let release t =
  clear t;
  t.exhausted <- true;
  t.statistics.released <- t.statistics.released + 1

(* The rebuild from the surviving leaves [inputs] (ascending ids, every one in [codes]), without
   noting them again. Each input already passed every test of [note] when it became a leaf
   (clauses are immutable, and leaves have distinct clauses), so a fresh [note] would test
   nothing that can fail but the capacity. The variables of a fresh context are numbered in order
   of first occurrence over the inputs in id order, which is a renumbering of the old variables
   (an atom has one variable): [renumber] maps each old variable to its new one, the inputs are
   added to the new solver with their stored literals renumbered, and [atoms] and [codes] are
   filtered in place to the surviving atoms (renumbered) and leaves, without hashing an atom
   again. [atoms] is only looked up and counted, so its bucket order is not observable. The new
   solver is built by the same [Boolean] calls in the same order as [collect_reference] makes
   them, so it is the same solver; [leaves] is rebuilt the same way, and the capacity is tested at
   the same points with the same sizes (nodes added plus atoms numbered so far), so a context
   that would be released is released. *)
let rebuild t inputs ~keep =
  let old = t.solver in
  let solver =
    Boolean.create ~variables:old.variables ~nodes:old.node_count ~clauses:old.clause_count ()
  in
  let renumber = Array.make (old.variables + 1) 0 in
  let numbered = ref 0 and added = ref 0 in
  Tbl.Int.clear t.leaves;
  t.solver <- solver;
  t.quantum <- 0;
  try
    List.iter
      (fun id ->
        let literals = Tbl.Int.find t.codes id in
        Array.iteri
          (fun k literal ->
            if !added + !numbered >= t.capacity then raise Capacity;
            let v = abs literal in
            if renumber.(v) = 0 then (
              renumber.(v) <- Boolean.new_variable solver + 1;
              incr numbered);
            literals.(k) <- (if literal > 0 then renumber.(v) else -renumber.(v)))
          literals;
        if !added + !numbered >= t.capacity then raise Capacity;
        let node = Boolean.add_clause solver ~origin:(Boolean.Split id) (Array.to_list literals) in
        incr added;
        Tbl.Int.add t.leaves node id)
      inputs;
    Tbl.Atom.filter_map_inplace
      (fun _ v ->
        let n = if v <= old.variables then renumber.(v) else 0 in
        if n = 0 then None else Some n)
      t.atoms;
    Tbl.Int.filter_map_inplace (fun id c -> if keep id then Some c else None) t.codes;
    Tbl.Int.filter_map_inplace (fun id c -> if keep id then Some c else None) t.clauses;
    t.dirty <- inputs <> []
  with Capacity -> release t

let atom t atom =
  match Tbl.Atom.find_opt t.atoms atom with
  | Some id -> id
  | None ->
      let id = Boolean.new_variable t.solver + 1 in
      Tbl.Atom.add t.atoms atom id;
      id

let encode t literal =
  let id = Tbl.Atom.find t.atoms literal.atom in
  if literal.positive then id else -id

(* The size of the solver as it stands (never pending). *)
let current_size t = Boolean.proof_size t.solver + Tbl.Atom.length t.atoms

(* [note]'s addition of a leaf to the solver after its tests (its guard calls made, or not:
   [guard]), as [note] makes it; [seen] and [clauses] are the caller's. *)
let install t ~guard (step : step) =
  List.iter
    (fun l ->
      guard ();
      if current_size t >= t.capacity then raise Capacity;
      ignore (atom t l.atom))
    step.clause;
  if current_size t >= t.capacity then raise Capacity;
  let literals = List.map (encode t) step.clause in
  let id = Boolean.add_clause t.solver ~origin:(Boolean.Split step.id) literals in
  Tbl.Int.add t.leaves id step.id;
  Tbl.Int.replace t.codes step.id (Array.of_list literals);
  t.dirty <- true

(* The rebuild [collect_logged] deferred, from the leaves it kept, then the leaves [note] deferred
   meanwhile (still alive), added in the order they were noted: each was noted with a larger id
   than every leaf of the rebuild, so this is the solver the rebuild at their [note] and their
   additions would have made. Their size tests passed when they were noted (see [note]). *)
let materialize t =
  if t.pending then (
    t.pending <- false;
    let inputs = List.sort Int.compare (Tbl.Int.fold (fun id _ ids -> id :: ids) t.codes []) in
    rebuild t inputs ~keep:(fun _ -> true);
    let deferred = List.rev t.deferred in
    t.deferred <- [];
    t.deferred_literals <- 0;
    (try
       List.iter
         (fun (s : step) ->
           if Tbl.Int.mem t.deferred_ids s.id then install t ~guard:(fun () -> ()) s)
         deferred
     with Capacity -> release t);
    Tbl.Int.clear t.deferred_ids)

let size t =
  materialize t;
  current_size t

(* The solver's proof size as the rebuild leaves it: one node per surviving leaf. *)
let proof_size t =
  if t.pending then Tbl.Int.length t.codes + Tbl.Int.length t.deferred_ids
  else Boolean.proof_size t.solver

let roots t =
  if t.pending then
    Tbl.Int.fold
      (fun id _ ids -> id :: ids)
      t.deferred_ids
      (Tbl.Int.fold (fun id _ ids -> id :: ids) t.codes [])
  else Tbl.Int.fold (fun _ id ids -> id :: ids) t.leaves []

let iter_roots t push =
  if t.pending then (
    Tbl.Int.iter (fun id _ -> push id) t.codes;
    Tbl.Int.iter (fun id () -> push id) t.deferred_ids)
  else Tbl.Int.iter (fun _ id -> push id) t.leaves

let has_work t =
  t.enabled && (not t.exhausted)
  && if t.pending then Tbl.Int.length t.codes + Tbl.Int.length t.deferred_ids > 0 else t.dirty

(* A deactivated clause: if it is a leaf, the next [collect_logged] tests it. *)
let forget t id =
  if Tbl.Int.mem t.codes id || Tbl.Int.mem t.deferred_ids id then t.logged <- id :: t.logged

(* Ordinary search may discard the optional context before taking more space.
   While a solve/lift holds its arrays and atom projection, unwind first instead
   of clearing those structures underneath its next proof lookup. *)
let enforce_space t ~available =
  if proof_size t > 0 && proof_size t >= available then
    if t.running then raise Capacity else release t

let with_running t f =
  let previous = t.running in
  t.running <- true;
  Fun.protect ~finally:(fun () -> t.running <- previous) f

let ground ~guard clause =
  let rec term = function
    | V _ -> false
    | Fn (_, ts) ->
        guard ();
        List.for_all term ts
  in
  List.for_all (fun l -> List.for_all term (Clause.atom_terms l.atom)) clause

(* A new leaf. While a rebuild is pending, the leaf is deferred to it ([materialize]) instead of
   forcing it now, when its id is larger than every leaf's and the context cannot reach its
   capacity in the meantime: the rebuilt solver has one node per leaf and at most the atoms the
   old one numbered plus the literals of the deferred leaves, so a bound below the capacity means
   no size test of the rebuild or of the additions can fail. Its guard calls are made now, one per
   literal as the addition makes them; if one raises, the solver is first brought to where the
   addition would have stopped (rebuilt, the atoms of the earlier literals numbered). *)
let note ?(count = true) t ~guard ~support (step : step) =
  with_running t (fun () ->
      try
        if
          t.enabled && (not t.exhausted) && support = [] && step.clause <> []
          && ground ~guard step.clause
          && (match step.rule with Component _ -> false | _ -> true)
          && not (Tbl.Clause.mem t.seen step.clause)
        then (
          let n = List.length step.clause in
          if
            t.pending && step.id > t.top
            && Tbl.Int.length t.codes + Tbl.Int.length t.deferred_ids + 1 + Tbl.Atom.length t.atoms
               + t.deferred_literals + n
               < t.capacity
          then (
            List.iteri
              (fun k _ ->
                try guard ()
                with e ->
                  materialize t;
                  List.iteri
                    (fun j (l : literal) -> if j < k then ignore (atom t l.atom))
                    step.clause;
                  raise e)
              step.clause;
            t.deferred <- step :: t.deferred;
            Tbl.Int.replace t.deferred_ids step.id ();
            t.deferred_literals <- t.deferred_literals + n)
          else (
            materialize t;
            install t ~guard step);
          Tbl.Clause.add t.seen step.clause step.id;
          Tbl.Int.replace t.clauses step.id step.clause;
          if step.id > t.top then t.top <- step.id;
          if count then (
            t.statistics.inputs <- t.statistics.inputs + 1;
            match step.rule with
            | Input _ -> ()
            | _ -> t.statistics.derived_inputs <- t.statistics.derived_inputs + 1))
      with Capacity -> release t)

(* Search retirement does not invalidate an unconditional theorem. Nevertheless
   keep no private cache alive merely to defeat ordinary proof collection. A GC
   boundary drops every learned clause and explanation when any leaf is retired,
   then rebuilds from the surviving exact inputs before Proof.reclaim runs. *)
(* The rebuild as [note] performs it: a cleared context (with the old one's capacity), then every
   surviving input noted again in id order. The reference of [collect] in the unit tests. *)
let collect_reference t ~keep ~get =
  materialize t;
  let ids = roots t in
  if List.exists (fun id -> not (keep id)) ids then (
    let inputs = ids |> List.filter keep |> List.sort_uniq Int.compare |> List.map get in
    clear ~reserve:true t;
    t.statistics.rebuilt <- t.statistics.rebuilt + 1;
    List.iter (note ~count:false t ~guard:(fun () -> ()) ~support:[]) inputs)

(* The rebuild after a leaf died, at once ([collect_logged] defers it); every leaf is tested
   with [keep]. *)
let collect t ~keep ~get:_ =
  materialize t;
  let ids = roots t in
  if List.exists (fun id -> not (keep id)) ids then (
    let inputs = ids |> List.filter keep |> List.sort_uniq Int.compare in
    t.statistics.rebuilt <- t.statistics.rebuilt + 1;
    Tbl.Clause.filter_map_inplace (fun _ id -> if keep id then Some id else None) t.seen;
    rebuild t inputs ~keep)

(* The engine's collection. A leaf is dead when its clause has left the retained index, which
   happens only by a deactivation, and every deactivation of a leaf was passed to [forget]: the
   dead leaves are the logged ones that fail [keep], so no other leaf is tested. Their clauses
   leave [seen] and their entries [codes] and [clauses] now, as [collect]'s rebuild would leave
   them; the rebuild itself waits until the solver, its atoms or its leaf numbering is read
   ([materialize]: by [note] when it adds a leaf, [size], [advance], [collect], [Engine.seal]).
   Until then [proof_size], [roots] and [has_work] answer as after the rebuild (one node per
   surviving leaf; [quantum] is reset by the rebuild and read only by [advance]). Deferring
   changes nothing: a second collection's rebuild from fewer survivors gives the context a
   rebuild from those survivors gives, since the fresh numbering depends only on the surviving
   leaves in id order, and the room reserved at creation is not observable (Boolean's unit test).
   [rebuilt] counts the collections that dropped a leaf, as before. *)
let collect_logged t ~keep =
  let logged = t.logged in
  t.logged <- [];
  let dead =
    List.filter
      (fun id -> (Tbl.Int.mem t.codes id || Tbl.Int.mem t.deferred_ids id) && not (keep id))
      logged
    |> List.sort_uniq Int.compare
  in
  if dead <> [] then (
    t.statistics.rebuilt <- t.statistics.rebuilt + 1;
    List.iter
      (fun id ->
        Tbl.Clause.remove t.seen (Tbl.Int.find t.clauses id);
        Tbl.Int.remove t.codes id;
        Tbl.Int.remove t.deferred_ids id;
        Tbl.Int.remove t.clauses id)
      dead;
    t.pending <- true)

(* Lift a Boolean proof through exact, caller-owned first-order leaves. Each
   normalized node is projected once; pivot positions are cached in that node's
   literal order. The caller owns dependency checks and final conflict handling. *)
let lift_proof ~guard ~(proof : Boolean.proof) ~encode ~leaf ~record ~on_record =
  let root =
    match proof.root with
    | Some id -> id
    | None -> invalid_arg "Ground_boolean: missing Boolean refutation"
  in
  let needed = Tbl.Int.create 128 and pending = Stack.create () in
  Stack.push root pending;
  while not (Stack.is_empty pending) do
    guard ();
    let id = Stack.pop pending in
    if not (Tbl.Int.mem needed id) then (
      Tbl.Int.add needed id ();
      match proof.nodes.(id).rule with
      | Boolean.Input _ -> ()
      | Resolution { left; right; _ } ->
          Stack.push left pending;
          Stack.push right pending)
  done;
  let lifted = Tbl.Int.create (Tbl.Int.length needed) in
  let project (step : step) expected =
    if not (ground ~guard step.clause) then
      invalid_arg "Ground_boolean: nonground proof leaf or conclusion";
    let positions = Tbl.Int.create (List.length step.clause) in
    let projected =
      List.mapi
        (fun index literal ->
          guard ();
          let value = encode literal in
          if value = 0 || Tbl.Int.mem positions value then
            invalid_arg "Ground_boolean: noninjective clause projection";
          Tbl.Int.add positions value index;
          value)
        step.clause
      |> List.sort Int.compare
    in
    if projected <> expected then
      invalid_arg "Ground_boolean: lifted clause does not match Boolean explanation";
    (step, positions)
  in
  let merge left right =
    let rec loop reversed left right =
      match (left, right) with
      | [], rest | rest, [] -> List.rev_append reversed rest
      | l :: ls, r :: rs ->
          guard ();
          let order = compare l r in
          if order = 0 then loop (l :: reversed) ls rs
          else if order < 0 then loop (l :: reversed) ls right
          else loop (r :: reversed) left rs
    in
    loop [] left right
  in
  let normalized clause =
    let rec sorted = function
      | [] | [ _ ] -> true
      | a :: (b :: _ as rest) ->
          guard ();
          compare a b < 0 && sorted rest
    in
    sorted clause
  in
  Array.iter
    (fun (node : Boolean.proof_node) ->
      if Tbl.Int.mem needed node.id then (
        guard ();
        let step =
          match node.rule with
          | Boolean.Input _ -> leaf node
          | Boolean.Resolution { left; right; pivot } ->
              let l, lp = Tbl.Int.find lifted left and r, rp = Tbl.Int.find lifted right in
              let sign = if Tbl.Int.mem lp pivot then pivot else -pivot in
              let find wanted positions =
                match Tbl.Int.find_opt positions wanted with
                | Some i -> i
                | None -> invalid_arg "Ground_boolean: missing resolution pivot"
              in
              let i = find sign lp and j = find (-sign) rp in
              let clause = merge (Clause.remove i l.clause) (Clause.remove j r.clause) in
              let step = record clause (Resolve (l.id, i, r.id, j, [])) in
              on_record step;
              step
        in
        if not (normalized step.clause) then
          invalid_arg "Ground_boolean: noncanonical lifted clause";
        Tbl.Int.add lifted node.id (project step node.clause)))
    proof.nodes;
  let step, _ = Tbl.Int.find lifted root in
  if step.clause <> [] then invalid_arg "Ground_boolean: nonempty refutation";
  step

let lift t ~guard ~get ~record =
  let leaf (node : Boolean.proof_node) =
    match node.rule with
    | Boolean.Input (Boolean.Split id) ->
        if Tbl.Int.find t.leaves node.id <> id then
          invalid_arg "Ground_boolean: input ownership changed";
        get id
    | _ -> invalid_arg "Ground_boolean: conditional leaf"
  in
  lift_proof ~guard ~proof:(Boolean.proof t.solver) ~encode:(encode t) ~leaf ~record
    ~on_record:(fun step ->
      Tbl.Int.replace t.emitted step.id ();
      t.statistics.replayed <- t.statistics.replayed + 1)

let advance t ~guard ~get ~record =
  if not (has_work t) then None
  else (
    materialize t;
    with_running t (fun () ->
        t.statistics.calls <- t.statistics.calls + 1;
        (* Work is bounded per scheduled turn. Learned clauses and saved phases
       survive a yield; the initial quantum scales with this context's size. *)
        if t.quantum = 0 then t.quantum <- max 1 (Tbl.Int.length t.leaves + Tbl.Atom.length t.atoms);
        let remaining = ref t.quantum in
        let bounded () =
          guard ();
          if size t >= t.capacity then raise Capacity;
          if !remaining = 0 then raise Yield;
          decr remaining
        in
        let started = Telemetry.now () in
        try
          let result =
            Fun.protect
              ~finally:(fun () ->
                t.statistics.solve_seconds <-
                  t.statistics.solve_seconds +. Telemetry.now () -. started)
              (fun () -> Boolean.solve t.solver ~guard:bounded)
          in
          if size t >= t.capacity then raise Capacity;
          match result with
          | Sat _ ->
              t.dirty <- false;
              t.quantum <- 0;
              None
          | Unsat ->
              t.statistics.conflicts <- t.statistics.conflicts + 1;
              let started = Telemetry.now () in
              let step =
                Fun.protect
                  ~finally:(fun () ->
                    t.statistics.replay_seconds <-
                      t.statistics.replay_seconds +. Telemetry.now () -. started)
                  (fun () -> lift t ~guard ~get ~record)
              in
              t.dirty <- false;
              Some step
        with
        | Yield ->
            t.statistics.yields <- t.statistics.yields + 1;
            t.quantum <- (if t.quantum >= t.capacity / 2 then t.capacity else 2 * t.quantum);
            None
        | Capacity ->
            release t;
            None))

let final_steps t (certificate : certificate) =
  List.fold_left
    (fun n (s : step) -> if Tbl.Int.mem t.emitted s.id then n + 1 else n)
    0 certificate.steps
