(** Incremental CDCL with an explicit binary-resolution proof DAG.

    Variables are allocated by [new_variable] and numbered from zero. Literals are signed
    [variable + 1]; zero and unallocated variables are rejected. [add_clause] keeps every input as a
    proof leaf, including tautologies, but tautologies are not installed in the solver. Duplicate
    literals are removed.

    Clauses, learned clauses, watches and saved phases survive [solve]. Each call starts its
    assignment at level zero. A guard may raise any exception; it is propagated unchanged, and the
    next call repairs watches if necessary. No solver clause is deleted, so every reason and proof
    parent remains valid.

    Resolution pivots are positive literal numbers (not zero-based variables). Either parent may
    contain the positive occurrence. Proof clauses are sorted sets of literals; watch positions
    never modify those immutable clauses. *)

type literal = int
type origin = Split of int | Conflict of int
type rule = Input of origin | Resolution of { left : int; right : int; pivot : int }
type proof_node = { id : int; clause : literal list; rule : rule }
type proof = { nodes : proof_node array; root : int option }
type result = Sat of bool array | Unsat

type statistics = {
  decisions : int;
  propagations : int;
  conflicts : int;
  learned_clauses : int;
  nonchronological_backjumps : int;
}

type vector = { mutable data : int array; mutable size : int }

let vector () = { data = [||]; size = 0 }

let push v x =
  if v.size = Array.length v.data then (
    let grown = Array.make (max 4 (2 * v.size)) 0 in
    Array.blit v.data 0 grown 0 v.size;
    v.data <- grown);
  v.data.(v.size) <- x;
  v.size <- v.size + 1

type solver_clause = {
  literals : literal array;
  proof_id : int;
  mutable first : int;
  mutable second : int;
}

let dummy_clause = { literals = [||]; proof_id = -1; first = 0; second = 0 }
let dummy_node = { id = -1; clause = []; rule = Input (Split (-1)) }

type t = {
  mutable variables : int;
  mutable values : int array;
  mutable levels : int array;
  mutable reasons : int array;
  mutable phases : bool array;
  mutable occurs : bool array;
  mutable activity : float array;
  mutable increment : float;
  mutable heap : int array;
      (** The decision order: a binary heap of variables, the greatest [activity] first and the
          lower variable first among equal ones ([before]). It holds every unassigned variable that
          occurs in a clause, and possibly assigned ones, which [decide] drops. *)
  mutable heap_size : int;
  mutable heap_position : int array;  (** a variable's index in [heap], or [-1] *)
  mutable free : int;  (** the unassigned variables that occur in a clause *)
  mutable reference : bool;  (** [decide] by the scan [decide_reference] (tests) *)
  mutable marks : int array;
  mutable stamp : int;
  mutable watches : vector array;
  mutable watches_dirty : bool;
  mutable clauses : solver_clause array;
  mutable clause_count : int;
  units : vector;
  trail : vector;
  limits : vector;
  mutable next_propagation : int;
  mutable nodes : proof_node array;
  mutable node_count : int;
  mutable root : int option;
  mutable solving : bool;
  mutable decisions : int;
  mutable propagations : int;
  mutable conflicts : int;
  mutable learned_clauses : int;
  mutable nonchronological_backjumps : int;
}

(* [variables], [nodes] and [clauses] only reserve room (a rebuild knows how large the context it
   replaces was): the arrays hold the same initial values that growing them would give, and
   nothing reads past the counts, so a solver behaves the same whatever room it starts with. *)
let create ?(variables = 0) ?(nodes = 0) ?(clauses = 0) () =
  {
    variables = 0;
    values = Array.make variables 0;
    levels = Array.make variables 0;
    reasons = Array.make variables (-1);
    phases = Array.make variables false;
    occurs = Array.make variables false;
    activity = Array.make variables 0.;
    increment = 1.;
    heap = Array.make variables 0;
    heap_size = 0;
    heap_position = Array.make variables (-1);
    free = 0;
    reference = false;
    marks = Array.make variables 0;
    stamp = 0;
    watches = Array.init (2 * variables) (fun _ -> vector ());
    watches_dirty = false;
    clauses = Array.make clauses dummy_clause;
    clause_count = 0;
    units = vector ();
    trail = vector ();
    limits = vector ();
    next_propagation = 0;
    nodes = Array.make nodes dummy_node;
    node_count = 0;
    root = None;
    solving = false;
    decisions = 0;
    propagations = 0;
    conflicts = 0;
    learned_clauses = 0;
    nonchronological_backjumps = 0;
  }

let require_idle t =
  if t.solving then invalid_arg "Boolean: mutation or recursive solve during solve"

let extend array n initial =
  let grown = Array.make n initial in
  Array.blit array 0 grown 0 (Array.length array);
  grown

let new_variable t =
  require_idle t;
  let id = t.variables in
  if id >= (max_int / 2) - 1 then invalid_arg "Boolean: too many variables";
  if id = Array.length t.values then (
    let capacity = max 8 (2 * id) in
    t.values <- extend t.values capacity 0;
    t.levels <- extend t.levels capacity 0;
    t.reasons <- extend t.reasons capacity (-1);
    t.phases <- extend t.phases capacity false;
    t.occurs <- extend t.occurs capacity false;
    t.activity <- extend t.activity capacity 0.;
    t.heap <- extend t.heap capacity 0;
    t.heap_position <- extend t.heap_position capacity (-1);
    t.marks <- extend t.marks capacity 0;
    let watches = Array.init (2 * capacity) (fun _ -> vector ()) in
    Array.blit t.watches 0 watches 0 (Array.length t.watches);
    t.watches <- watches);
  t.variables <- id + 1;
  id

let variable lit = abs lit - 1
let watch_index lit = (2 * variable lit) + if lit < 0 then 1 else 0

let validate_literal t lit =
  if lit = 0 || lit = min_int || abs lit > t.variables then
    invalid_arg "Boolean: literal is zero or refers to an unallocated variable"

(* {2 The decision heap} *)

let[@inline] before t a b =
  let x = Array.unsafe_get t.activity a and y = Array.unsafe_get t.activity b in
  x > y || (Float.equal x y && a < b)

let heap_place t i v =
  t.heap.(i) <- v;
  t.heap_position.(v) <- i

let rec sift_up t i v =
  if i = 0 then heap_place t 0 v
  else
    let parent = (i - 1) / 2 in
    let p = t.heap.(parent) in
    if before t v p then (
      heap_place t i p;
      sift_up t parent v)
    else heap_place t i v

let rec sift_down t i v =
  let left = (2 * i) + 1 in
  if left >= t.heap_size then heap_place t i v
  else
    let right = left + 1 in
    let child =
      if right < t.heap_size && before t t.heap.(right) t.heap.(left) then right else left
    in
    let c = t.heap.(child) in
    if before t c v then (
      heap_place t i c;
      sift_down t child v)
    else heap_place t i v

let heap_insert t v =
  if t.heap_position.(v) < 0 then (
    let i = t.heap_size in
    t.heap_size <- i + 1;
    sift_up t i v)

(* The greatest variable leaves the heap. *)
let heap_pop t =
  let top = t.heap.(0) in
  t.heap_position.(top) <- -1;
  let size = t.heap_size - 1 in
  t.heap_size <- size;
  if size > 0 then sift_down t 0 t.heap.(size);
  top

(* After the activities were all scaled, which may turn two of them equal. *)
let heap_rebuild t =
  for i = (t.heap_size / 2) - 1 downto 0 do
    sift_down t i t.heap.(i)
  done

(* [v] is unassigned: it is a candidate again if it occurs. *)
let[@inline] release_variable t v =
  if t.occurs.(v) then (
    t.free <- t.free + 1;
    heap_insert t v)

(* Every variable is unassigned: the heap is made again from the occurring ones, in linear time. *)
let heap_reset t =
  let size = ref 0 in
  for v = 0 to t.variables - 1 do
    if t.occurs.(v) then (
      t.heap.(!size) <- v;
      t.heap_position.(v) <- !size;
      incr size)
    else t.heap_position.(v) <- -1
  done;
  t.heap_size <- !size;
  t.free <- !size;
  heap_rebuild t

let append_node t clause rule =
  let id = t.node_count in
  if id = Array.length t.nodes then t.nodes <- extend t.nodes (max 16 (2 * id)) dummy_node;
  t.nodes.(id) <- { id; clause; rule };
  t.node_count <- id + 1;
  id

let attach t id cl =
  push t.watches.(watch_index cl.literals.(cl.first)) id;
  push t.watches.(watch_index cl.literals.(cl.second)) id

let install_clause t proof_id literals ~first ~second =
  let id = t.clause_count in
  if id = Array.length t.clauses then t.clauses <- extend t.clauses (max 16 (2 * id)) dummy_clause;
  let cl = { literals; proof_id; first; second } in
  t.clauses.(id) <- cl;
  t.clause_count <- id + 1;
  Array.iter
    (fun lit ->
      let v = variable lit in
      if not t.occurs.(v) then (
        t.occurs.(v) <- true;
        if t.values.(v) = 0 then (
          t.free <- t.free + 1;
          heap_insert t v)))
    literals;
  (match Array.length literals with
  | 0 -> t.root <- Some proof_id
  | 1 -> push t.units id
  | _ -> attach t id cl);
  id

let tautological literals =
  let seen = Tbl.Int.create (List.length literals) in
  List.exists
    (fun lit ->
      if Tbl.Int.mem seen (-lit) then true
      else (
        Tbl.Int.add seen lit ();
        false))
    literals

let add_clause t ~origin literals =
  require_idle t;
  List.iter (validate_literal t) literals;
  let normalized = List.sort_uniq Int.compare literals in
  let proof_id = append_node t normalized (Input origin) in
  if not (tautological normalized) then
    ignore
      (install_clause t proof_id (Array.of_list normalized) ~first:0
         ~second:(if List.length normalized > 1 then 1 else 0));
  proof_id

let proof (t : t) : proof = { nodes = Array.sub t.nodes 0 t.node_count; root = t.root }
let proof_size t = t.node_count

let statistics (t : t) : statistics =
  {
    decisions = t.decisions;
    propagations = t.propagations;
    conflicts = t.conflicts;
    learned_clauses = t.learned_clauses;
    nonchronological_backjumps = t.nonchronological_backjumps;
  }

let value t lit = if lit > 0 then t.values.(variable lit) else -t.values.(variable lit)

let enqueue t lit reason =
  match value t lit with
  | 1 -> true
  | -1 -> false
  | _ ->
      let v = variable lit in
      if t.occurs.(v) then t.free <- t.free - 1;
      t.values.(v) <- (if lit > 0 then 1 else -1);
      t.levels.(v) <- t.limits.size;
      t.reasons.(v) <- reason;
      t.phases.(v) <- lit > 0;
      push t.trail lit;
      true

let clear_assignment t =
  for i = 0 to t.trail.size - 1 do
    let v = variable t.trail.data.(i) in
    t.values.(v) <- 0;
    t.levels.(v) <- 0;
    t.reasons.(v) <- -1
  done;
  heap_reset t;
  t.trail.size <- 0;
  t.limits.size <- 0;
  t.next_propagation <- 0

let rebuild_watches t ~guard =
  Array.iter (fun watch -> watch.size <- 0) t.watches;
  for id = 0 to t.clause_count - 1 do
    guard ();
    let cl = t.clauses.(id) in
    if Array.length cl.literals >= 2 then (
      cl.first <- 0;
      cl.second <- 1;
      attach t id cl)
  done;
  t.watches_dirty <- false

(** Move a falsified watch to a nonfalse literal, or propagate its partner. Watch vectors use swap
    removal; nothing is copied for satisfied clauses. *)
let propagate t ~guard =
  let conflict = ref (-1) in
  while !conflict < 0 && t.next_propagation < t.trail.size do
    guard ();
    let false_lit = -t.trail.data.(t.next_propagation) in
    t.next_propagation <- t.next_propagation + 1;
    t.propagations <- t.propagations + 1;
    let watched = t.watches.(watch_index false_lit) in
    let i = ref 0 in
    while !conflict < 0 && !i < watched.size do
      guard ();
      let id = watched.data.(!i) in
      let cl = t.clauses.(id) in
      let moving_first = cl.literals.(cl.first) = false_lit in
      let other_pos = if moving_first then cl.second else cl.first in
      let other = cl.literals.(other_pos) in
      if value t other = 1 then incr i
      else
        let replacement = ref (-1) in
        let k = ref 0 in
        while !replacement < 0 && !k < Array.length cl.literals do
          if !k land 255 = 0 then guard ();
          if !k <> other_pos && value t cl.literals.(!k) >= 0 then replacement := !k;
          incr k
        done;
        if !replacement >= 0 then (
          if moving_first then cl.first <- !replacement else cl.second <- !replacement;
          watched.size <- watched.size - 1;
          watched.data.(!i) <- watched.data.(watched.size);
          push t.watches.(watch_index cl.literals.(!replacement)) id)
        else (
          incr i;
          if not (enqueue t other id) then conflict := id)
    done
  done;
  !conflict

let bump t v =
  t.activity.(v) <- t.activity.(v) +. t.increment;
  let i = t.heap_position.(v) in
  if i >= 0 then sift_up t i v;
  if t.activity.(v) > 1e100 then (
    for i = 0 to t.variables - 1 do
      t.activity.(i) <- t.activity.(i) *. 1e-100
    done;
    t.increment <- t.increment *. 1e-100;
    heap_rebuild t)

let mark_clause t literals =
  if t.stamp = max_int then (
    Array.fill t.marks 0 (Array.length t.marks) 0;
    t.stamp <- 0);
  t.stamp <- t.stamp + 1;
  List.iter (fun lit -> t.marks.(variable lit) <- t.stamp) literals

(** Exact set resolution, without subsumption or silent root-level deletion. *)
let resolve (t : t) ~guard left right pivot =
  let a = t.nodes.(left).clause and b = t.nodes.(right).clause in
  if not ((List.mem pivot a && List.mem (-pivot) b) || (List.mem (-pivot) a && List.mem pivot b))
  then failwith "Boolean: resolution parents do not have opposite pivots";
  let rec merge acc a b steps =
    if steps land 255 = 0 then guard ();
    match (a, b) with
    | x :: xs, _ when abs x = pivot -> merge acc xs b (steps + 1)
    | _, y :: ys when abs y = pivot -> merge acc a ys (steps + 1)
    | [], [] -> List.rev acc
    | x :: xs, [] -> merge (x :: acc) xs [] (steps + 1)
    | [], y :: ys -> merge (y :: acc) [] ys (steps + 1)
    | x :: xs, y :: ys ->
        if x = y then merge (x :: acc) xs ys (steps + 1)
        else if x < y then merge (x :: acc) xs b (steps + 1)
        else merge (y :: acc) a ys (steps + 1)
  in
  let clause = merge [] a b 0 in
  append_node t clause (Resolution { left; right; pivot })

let latest_marked t cursor ~guard =
  while !cursor >= 0 && t.marks.(variable t.trail.data.(!cursor)) <> t.stamp do
    if !cursor land 255 = 0 then guard ();
    decr cursor
  done;
  if !cursor < 0 then failwith "Boolean: conflict clause is not falsified on the trail";
  let v = variable t.trail.data.(!cursor) in
  decr cursor;
  v

(** Root assignments have reasons too. Resolve them out to obtain a genuine empty clause, rather
    than claiming an empty clause from a nonempty conflict. *)
let refute_root t ~guard conflict =
  let current = ref t.clauses.(conflict).proof_id in
  let cursor = ref (t.trail.size - 1) in
  while t.nodes.(!current).clause <> [] do
    guard ();
    mark_clause t t.nodes.(!current).clause;
    let v = latest_marked t cursor ~guard in
    let reason = t.reasons.(v) in
    if reason < 0 || t.levels.(v) <> 0 then failwith "Boolean: unexplained root assignment";
    current := resolve t ~guard !current t.clauses.(reason).proof_id (v + 1)
  done;
  t.root <- Some !current

(** First-UIP analysis. Each substitution of a reason is also one proof node. *)
let analyze t ~guard conflict =
  let current = ref t.clauses.(conflict).proof_id in
  let cursor = ref (t.trail.size - 1) in
  let level = t.limits.size in
  let count = ref 0 in
  let mark () =
    count := 0;
    let clause = t.nodes.(!current).clause in
    mark_clause t clause;
    List.iter
      (fun lit ->
        let v = variable lit in
        bump t v;
        if t.levels.(v) = level then incr count)
      clause
  in
  mark ();
  while !count > 1 do
    guard ();
    let v = latest_marked t cursor ~guard in
    let reason = t.reasons.(v) in
    if reason < 0 || t.levels.(v) <> level then
      failwith "Boolean: a decision was reached before the first UIP";
    current := resolve t ~guard !current t.clauses.(reason).proof_id (v + 1);
    mark ()
  done;
  if !count <> 1 then failwith "Boolean: conflict has no current-level literal";
  let asserting = ref 0 and backjump = ref 0 in
  List.iter
    (fun lit ->
      let lit_level = t.levels.(variable lit) in
      if lit_level = level then asserting := lit else backjump := max !backjump lit_level)
    t.nodes.(!current).clause;
  t.increment <- t.increment /. 0.95;
  (!current, !asserting, !backjump)

let backtrack t level =
  let length = t.limits.data.(level) in
  for i = length to t.trail.size - 1 do
    let v = variable t.trail.data.(i) in
    t.values.(v) <- 0;
    t.levels.(v) <- 0;
    t.reasons.(v) <- -1;
    release_variable t v
  done;
  t.trail.size <- length;
  t.limits.size <- level;
  t.next_propagation <- min t.next_propagation length

let learn t ~guard conflict =
  let proof_id, asserting, level = analyze t ~guard conflict in
  let literals = Array.of_list t.nodes.(proof_id).clause in
  let first = ref 0 and second = ref (-1) in
  Array.iteri
    (fun i lit ->
      if lit = asserting then first := i
      else if !second < 0 || t.levels.(variable lit) > t.levels.(variable literals.(!second)) then
        second := i)
    literals;
  if level < t.limits.size - 1 then t.nonchronological_backjumps <- t.nonchronological_backjumps + 1;
  backtrack t level;
  let id =
    install_clause t proof_id literals ~first:!first
      ~second:(if !second < 0 then !first else !second)
  in
  t.learned_clauses <- t.learned_clauses + 1;
  if not (enqueue t asserting id) then failwith "Boolean: learned clause is not asserting"

(* The unassigned occurring variable of the greatest activity, the lowest one among equal
   activities, by a scan over every variable: the reference of the heap's decision in the tests.
   The scan polls [guard] at every 256th variable. *)
let scan_best t ~guard =
  let best = ref (-1) in
  for v = 0 to t.variables - 1 do
    if v land 255 = 0 then guard ();
    if t.values.(v) = 0 && t.occurs.(v) && (!best < 0 || t.activity.(v) > t.activity.(!best)) then
      best := v
  done;
  !best

(* The same variable from the heap, after the same [guard] calls as the scan (which change
   nothing else, so a raise leaves the solver as the scan's would): assigned variables met at the
   top are dropped, the chosen one leaves. *)
let heap_best t ~guard =
  for _ = 1 to (t.variables + 255) / 256 do
    guard ()
  done;
  if t.free = 0 then -1
  else (
    while t.heap_size > 0 && t.values.(t.heap.(0)) <> 0 do
      ignore (heap_pop t)
    done;
    if t.heap_size = 0 then -1 else heap_pop t)

let decide t ~guard =
  let best = if t.reference then scan_best t ~guard else heap_best t ~guard in
  if best < 0 then false
  else (
    push t.limits t.trail.size;
    t.decisions <- t.decisions + 1;
    let lit = if t.phases.(best) then best + 1 else -(best + 1) in
    ignore (enqueue t lit (-1));
    true)

let run t ~guard =
  guard ();
  clear_assignment t;
  if t.watches_dirty then rebuild_watches t ~guard;
  match t.root with
  | Some _ -> Unsat
  | None -> (
      let initial_conflict = ref (-1) in
      let i = ref 0 in
      while !initial_conflict < 0 && !i < t.units.size do
        guard ();
        let id = t.units.data.(!i) in
        if not (enqueue t t.clauses.(id).literals.(0) id) then initial_conflict := id;
        incr i
      done;
      if !initial_conflict >= 0 then (
        t.conflicts <- t.conflicts + 1;
        refute_root t ~guard !initial_conflict;
        Unsat)
      else
        let finished = ref false in
        while not !finished do
          guard ();
          let conflict = propagate t ~guard in
          if conflict >= 0 then (
            t.conflicts <- t.conflicts + 1;
            if t.limits.size = 0 then (
              refute_root t ~guard conflict;
              finished := true)
            else learn t ~guard conflict)
          else if not (decide t ~guard) then finished := true
        done;
        match t.root with
        | Some _ -> Unsat
        | None -> Sat (Array.init t.variables (fun v -> t.values.(v) = 1)))

let solve t ~guard =
  require_idle t;
  t.solving <- true;
  match run t ~guard with
  | result ->
      t.solving <- false;
      result
  | exception exn ->
      let backtrace = Printexc.get_raw_backtrace () in
      t.solving <- false;
      t.watches_dirty <- true;
      Printexc.raise_with_backtrace exn backtrace
