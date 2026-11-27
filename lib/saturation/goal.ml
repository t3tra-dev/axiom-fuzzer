open Wire

(* A table of unfinished derivations. Its clauses are consequences, not new
   assumptions: expansion is resolution/factoring/paramodulation, and admission
   reconstructs the ordinary proof DAG. No search failure is a learned clause. *)
type ticket = int * int

type recipe = {
  step : step;
  raw : clause;
  parents : recipe list;
  leaves : ticket list;
  support : int list;
  height : int;
}

(* The scan a state's cursor performs: its lower generation bound, where its
   index cursors stand and how many elements of each stream it has consumed
   there. It outlives a cursor dropped under memory pressure, which then
   continues exactly where it stopped instead of starting over. *)
type scan = {
  since : int;
  resolution : Index.mark;
  equality : Equality_index.mark;
  unary_taken : int ref;
  resolution_taken : int ref;
  equality_taken : int ref;
}

type state = {
  proof : recipe;
  owner : ticket;
  mutable depth : int;
  mutable weight : int;
  mutable cursor : (recipe list * Calculus.inference) Seq.t option;
  mutable queued : bool;
  mutable waiting : bool;
  mutable restart : bool;
  mutable engaged : bool;
  mutable started : bool;
  mutable queued_at : int;
  born : int;
  mutable credit : int;
  mutable connections : int;
  mutable promoted : bool;
  mutable seen : int;
  mutable cursor_epoch : int;
  mutable replay : bool;
  mutable scan : scan option;
}

type root = {
  proof : recipe;
  owner : ticket;  (** its key in [roots] *)
  mutable removed : bool;
      (** it has left [roots]. An owner is the ticket of one retained generation, so a root is noted
          once and never replaced: [Tbl.Pair.mem t.roots r.owner] is [not r.removed] *)
  mutable round : int;
  mutable queued : bool;
  mutable seen : int;
  mutable engaged : bool;
  mutable work : int;
  mutable next_budget : int;
  mutable runnable : int;
}

type metrics = {
  mutable created : int;
  mutable expanded : int;
  mutable attempts : int;
  mutable shared : int;
  mutable resumed : int;
  mutable woken : int;
  mutable waiting : int;
  mutable depth_cut : int;
  mutable weight_cut : int;
  mutable slices : int;
  mutable widened : int;
  mutable roots : int;
  mutable invalidated : int;
  mutable evicted : int;
  mutable retired : int;
  mutable committed : int;
  mutable closed : int;
  mutable conditional : int;
  mutable blocked : int;
  mutable redundant : int;
  mutable age_total : int;
  mutable age_max : int;
  mutable fresh_selected : int;
  mutable continued_selected : int;
  mutable wait_total : int;
  mutable wait_max : int;
  mutable height_max : int;
  mutable depth_max : int;
  mutable promoted : int;
  mutable promotion_stale : int;
  mutable resolution_attempts : int;
  mutable equality_attempts : int;
  mutable first_trials : int;
  mutable delta_queries : int;
  mutable reused : int;
}

type t = {
  index : Index.t;
  equality : Equality_index.t;
  states : state Tbl.Int.t;
  memo : int Tbl.Clause_ints.t;
  cache : int Queue.t;
  promotion : int Queue.t;
  ready : int Queue.t;
  continuing : int Queue.t;
  roots : root Tbl.Pair.t;
  revisits : root Queue.t;
  schedule : Directions.Schedule.t;
  refresh_order : root Queue.t;
  mutable refresh_left : int;
  mutable epoch : int;
  calculus : Calculus.t;
  on_clause : (string -> int list -> step -> unit) option;
  mutable fresh_states : state list;  (** states added since the last [collect] *)
  mutable fresh_roots : ticket list;  (** root owners added since the last [collect] *)
  mutable forgotten : int;  (** states removed from [states] so far *)
  mutable retired : int list;
      (** ids whose retained ticket died since the last [collect] ([remove] and [supersede]; repeats
          allowed): the only ids whose tickets [collect]'s [alive] can reject anew *)
  by_leaf : int list Tbl.Int.t;
      (** per leaf id, the states (by id) whose proof has a leaf ticket of it; may also hold states
          that were forgotten since, or ids of later states *)
  mutable by_leaf_entries : int;  (** the entries of [by_leaf] *)
  mutable leaf_entries : int;  (** the leaves of the states in [states] *)
  roots_by_id : root list Tbl.Int.t;  (** per owner id, the roots noted for it (removed too) *)
  mutable recheck : int list;
      (** ids that kept an invalid binding through the last full test (see [collect]) *)
  mutable dropped : int;  (** roots removed from [roots] so far *)
  mutable pruned : int * int;  (** [forgotten] and [dropped] at the last [collect]'s prunes *)
  mutable next : int;
  mutable turns : int;
  metrics : metrics;
}

let create ?on_clause ?on_inference () =
  let calculus = Calculus.create ~selection:false (Term.create ()) in
  calculus.observe <- on_inference;
  {
    index = Index.create ();
    equality = Equality_index.create ();
    states = Tbl.Int.create 256;
    memo = Tbl.Clause_ints.create 512;
    cache = Queue.create ();
    promotion = Queue.create ();
    ready = Queue.create ();
    continuing = Queue.create ();
    roots = Tbl.Pair.create 256;
    revisits = Queue.create ();
    schedule = Directions.Schedule.create ();
    refresh_order = Queue.create ();
    refresh_left = 0;
    epoch = 0;
    calculus;
    on_clause;
    fresh_states = [];
    fresh_roots = [];
    forgotten = 0;
    retired = [];
    by_leaf = Tbl.Int.create 256;
    by_leaf_entries = 0;
    leaf_entries = 0;
    roots_by_id = Tbl.Int.create 256;
    recheck = [];
    dropped = 0;
    pruned = (0, 0);
    next = -1;
    turns = 0;
    metrics =
      {
        created = 0;
        expanded = 0;
        attempts = 0;
        shared = 0;
        resumed = 0;
        woken = 0;
        waiting = 0;
        depth_cut = 0;
        weight_cut = 0;
        slices = 0;
        widened = 0;
        roots = 0;
        invalidated = 0;
        evicted = 0;
        retired = 0;
        committed = 0;
        closed = 0;
        conditional = 0;
        blocked = 0;
        redundant = 0;
        age_total = 0;
        age_max = 0;
        fresh_selected = 0;
        continued_selected = 0;
        wait_total = 0;
        wait_max = 0;
        height_max = 0;
        depth_max = 0;
        promoted = 0;
        promotion_stale = 0;
        resolution_attempts = 0;
        equality_attempts = 0;
        first_trials = 0;
        delta_queries = 0;
        reused = 0;
      };
  }

let valid ~alive p = List.for_all alive p.leaves
let key p = (p.step.clause, p.support)
let union a b = List.sort_uniq compare (a @ b)
let wanted clause = List.map (fun l -> { l with positive = not l.positive }) clause

let enqueue t (s : state) =
  if not s.queued then (
    s.queued <- true;
    Option.iter (fun r -> r.runnable <- r.runnable + 1) (Tbl.Pair.find_opt t.roots s.owner);
    s.queued_at <- t.turns;
    Queue.add s.proof.step.id (if s.started || s.proof.height > 0 then t.continuing else t.ready))

let root_queue t owner =
  match Tbl.Pair.find_opt t.roots owner with
  | Some r when r.engaged && not r.queued ->
      r.queued <- true;
      Queue.add r t.revisits
  | _ -> ()

(* Every removal from [roots] goes through here, so [removed] marks exactly the roots that left. *)
let drop_root t (r : root) =
  r.removed <- true;
  t.dropped <- t.dropped + 1;
  Tbl.Pair.remove t.roots r.owner

let engage t (s : state) =
  s.engaged <- true;
  Option.iter (fun r -> r.engaged <- true) (Tbl.Pair.find_opt t.roots s.owner)

let observe t stage (p : recipe) = Option.iter (fun f -> f stage p.support p.step) t.on_clause
let merit (s : state) = s.credit + min 4 s.connections + if s.scan <> None then 2 else 0

let forget ?(reason = "goal_forgotten") t id =
  match Tbl.Int.find_opt t.states id with
  | None -> ()
  | Some s ->
      observe t reason s.proof;
      if s.queued then
        Option.iter
          (fun r -> r.runnable <- max 0 (r.runnable - 1))
          (Tbl.Pair.find_opt t.roots s.owner);
      let age = t.turns - s.born in
      t.metrics.age_total <- t.metrics.age_total + age;
      t.metrics.age_max <- max t.metrics.age_max age;
      if Tbl.Clause_ints.find_opt t.memo (key s.proof) = Some id then
        Tbl.Clause_ints.remove t.memo (key s.proof);
      if s.waiting then t.metrics.waiting <- t.metrics.waiting - 1;
      t.forgotten <- t.forgotten + 1;
      t.leaf_entries <- t.leaf_entries - List.length s.proof.leaves;
      Tbl.Int.remove t.states id;
      Index.remove t.index id;
      Equality_index.remove t.equality id

let wake t ~guard (proof : recipe) =
  (* The watch key is the current obligation, including substituted terms. A
     bounded notification only affects latency: root retries remain FIFO. *)
  let candidates = Tbl.Int.create 16 in
  List.iter
    (fun literal ->
      Index.sample ~guard ~limit:8 ~budget:32 t.index literal
      |> List.iter (fun (s : step) -> Tbl.Int.replace candidates s.id true))
    proof.step.clause;
  (* Equality can enable an obligation without a complementary predicate. *)
  (if List.exists (fun l -> match l.atom with E _ -> true | _ -> false) proof.step.clause then
     let left = ref 32 in
     Equality_index.locations ~sources:true ~variables:true proof.step.clause
     |> List.iter (fun (term, _) ->
         let exception Enough in
         try
           Equality_index.query t.equality t.equality.targets ~variables:true term
             ~guard:(fun () ->
               guard ();
               decr left;
               if !left < 0 then raise Enough)
             (fun p ->
               if not (Tbl.Int.mem candidates p.Equality_index.step.id) then
                 Tbl.Int.add candidates p.step.id false)
         with Enough -> ()));
  Tbl.Int.iter
    (fun id complementary ->
      (match (Tbl.Int.find_opt t.states id, Tbl.Int.find_opt t.states proof.step.id) with
      | Some other, Some source
        when other.owner <> source.owner
             && not (List.exists (fun (leaf, _) -> leaf = id) proof.leaves) ->
          source.connections <- min 8 (source.connections + 1);
          other.connections <- min 8 (other.connections + 1)
      | _ -> ());
      match Tbl.Int.find_opt t.states id with
      | Some s ->
          if complementary then s.engaged <- true;
          if s.waiting && s.engaged then (
            s.waiting <- false;
            t.metrics.waiting <- t.metrics.waiting - 1;
            t.metrics.woken <- t.metrics.woken + 1;
            s.cursor <- None;
            s.scan <- None;
            enqueue t s)
          else if s.engaged && s.started then s.restart <- true
      | _ -> ())
    candidates

let add_state ?(active = true) t ~guard ~owner ~depth ~weight proof =
  let s =
    {
      proof;
      owner;
      depth;
      weight;
      cursor = None;
      queued = false;
      waiting = false;
      restart = false;
      engaged = active;
      started = false;
      queued_at = t.turns;
      born = t.turns;
      credit = 0;
      connections = 0;
      promoted = false;
      seen = 0;
      cursor_epoch = 0;
      replay = false;
      scan = None;
    }
  in
  Tbl.Int.add t.states proof.step.id s;
  t.fresh_states <- s :: t.fresh_states;
  List.iter
    (fun ((leaf, _) : ticket) ->
      Tbl.Int.replace t.by_leaf leaf
        (proof.step.id :: Option.value ~default:[] (Tbl.Int.find_opt t.by_leaf leaf)))
    proof.leaves;
  let leaves = List.length proof.leaves in
  t.by_leaf_entries <- t.by_leaf_entries + leaves;
  t.leaf_entries <- t.leaf_entries + leaves;
  Index.add t.index proof.step;
  (* Every retained equality can rewrite a goal. Only cached residuals need
     reverse target postings: original clauses are queried as goals themselves.
     Duplicating all retained subterm locations would dominate the proof cache. *)
  Equality_index.add ~targets:(proof.height > 0) t.equality proof.step;
  if proof.height > 0 then (
    Tbl.Clause_ints.replace t.memo (key proof) proof.step.id;
    Queue.add proof.step.id t.cache;
    Queue.add proof.step.id t.promotion;
    while Queue.length t.cache > 512 do
      let first = Queue.take t.cache in
      let candidates = ref [ first ] in
      if t.metrics.evicted mod 4 <> 0 then
        for _ = 1 to min 7 (Queue.length t.cache) do
          candidates := Queue.take t.cache :: !candidates
        done;
      let value id = match Tbl.Int.find_opt t.states id with None -> -1 | Some s -> merit s in
      let id =
        List.fold_left (fun best id -> if value id < value best then id else best) first !candidates
      in
      let prefix = Queue.create () in
      List.rev !candidates |> List.iter (fun other -> if other <> id then Queue.add other prefix);
      Queue.transfer t.cache prefix;
      Queue.transfer prefix t.cache;
      if Tbl.Int.mem t.states id then (
        t.metrics.evicted <- t.metrics.evicted + 1;
        root_queue t (Tbl.Int.find t.states id).owner;
        forget ~reason:"goal_evicted" t id)
    done);
  t.metrics.created <- t.metrics.created + 1;
  if proof.height > 0 then observe t "goal" proof;
  t.metrics.height_max <- max t.metrics.height_max proof.height;
  t.metrics.depth_max <- max t.metrics.depth_max depth;
  t.epoch <- t.epoch + 1;
  t.refresh_left <- Queue.length t.refresh_order;
  if active then enqueue t s
  else (
    s.waiting <- true;
    t.metrics.waiting <- t.metrics.waiting + 1);
  wake t ~guard proof;
  s

let note t ~guard ~support owner (step : step) =
  if not (Tbl.Pair.mem t.roots owner) then (
    let proof =
      { step; raw = step.clause; parents = []; leaves = [ owner ]; support; height = 0 }
    in
    (* Every premise receives one finite trial. Only demand-engaged roots widen
       automatically; positive-only knowledge cannot start infinite expansion. *)
    let active = List.exists (fun l -> not l.positive) step.clause in
    t.fresh_roots <- owner :: t.fresh_roots;
    let root =
      {
        proof;
        owner;
        removed = false;
        round = 1;
        queued = false;
        seen = -1;
        engaged = active;
        work = 0;
        next_budget = 64;
        runnable = 0;
      }
    in
    Tbl.Pair.add t.roots owner root;
    Tbl.Int.replace t.roots_by_id (fst owner)
      (root :: Option.value ~default:[] (Tbl.Int.find_opt t.roots_by_id (fst owner)));
    Queue.add root t.refresh_order;
    let s = add_state t ~guard ~owner ~depth:2 ~weight:(Clause.weight step.clause + 8) proof in
    s.engaged <- active)

(* The engine's retained ticket of [id] was replaced by a new generation without a removal. *)
let supersede t id = t.retired <- id :: t.retired

let remove t id =
  t.retired <- id :: t.retired;
  (match Tbl.Int.find_opt t.states id with
  | Some s ->
      Option.iter (drop_root t) (Tbl.Pair.find_opt t.roots s.owner);
      t.metrics.retired <- t.metrics.retired + 1
  | None -> ());
  forget t id

let ready_empty t = Queue.is_empty t.ready && Queue.is_empty t.continuing
let has_work t = t.refresh_left > 0 || not (ready_empty t && Queue.is_empty t.revisits)

let map_rule f = function
  | Resolve (p, i, q, j, s) -> Resolve (f p, i, f q, j, s)
  | Factor (p, i, j, s) -> Factor (f p, i, j, s)
  | Equality_resolve (p, i, s) -> Equality_resolve (f p, i, s)
  | Equality_factor (p, i, a, j, b, s) -> Equality_factor (f p, i, a, j, b, s)
  | Paramodulate (p, i, a, q, j, path, s) -> Paramodulate (f p, i, a, f q, j, path, s)
  | Input _ | Component _ -> invalid_arg "Goal: inferred recipe has an input rule"

let commit ?on_commit t ~guard ~record ~emit proof =
  Option.iter (fun f -> f (proof.step.clause = [])) on_commit;
  let ids = Tbl.Int.create 32 in
  let rec materialize p =
    guard ();
    if p.height = 0 then p.step.id
    else
      match Tbl.Int.find_opt ids p.step.id with
      | Some id -> id
      | None ->
          List.iter (fun parent -> ignore (materialize parent)) p.parents;
          let rule = map_rule lookup p.step.rule in
          let step = record p.raw rule in
          Tbl.Int.add ids p.step.id step.id;
          step.id
  and lookup id = if id >= 0 then id else Tbl.Int.find ids id in
  List.iter (fun p -> ignore (materialize p)) proof.parents;
  t.metrics.committed <- t.metrics.committed + 1;
  if proof.step.clause = [] then (
    t.metrics.closed <- t.metrics.closed + 1;
    if proof.support <> [] then t.metrics.conditional <- t.metrics.conditional + 1);
  emit proof.raw (map_rule lookup proof.step.rule)

(* [from] continues a dropped scan from its marks over postings up to [upto],
   the generation its original snapshot ended at. *)
let cursor ?(since = 0) ?upto ?from t ~guard ~alive (p : recipe) =
  let scan =
    match from with
    | Some (r : scan) -> r
    | None ->
        {
          since;
          resolution = Index.mark ();
          equality = Equality_index.mark ();
          unary_taken = ref 0;
          resolution_taken = ref 0;
          equality_taken = ref 0;
        }
  in
  let since = scan.since and resumes = from <> None in
  let unary emit = Calculus.unary t.calculus p.step emit in
  let partner id =
    match Tbl.Int.find_opt t.states id with
    | Some s when valid ~alive s.proof -> Some s.proof
    | _ -> None
  in
  let resolutions =
    Index.cursor ~since ?upto
      ?from:(Option.map (fun (r : scan) -> r.resolution) from)
      ~mark:scan.resolution ~guard t.index p.step.clause
    |> Seq.flat_map (function
      | None -> Seq.return ([], fun _ -> ())
      | Some ((q : step), position) -> (
          match partner q.id with
          | None -> Seq.return ([], fun _ -> ())
          | Some q ->
              Calculus.resolve_cursor ~positions:[ position ] t.calculus p.step q.step
              |> Seq.map (fun f ->
                  ( [ p; q ],
                    fun emit ->
                      t.metrics.resolution_attempts <- t.metrics.resolution_attempts + 1;
                      f emit ))))
    |> Index.follow ~resumes
         ~visits:(fun () -> scan.resolution.visits)
         ~position:(fun () -> Index.position scan.resolution)
         ~taken:scan.resolution_taken
  in
  let equalities =
    Equality_index.cursor ~since ?upto
      ?from:(Option.map (fun (r : scan) -> r.equality) from)
      ~mark:scan.equality ~guard t.equality ~variables:false p.step.clause
    |> Seq.flat_map (function
      | None -> Seq.return ([], fun _ -> ())
      | Some ((q : step), outgoing, position) -> (
          match partner q.id with
          | None -> Seq.return ([], fun _ -> ())
          | Some q ->
              (if outgoing then
                 Calculus.paramodulate_cursor ~positions:[ position ] t.calculus p.step q.step
               else Calculus.paramodulate_cursor ~positions:[ position ] t.calculus q.step p.step)
              |> Seq.map (fun f ->
                  ( [ p; q ],
                    fun emit ->
                      t.metrics.equality_attempts <- t.metrics.equality_attempts + 1;
                      f emit ))))
    |> Index.follow ~resumes
         ~visits:(fun () -> scan.equality.visits)
         ~position:(fun () -> Equality_index.position scan.equality)
         ~taken:scan.equality_taken
  in
  let local =
    if since > 0 then Seq.empty
    else
      Calculus.interleave
        (Seq.return ([ p ], unary))
        (Calculus.equality_factor_cursor t.calculus p.step |> Seq.map (fun f -> ([ p ], f)))
      |> Seq.drop (if resumes then !(scan.unary_taken) else 0)
      |> Seq.map (fun x ->
          incr scan.unary_taken;
          x)
  in
  (Calculus.interleave local (Calculus.interleave resolutions equalities), scan)

let widen t ~guard ~alive =
  let queue = t.revisits in
  if not (Queue.is_empty queue) then
    (* A removed root is the one [Tbl.Pair.find_opt t.roots owner] would not find. *)
    let r = Queue.take queue in
    let owner = r.owner in
    match if r.removed then None else Some r with
    | Some r when valid ~alive r.proof && r.runnable > 0 && r.work < r.next_budget ->
        Queue.add r t.revisits
    | Some r when valid ~alive r.proof -> (
        r.queued <- false;
        t.metrics.widened <- t.metrics.widened + 1;
        r.next_budget <- max (r.work + 64) (min (max_int / 2) r.next_budget * 2);
        let depth = 2 + r.round in
        t.metrics.depth_max <- max t.metrics.depth_max depth;
        let weight = (Clause.weight r.proof.step.clause + 8) * (1 + r.round) in
        r.round <- min (max_int / 1024) (r.round + 1);
        match Tbl.Int.find_opt t.states r.proof.step.id with
        | Some s ->
            s.depth <- depth;
            s.weight <- weight;
            s.replay <- true;
            if s.waiting then (
              s.waiting <- false;
              t.metrics.waiting <- t.metrics.waiting - 1);
            if s.scan = None then enqueue t s else s.restart <- true
        | None -> ignore (add_state t ~guard ~owner ~depth ~weight r.proof))
    | Some r -> drop_root t r
    | None -> ()

(* Notifications are bounded; a rotating epoch sweep also retries every live,
   engaged root after new knowledge. It cannot repeatedly prefer a recent root. *)
let refresh t =
  if t.refresh_left > 0 then (
    t.refresh_left <- t.refresh_left - 1;
    if Queue.is_empty t.refresh_order then t.refresh_left <- 0
    else
      let r = Queue.take t.refresh_order in
      if not r.removed then (
        Queue.add r t.refresh_order;
        if r.seen < t.epoch then (
          r.seen <- t.epoch;
          match Tbl.Int.find_opt t.states r.proof.step.id with
          | Some s when s.engaged && s.started ->
              if s.waiting then (
                s.waiting <- false;
                t.metrics.waiting <- t.metrics.waiting - 1;
                t.metrics.woken <- t.metrics.woken + 1;
                enqueue t s)
              else s.restart <- true
          | _ -> ())))

let take ?(first = false) t =
  let fifo = first in
  (* Continuations get three slots out of four. Each queue also retains its
     own FIFO turn, so short residuals cannot permanently overtake old work. *)
  let primary, other =
    if first || t.turns mod 4 = 0 then (t.ready, t.continuing) else (t.continuing, t.ready)
  in
  let rec pop queue =
    if Queue.is_empty queue then None
    else
      let id = Queue.take queue in
      match Tbl.Int.find_opt t.states id with Some s when s.queued -> Some s | _ -> pop queue
  in
  let queue, first =
    match pop primary with Some _ as first -> (primary, first) | None -> (other, pop other)
  in
  match first with
  | None -> None
  | Some first ->
      let candidates = ref [ first ] in
      let continued = queue == t.continuing in
      let turn = if continued then t.metrics.continued_selected else t.metrics.fresh_selected in
      if (not fifo) && turn mod 4 <> 0 then
        for _ = 1 to 7 do
          Option.iter (fun s -> candidates := s :: !candidates) (pop queue)
        done;
      let rank (s : state) =
        ( ((4 * List.length s.proof.step.clause) + Clause.weight s.proof.step.clause)
          * 16
          / (16 + merit s),
          s.born )
      in
      let best =
        List.fold_left (fun best s -> if rank s < rank best then s else best) first !candidates
      in
      (* Restore the unchosen prefix in front, so an old root keeps its age. *)
      let prefix = Queue.create () in
      List.rev !candidates
      |> List.iter (fun (s : state) -> if s != best then Queue.add s.proof.step.id prefix);
      Queue.transfer queue prefix;
      Queue.transfer prefix queue;
      best.queued <- false;
      Option.iter
        (fun r -> r.runnable <- max 0 (r.runnable - 1))
        (Tbl.Pair.find_opt t.roots best.owner);
      let wait = t.turns - best.queued_at in
      t.metrics.wait_total <- t.metrics.wait_total + wait;
      t.metrics.wait_max <- max t.metrics.wait_max wait;
      if continued then t.metrics.continued_selected <- t.metrics.continued_selected + 1
      else t.metrics.fresh_selected <- t.metrics.fresh_selected + 1;
      Some best

let promote ?offer ?on_commit t ~guard ~alive ~blocked ~redundant ~record ~emit =
  let rec scan left =
    if left > 0 && not (Queue.is_empty t.promotion) then (
      guard ();
      let id = Queue.take t.promotion in
      match Tbl.Int.find_opt t.states id with
      | None -> scan (left - 1)
      | Some s when s.promoted -> scan (left - 1)
      | Some s ->
          Queue.add id t.promotion;
          let p = s.proof in
          if not (valid ~alive p) then (
            t.metrics.promotion_stale <- t.metrics.promotion_stale + 1;
            forget ~reason:"goal_invalidated" t id;
            scan (left - 1))
          else if
            p.height > 8
            || List.length p.step.clause > 2
            || (s.connections = 0 && s.credit < 4)
            || (not
                  (Option.fold ~none:false
                     ~some:(fun r -> r.engaged)
                     (Tbl.Pair.find_opt t.roots s.owner)))
            || blocked p.support
            || redundant (List.map fst p.leaves) p.step.clause
          then scan (left - 1)
          else
            (* Bound reconstruction work, including shared ancestors. *)
            let seen = Tbl.Int.create 32 in
            let rec small p =
              guard ();
              p.height = 0 || Tbl.Int.mem seen p.step.id
              || Tbl.Int.length seen < 64
                 &&
                 (Tbl.Int.add seen p.step.id ();
                  List.for_all small p.parents)
            in
            if small p then (
              s.promoted <- true;
              t.metrics.promoted <- t.metrics.promoted + 1;
              observe t "goal_promoted" p;
              match offer with
              | Some offer -> offer p
              | None -> commit ?on_commit t ~guard ~record ~emit p))
  in
  scan 8

let advance ?offer ?on_commit ?(attempts = 16) ?(first = false) ?(blocked = fun _ -> false)
    ?(use = fun _ _ -> ()) t ~guard ~alive ~record ~emit ~redundant ~demand =
  t.turns <- t.turns + 1;
  t.calculus.guard <- guard;
  if t.turns mod 8 = 0 then
    promote ?offer ?on_commit t ~guard ~alive ~blocked ~redundant ~record ~emit;
  refresh t;
  let open Directions.Schedule in
  let ready =
    (if Queue.is_empty t.ready then [] else [ First ])
    @ (if Queue.is_empty t.revisits then [] else [ Demand ])
    @ if Queue.is_empty t.continuing then [] else [ Continue ]
  in
  let job = if first && List.mem First ready then Some First else choose t.schedule ready in
  if job = Some Demand then widen t ~guard ~alive;
  let before = t.index.postings + t.equality.postings + t.calculus.attempts in
  let owner = ref None in
  Fun.protect
    ~finally:(fun () ->
      let work = 1 + t.index.postings + t.equality.postings + t.calculus.attempts - before in
      Option.iter
        (fun ticket ->
          Option.iter (fun (r : root) -> r.work <- r.work + work) (Tbl.Pair.find_opt t.roots ticket))
        !owner;
      Option.iter (fun job -> charge t.schedule job work) job)
    (fun () ->
      match take ~first:(job = Some First) t with
      | None -> ()
      | Some s when not (valid ~alive s.proof) ->
          t.metrics.invalidated <- t.metrics.invalidated + 1;
          forget t s.proof.step.id
      | Some s when blocked s.proof.support ->
          t.metrics.blocked <- t.metrics.blocked + 1;
          s.cursor <- None;
          s.scan <- None;
          if not s.waiting then (
            s.waiting <- true;
            t.metrics.waiting <- t.metrics.waiting + 1)
      | Some s ->
          owner := Some s.owner;
          if (not s.started) && s.proof.height = 0 then (
            t.metrics.first_trials <- t.metrics.first_trials + 1;
            t.metrics.roots <- t.metrics.roots + 1;
            observe t "goal_first" s.proof);
          s.started <- true;
          let fresh = s.scan = None in
          if fresh then (
            t.metrics.expanded <- t.metrics.expanded + 1;
            demand ~guard (wanted s.proof.step.clause))
          else t.metrics.resumed <- t.metrics.resumed + 1;
          let stream = ref (Option.value ~default:Seq.empty s.cursor) in
          (match (s.cursor, s.scan) with
          | Some _, _ -> ()
          | None, Some from ->
              (* Dropped under memory pressure: continue the same scan. *)
              stream := fst (cursor ~upto:s.cursor_epoch ~from t ~guard ~alive s.proof)
          | None, None ->
              let since = if s.replay then 0 else s.seen in
              if since > 0 then t.metrics.delta_queries <- t.metrics.delta_queries + 1;
              s.replay <- false;
              s.cursor_epoch <- t.epoch;
              let c, scan = cursor ~since t ~guard ~alive s.proof in
              s.scan <- Some scan;
              stream := c);
          (* Initial coverage is cheap; continuation owns the larger slices.
             Keep the exact cursor even when the first probe found nothing. *)
          let finished = ref false
          and left = ref (if job = Some First then min 4 attempts else attempts) in
          let derive parents raw rule =
            guard ();
            if List.for_all (valid ~alive) parents then
              let clause = Clause.normalize raw in
              if not (Clause.tautology_sorted clause) then
                let support = List.fold_left (fun a p -> union a p.support) [] parents in
                let leaves = List.fold_left (fun a p -> union a p.leaves) [] parents in
                let height = 1 + List.fold_left (fun a p -> max a p.height) 0 parents in
                let proof =
                  { step = { id = t.next; clause; rule }; raw; parents; leaves; support; height }
                in
                if clause <> s.proof.step.clause || support <> s.proof.support then
                  if blocked support then t.metrics.blocked <- t.metrics.blocked + 1
                  else if height > s.depth then (
                    observe t "goal_depth_cut" proof;
                    t.metrics.depth_cut <- t.metrics.depth_cut + 1;
                    root_queue t s.owner)
                  else if Clause.weight clause > s.weight then (
                    observe t "goal_weight_cut" proof;
                    t.metrics.weight_cut <- t.metrics.weight_cut + 1;
                    root_queue t s.owner)
                  else (
                    t.next <- t.next - 1;
                    if List.exists (fun p -> p.height > 0 && p.step.id <> s.proof.step.id) parents
                    then t.metrics.shared <- t.metrics.shared + 1;
                    let previous =
                      Option.bind
                        (Tbl.Clause_ints.find_opt t.memo (key proof))
                        (Tbl.Int.find_opt t.states)
                    in
                    let connected =
                      List.exists
                        (fun p ->
                          match Tbl.Int.find_opt t.states p.step.id with
                          | Some parent ->
                              Option.fold ~none:false
                                ~some:(fun r -> r.engaged)
                                (Tbl.Pair.find_opt t.roots parent.owner)
                          | None -> false)
                        parents
                    in
                    match previous with
                    | Some old when valid ~alive old.proof && old.proof.height <= height ->
                        if connected then engage t old;
                        if s.depth > old.depth || s.weight > old.weight then (
                          old.depth <- max old.depth s.depth;
                          old.weight <- max old.weight s.weight;
                          old.replay <- true;
                          if old.waiting then (
                            old.waiting <- false;
                            t.metrics.waiting <- t.metrics.waiting - 1);
                          old.restart <- true;
                          enqueue t old)
                    | _ ->
                        Option.iter (fun (old : state) -> forget t old.proof.step.id) previous;
                        if redundant (List.map fst leaves) clause then
                          t.metrics.redundant <- t.metrics.redundant + 1
                        else
                          (* Partial consequences stay shared. A bounded later promotion
                         can export a connected or reused lemma with this DAG. *)
                          let shorter = List.length clause < List.length s.proof.step.clause in
                          if shorter || List.exists (fun p -> p.step.id <> s.proof.step.id) parents
                          then use leaves (if shorter then 8 else 2);
                          List.iter
                            (fun (p : recipe) ->
                              Option.iter
                                (fun (parent : state) ->
                                  let reused = parent.owner <> s.owner in
                                  if reused && p.height > 0 then
                                    t.metrics.reused <- t.metrics.reused + 1;
                                  (* Resolution is symmetric: either parent can
                                     carry the demand, regardless of its owner. *)
                                  if connected then engage t parent;
                                  let gain =
                                    if clause = [] then 16 else if shorter || reused then 4 else 0
                                  in
                                  parent.credit <- min 32 (parent.credit + gain))
                                (Tbl.Int.find_opt t.states p.step.id))
                            parents;
                          if clause = [] then commit ?on_commit t ~guard ~record ~emit proof;
                          if clause <> [] && valid ~alive proof then
                            ignore
                              (add_state t ~guard ~owner:s.owner ~depth:s.depth ~weight:s.weight
                                 proof))
          in
          Fun.protect
            ~finally:(fun () -> Term.clear t.calculus.unifier.arena)
            (fun () ->
              while !left > 0 && not !finished do
                guard ();
                match !stream () with
                | Seq.Nil -> finished := true
                | Seq.Cons ((parents, attempt), rest) ->
                    stream := rest;
                    decr left;
                    t.metrics.attempts <- t.metrics.attempts + 1;
                    if List.for_all (valid ~alive) parents then attempt (derive parents)
              done);
          if Tbl.Int.mem t.states s.proof.step.id then
            if !finished then (
              s.cursor <- None;
              s.scan <- None;
              s.seen <- s.cursor_epoch;
              if s.restart then (
                s.restart <- false;
                enqueue t s)
              else (
                s.waiting <- true;
                t.metrics.waiting <- t.metrics.waiting + 1))
            else (
              s.cursor <- Some !stream;
              t.metrics.slices <- t.metrics.slices + 1;
              enqueue t s))

(* [quiet]: no ticket that [alive] accepted at the previous collection has died since (tickets
   never come back to life). Then every state and root that was kept then is still valid, so
   only those added since can be dead; when none of them is, the scans below would drop nothing
   and are skipped. Otherwise they run as before, in the same table order. *)
(* [by_leaf] without the forgotten states, once stale entries outnumber the live ones. *)
let rebuild_leaves t =
  if t.by_leaf_entries > (2 * t.leaf_entries) + 4096 then (
    Tbl.Int.reset t.by_leaf;
    Tbl.Int.iter
      (fun id (s : state) ->
        List.iter
          (fun ((leaf, _) : ticket) ->
            Tbl.Int.replace t.by_leaf leaf
              (id :: Option.value ~default:[] (Tbl.Int.find_opt t.by_leaf leaf)))
          s.proof.leaves)
      t.states;
    t.by_leaf_entries <- t.leaf_entries)

(* [alive] is the engine's ticket test: a ticket dies when its id's retained ticket changes, and
   never comes back (generations only grow). Every such change since the last collection is in
   [retired]. A state or root that passed [alive] then fails it now only if one of its tickets
   is of a retired id, so the full scans test only the fresh ones and those found through
   [by_leaf] and [roots_by_id]; they forget and drop the same ones (in another order, which
   changes no table: every key has one binding). [~exhaustive:true] scans everything, as
   before (the reference of the unit tests). *)
let collect ?(quiet = false) ?(exhaustive = false) t ~alive =
  let fresh_states = t.fresh_states and fresh_roots = t.fresh_roots in
  let retired = t.retired in
  t.fresh_states <- [];
  t.fresh_roots <- [];
  t.retired <- [];
  let invalidate id =
    t.metrics.invalidated <- t.metrics.invalidated + 1;
    forget t id
  in
  if not (quiet && List.for_all (fun (s : state) -> valid ~alive s.proof) fresh_states) then (
    if exhaustive then
      let dead =
        Tbl.Int.fold
          (fun id (s : state) acc -> if valid ~alive s.proof then acc else id :: acc)
          t.states []
      in
      List.iter invalidate dead
    else
      (* A state id can have several bindings (a root noted again for a new ticket of its
          clause before the old state was forgotten): the full scan calls [forget] once per
          invalid binding, and [forget] acts on the latest binding, which may be a valid one, so
          an invalid binding can outlive the scan and fall to a later one. [test] does the same
          once per id, and the ids left with an invalid binding are tested again next time. *)
      let tested = Tbl.Int.create 16 and left = ref [] in
      let test id =
        if not (Tbl.Int.mem tested id) then (
          Tbl.Int.add tested id ();
          let bindings = Tbl.Int.find_all t.states id in
          List.iter (fun (s : state) -> if not (valid ~alive s.proof) then invalidate id) bindings;
          match bindings with
          | [] | [ _ ] -> ()
          | _ ->
              if
                List.exists
                  (fun (s : state) -> not (valid ~alive s.proof))
                  (Tbl.Int.find_all t.states id)
              then left := id :: !left)
      in
      let recheck = t.recheck in
      t.recheck <- [];
      List.iter test recheck;
      List.iter (fun (s : state) -> test s.proof.step.id) fresh_states;
      List.iter
        (fun leaf ->
          match Tbl.Int.find_opt t.by_leaf leaf with
          | None -> ()
          | Some ids ->
              List.iter test ids;
              let still =
                List.filter
                  (fun id ->
                    List.exists
                      (fun (s : state) ->
                        List.exists (fun ((l, _) : ticket) -> l = leaf) s.proof.leaves)
                      (Tbl.Int.find_all t.states id))
                  ids
              in
              t.by_leaf_entries <- t.by_leaf_entries - List.length ids + List.length still;
              if still = [] then Tbl.Int.remove t.by_leaf leaf
              else Tbl.Int.replace t.by_leaf leaf still)
        retired;
      t.recheck <- !left);
  rebuild_leaves t;
  let drop (r : root) =
    if not (r.removed || alive r.owner) then (
      r.removed <- true;
      t.dropped <- t.dropped + 1;
      Tbl.Pair.remove t.roots r.owner)
  in
  if not (quiet && List.for_all alive fresh_roots) then
    if exhaustive then
      Tbl.Pair.filter_map_inplace
        (fun owner r ->
          if alive owner then Some r
          else (
            r.removed <- true;
            t.dropped <- t.dropped + 1;
            None))
        t.roots
    else (
      List.iter (fun owner -> Option.iter drop (Tbl.Pair.find_opt t.roots owner)) fresh_roots;
      List.iter
        (fun id ->
          match Tbl.Int.find_opt t.roots_by_id id with
          | None -> ()
          | Some roots -> (
              List.iter drop roots;
              match List.filter (fun (r : root) -> not r.removed) roots with
              | [] -> Tbl.Int.remove t.roots_by_id id
              | live -> Tbl.Int.replace t.roots_by_id id live))
        retired);
  let prune queue keep = Shared.filter_queue keep queue in
  (* After a prune every element passes its test. An element of [ready] or [continuing] is a
     queued state (a state stops being queued only when [take] takes it off its queue), one of
     [cache] or [promotion] a state: either can fail only once a state has been forgotten. A
     root queue's element fails only once its root has been dropped. Without such a change since
     the last prunes, these prunes would keep every element and are skipped. *)
  let forgotten, dropped = t.pruned in
  if t.forgotten <> forgotten then (
    prune t.ready (fun id ->
        match Tbl.Int.find_opt t.states id with Some s -> s.queued | None -> false);
    prune t.continuing (fun id ->
        match Tbl.Int.find_opt t.states id with Some s -> s.queued | None -> false);
    prune t.cache (Tbl.Int.mem t.states);
    prune t.promotion (Tbl.Int.mem t.states));
  if t.dropped <> dropped then (
    prune t.revisits (fun r -> not r.removed);
    prune t.refresh_order (fun r -> not r.removed));
  t.pruned <- (t.forgotten, t.dropped);
  t.refresh_left <- min t.refresh_left (Queue.length t.refresh_order);
  Index.compact t.index;
  Equality_index.compact t.equality

(* Memory pressure: forget suspended cursors, which keep the posting lists of
   their creation alive. The state stays queued with its scan; its next run
   continues the same scan (same lower bound, same upper generation) over the
   current posting lists from where it stopped, so no attempt is skipped or
   repeated and progress survives any number of drops. Returns the number of
   cursors dropped. *)
let drop_cursors t =
  Tbl.Int.fold
    (fun _ (s : state) dropped ->
      match (s.cursor, s.scan) with
      | Some _, Some scan ->
          s.cursor <- None;
          Equality_index.detach scan.equality;
          dropped + 1
      | _ -> dropped)
    t.states 0
