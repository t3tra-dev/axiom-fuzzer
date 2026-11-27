open Wire

(* Search hints, never logical premises. Requests are complements of retained
   units; their registration generations are checked before every use. Rewards
   follow a bounded part of the proof DAG and cannot authorize deletion. *)
type entry = {
  mutable credit : int;
  mutable seconds : float;
  mutable batches : int;
  mutable generation : int option;
  mutable plan_cost : int;
  mutable closed_credit : int;
  planned : bool;
  mutable useful : bool;
}

type request = { ticket : int * int; wanted : literal }
type resolution = { pivot : int; using : int * int; sigma : substitution; conclusion : clause }
type plan = { residual : clause; reverse : resolution list }

type t = {
  entries : entry Tbl.Int.t;
  requests : request Queue.t;
  by_literal : request list Tbl.Feature.t;
  units : Index.t;
  goals : Index.t;
  goal_order : (int * int) Queue.t;
  pending : (int * int) Queue.t;
  queued : unit Tbl.Pair.t;
  saved : plan Tbl.Pair.t;
  mutable fresh_entries : int list;  (** entry ids registered since the last [collect] *)
  mutable removed_entries : int list;
      (** ids passed to [remove] since the last [collect] (repeats allowed): with [fresh_entries],
          every entry that can fail the next [collect]'s [keep] *)
  mutable choosing : int;
  mutable committing : bool;
  mutable requested : int;
  mutable matches : int;
  mutable trials : int;
  mutable progress : int;
  mutable probes : int;
  mutable preferred_resumes : int;
  mutable plans : int;
  mutable plan_trials : int;
  mutable plan_steps : int;
  mutable plan_closed : int;
  mutable plan_exhausted : int;
  mutable plan_stale : int;
  mutable plan_dropped : int;
  mutable plan_redundant : int;
  mutable plan_deferred : int;
  mutable plan_reused : int;
  mutable plan_invalidated : int;
  mutable plan_prioritized : int;
  mutable plan_useful : int;
  scratch : Term.arena;
      (** the term arena of [pressure]'s unifiers, emptied before each attempt (as a fresh one) *)
}

let create () =
  {
    entries = Tbl.Int.create 256;
    requests = Queue.create ();
    by_literal = Tbl.Feature.create 32;
    units = Index.create ();
    goals = Index.create ();
    goal_order = Queue.create ();
    pending = Queue.create ();
    queued = Tbl.Pair.create 128;
    saved = Tbl.Pair.create 128;
    fresh_entries = [];
    removed_entries = [];
    choosing = 0;
    committing = false;
    requested = 0;
    matches = 0;
    trials = 0;
    progress = 0;
    probes = 0;
    preferred_resumes = 0;
    plans = 0;
    plan_trials = 0;
    plan_steps = 0;
    plan_closed = 0;
    plan_exhausted = 0;
    plan_stale = 0;
    plan_dropped = 0;
    plan_redundant = 0;
    plan_deferred = 0;
    plan_reused = 0;
    plan_invalidated = 0;
    plan_prioritized = 0;
    plan_useful = 0;
    scratch = Term.create ();
  }

let register t id =
  if not (Tbl.Int.mem t.entries id) then (
    t.fresh_entries <- id :: t.fresh_entries;
    Tbl.Int.add t.entries id
      {
        credit = 0;
        seconds = 0.;
        batches = 0;
        generation = None;
        plan_cost = 0;
        closed_credit = 0;
        planned = t.committing;
        useful = false;
      })

let ticket t id =
  Option.bind (Tbl.Int.find_opt t.entries id) (fun e -> Option.map (fun g -> (id, g)) e.generation)

let enqueue t key =
  if not (Tbl.Pair.mem t.queued key) then (
    if Queue.length t.pending >= 128 then (
      Tbl.Pair.remove t.queued (Queue.take t.pending);
      t.plan_dropped <- t.plan_dropped + 1);
    Queue.add key t.pending;
    Tbl.Pair.add t.queued key ())

(* A bounded watch list wakes old goals when a new unit can discharge a literal.
   Eviction affects only this extra inference path, never the retained clauses. *)
let note t ~guard ((id, generation) as key) (step : step) =
  register t id;
  (Tbl.Int.find t.entries id).generation <- Some generation;
  match step.clause with
  | [ literal ] when not (Index.mem t.units id) ->
      Index.add t.units step;
      Index.sample ~guard ~limit:16 t.goals literal
      |> List.iter (fun (goal : step) -> Option.iter (enqueue t) (ticket t goal.id))
  | _ :: _ :: _ when List.length step.clause <= 8 && not (Index.mem t.goals id) ->
      if Queue.length t.goal_order >= 256 then (
        let ((old, _) as previous) = Queue.take t.goal_order in
        Tbl.Pair.remove t.saved previous;
        if ticket t old = Some previous then Index.remove t.goals old);
      Index.add t.goals step;
      Queue.add key t.goal_order;
      enqueue t key
  | _ -> ()

let remove t id =
  t.removed_entries <- id :: t.removed_entries;
  Option.iter (Tbl.Pair.remove t.saved) (ticket t id);
  Option.iter (fun e -> e.generation <- None) (Tbl.Int.find_opt t.entries id);
  Index.remove t.units id;
  Index.remove t.goals id

let has_work t = not (Queue.is_empty t.pending)

(* Each extension is ordinary binary resolution against a freshly scoped unit.
   Its substitution is applied to ALL remaining literals before another choice;
   separate matches can therefore never invent an inconsistent joint witness. *)
let plan ?(budget = 4096) ?(attempts = 64) ?seed t ~guard ~alive (target : step) =
  let exception Exhausted in
  let exception Closed of plan in
  let left = ref budget and trials = ref attempts in
  let tick () =
    guard ();
    decr left;
    if !left < 0 then raise Exhausted
  in
  let initial = { residual = target.clause; reverse = [] } in
  let best = ref (Option.value ~default:initial seed) and seen = Tbl.Clause.create 64 in
  let score p = (List.length p.residual, Clause.weight p.residual, List.length p.reverse) in
  let unifier = Unify.create ~guard:tick (Term.create ()) in
  let rec explore current =
    tick ();
    if score current < score !best then best := current;
    if current.residual = [] then raise (Closed current);
    if not (Tbl.Clause.mem seen current.residual) then (
      Tbl.Clause.add seen current.residual ();
      let choices =
        List.mapi
          (fun i literal -> (i, Index.sample ~guard:tick ~budget:32 ~limit:8 t.units literal))
          current.residual
        |> List.filter (fun (_, units) -> units <> [])
        |> List.stable_sort (fun (_, a) (_, b) -> compare (List.length a) (List.length b))
      in
      List.iter
        (fun (pivot, units) ->
          let scoped = Clause.scope 1 current.residual in
          let literal = List.nth scoped pivot in
          List.iter
            (fun (unit : step) ->
              tick ();
              match ticket t unit.id with
              | Some using when alive using ->
                  let other = List.hd (Clause.scope 2 unit.clause) in
                  List.iter
                    (fun equations ->
                      if !trials = 0 then raise Exhausted;
                      decr trials;
                      t.plan_trials <- t.plan_trials + 1;
                      Unify.solve unifier equations (fun sigma apply ->
                          let conclusion =
                            Clause.remove pivot scoped |> List.map (Clause.map_literal apply)
                          in
                          let residual = Clause.normalize conclusion in
                          if not (Clause.tautology_sorted residual) then
                            explore
                              {
                                residual;
                                reverse = { pivot; using; sigma; conclusion } :: current.reverse;
                              }))
                    (Calculus.equations literal.atom other.atom)
              | _ -> ())
            units)
        choices)
  in
  t.plans <- t.plans + 1;
  (* A saved witness must not monopolize a retry: reserve half of the work for
     alternative witnesses starting at the original, universally quantified goal. *)
  let roots = match seed with None -> [ initial ] | Some seed -> [ seed; initial ] in
  let exhausted = ref false in
  let result =
    try
      List.iter
        (fun root ->
          left := budget / List.length roots;
          trials := attempts / List.length roots;
          Tbl.Clause.clear seen;
          try explore root with Exhausted -> exhausted := true)
        roots;
      !best
    with Closed result -> result
  in
  if !exhausted then t.plan_exhausted <- t.plan_exhausted + 1;
  result

let wanted clause = List.map (fun l -> { l with positive = not l.positive }) clause

let saved t ~alive owner =
  match Tbl.Pair.find_opt t.saved owner with
  | Some p when alive owner && List.for_all (fun edge -> alive edge.using) p.reverse -> Some p
  | Some _ ->
      Tbl.Pair.remove t.saved owner;
      t.plan_invalidated <- t.plan_invalidated + 1;
      None
  | None -> None

(* This bounded estimate is only a scheduling hint. Matching fingerprints do not
   prove that the remaining conditions have a common substitution. *)
let priority t ~guard ~alive ~get ((id, _) as owner) =
  if not (alive owner && Index.mem t.goals id) then (max_int, max_int, infinity)
  else
    let clause = match saved t ~alive owner with Some p -> p.residual | None -> (get id).clause in
    let missing = ref 0 and choices = ref 0 and shared = ref 0 in
    let variables = Tbl.Pair.create 8 in
    List.iteri
      (fun i literal ->
        let count = List.length (Index.sample ~guard ~budget:16 ~limit:4 t.units literal) in
        if count = 0 then incr missing;
        choices := !choices + count;
        let rec term = function
          | V v -> (
              guard ();
              match Tbl.Pair.find_opt variables v with
              | None -> Tbl.Pair.add variables v i
              | Some j when j <> i && j <> -1 ->
                  incr shared;
                  Tbl.Pair.replace variables v (-1)
              | _ -> ())
          | Fn (_, args) ->
              guard ();
              List.iter term args
        in
        List.iter term (Clause.atom_terms literal.atom))
      clause;
    let entry = Tbl.Int.find t.entries id in
    let cost = Clause.weight clause + (!choices * (1 + !shared)) + entry.plan_cost in
    (!missing, List.length clause, float cost /. float (1 + entry.closed_credit))

let take_goal t ~guard ~alive ~get =
  let first = Queue.peek t.pending in
  t.choosing <- t.choosing + 1;
  let best = ref first and score = ref (max_int, max_int, infinity) in
  (if t.choosing mod 4 <> 0 then
     let exception Exhausted in
     let left = ref 1024 in
     let tick () =
       guard ();
       decr left;
       if !left < 0 then raise Exhausted
     in
     try
       Queue.to_seq t.pending |> Seq.take 8
       |> Seq.iter (fun owner ->
           let candidate = priority t ~guard:tick ~alive ~get owner in
           if candidate < !score then (
             best := owner;
             score := candidate))
     with Exhausted -> ());
  if !best <> first then t.plan_prioritized <- t.plan_prioritized + 1;
  let remaining = Queue.to_seq t.pending |> Seq.filter (( <> ) !best) |> List.of_seq in
  Queue.clear t.pending;
  List.iter (fun key -> Queue.add key t.pending) remaining;
  Tbl.Pair.remove t.queued !best;
  !best

let advance ?(redundant = fun _ _ -> false) t ~guard ~alive ~get ~record ~emit ~demand =
  if has_work t then (
    let ((id, _) as owner) = take_goal t ~guard ~alive ~get in
    if not (alive owner && Index.mem t.goals id) then t.plan_stale <- t.plan_stale + 1
    else
      let seed = saved t ~alive owner in
      if seed <> None then t.plan_reused <- t.plan_reused + 1;
      let before = t.plan_trials in
      let result = plan ?seed t ~guard ~alive (get id) in
      let entry = Tbl.Int.find t.entries id in
      entry.plan_cost <- (entry.plan_cost + t.plan_trials - before) / 2;
      if result.residual <> [] then demand ~guard (wanted result.residual);
      let path = List.rev result.reverse in
      if not (alive owner && List.for_all (fun edge -> alive edge.using) path) then (
        Tbl.Pair.remove t.saved owner;
        t.plan_stale <- t.plan_stale + 1)
      else if List.length result.residual >= 2 then (
        if path <> [] then (
          Tbl.Pair.replace t.saved owner result;
          t.plan_deferred <- t.plan_deferred + 1))
      else (
        Tbl.Pair.remove t.saved owner;
        (* A single step is already covered by normal resolution. Multi-step
         plans are committed only after checking every premise generation. *)
        if List.length path >= 2 || result.residual = [] then
          if redundant (id :: List.map (fun edge -> fst edge.using) path) result.residual then
            t.plan_redundant <- t.plan_redundant + 1
          else (
            t.plan_steps <- t.plan_steps + List.length path;
            if result.residual = [] then t.plan_closed <- t.plan_closed + 1;
            let rec commit parent = function
              | [] -> ()
              | edge :: rest ->
                  guard ();
                  let rule = Resolve (parent, edge.pivot, fst edge.using, 0, edge.sigma) in
                  if rest = [] then (
                    let previous = t.committing in
                    t.committing <- true;
                    Fun.protect
                      ~finally:(fun () -> t.committing <- previous)
                      (fun () -> emit edge.conclusion rule))
                  else commit (record edge.conclusion rule).id rest
            in
            commit id path)))

let request t ticket = function
  | [ literal ] ->
      let r = { ticket; wanted = { literal with positive = not literal.positive } } in
      (if Queue.length t.requests >= 128 then
         let old = Queue.take t.requests in
         let key = Clause.key old.wanted in
         let keep = List.filter (fun r -> r != old) (Tbl.Feature.find t.by_literal key) in
         if keep = [] then Tbl.Feature.remove t.by_literal key
         else Tbl.Feature.replace t.by_literal key keep);
      Queue.add r t.requests;
      let key = Clause.key r.wanted in
      Tbl.Feature.replace t.by_literal key
        (r :: Option.value ~default:[] (Tbl.Feature.find_opt t.by_literal key));
      t.requested <- t.requested + 1;
      Some r.wanted
  | _ -> None

let pressure ?(eligible = fun _ _ -> true) t ~guard ~alive clause =
  let exception Exhausted in
  let attempts = ref 8 and work = ref 512 in
  let tick () =
    guard ();
    decr work;
    if !work < 0 then raise Exhausted
  in
  let rec literals i = function
    | [] -> false
    | _ when i = 8 -> false
    | literal :: rest ->
        let candidates =
          Option.value ~default:[] (Tbl.Feature.find_opt t.by_literal (Clause.key literal))
        in
        let rec matching = function
          | [] -> false
          | r :: rs ->
              tick ();
              if not (alive r.ticket) then matching rs
              else if !attempts = 0 then false
              else (
                decr attempts;
                t.trials <- t.trials + 1;
                let a = (List.hd (Clause.scope 1 [ literal ])).atom
                and b = (List.hd (Clause.scope 2 [ r.wanted ])).atom in
                let matched = ref false in
                Term.clear t.scratch;
                let u = Unify.create ~guard:tick t.scratch in
                List.iter
                  (fun equations ->
                    Unify.solve u ~accept:(eligible i) equations (fun _ _ -> matched := true))
                  (Calculus.equations a b);
                !matched || matching rs)
        in
        matching candidates || literals (i + 1) rest
  in
  let matched = try literals 0 clause with Exhausted -> false in
  if matched then t.matches <- t.matches + 1;
  if matched then 8 else 0

let credit t id = match Tbl.Int.find_opt t.entries id with Some e -> e.credit | None -> 0

let reward ?(closed = false) t ~get ~promote ids amount =
  let seen = Tbl.Int.create 16 and left = ref (if closed then 64 else 16) in
  let rec visit depth amount id =
    if depth >= 0 && amount > 0 && !left > 0 && not (Tbl.Int.mem seen id) then (
      decr left;
      Tbl.Int.add seen id ();
      (match Tbl.Int.find_opt t.entries id with
      | None -> ()
      | Some e ->
          if closed then (
            e.closed_credit <- min 64 (e.closed_credit + amount);
            if e.planned && not e.useful then (
              e.useful <- true;
              t.plan_useful <- t.plan_useful + 1));
          let gain = min amount (64 - e.credit) in
          e.credit <- e.credit + gain;
          t.progress <- t.progress + gain;
          promote id e.credit);
      try
        List.iter
          (visit (depth - 1) (if closed then max 1 (amount / 2) else amount / 2))
          (Wire.parents (get id).rule)
      with Not_found -> ())
  in
  List.iter (visit (if closed then 8 else 3) amount) ids

let observe_batch t id ~seconds ~generated =
  Option.iter
    (fun e ->
      e.batches <- e.batches + 1;
      e.seconds <- e.seconds +. seconds +. (float generated *. 0.00001))
    (Tbl.Int.find_opt t.entries id)

let rank t id =
  match Tbl.Int.find_opt t.entries id with
  | None -> 0.
  | Some e -> float e.credit /. sqrt (1. +. (1000. *. e.seconds) +. float e.batches)

(* [quiet]: no id that [keep] accepted at the previous collection has been dropped since. Then
   only the entries registered since can fail [keep]; when none does, the entry filter would
   drop nothing and is skipped.

   [keep] is the engine's retained-index membership, and an id leaves that index only through a
   deactivation, which calls [remove]. After a collection every entry passes [keep] (the filter
   drops the others, and a quiet collection changes nothing that passed), so an entry that fails
   [keep] now was registered since ([fresh_entries]) or removed since ([removed_entries]). Only
   those are tested: the other entries would pass and stay. [Tbl.Int.remove] of each failing
   entry leaves the table exactly as the full filter did, binding for binding and in the same
   bucket order (every id has one binding, and both keep the order of the others). With
   [~exhaustive:true] every entry, unit and goal is tested, as before (the reference of the unit
   tests). *)
let collect ?(quiet = false) ?(exhaustive = false) t ~keep ~alive =
  let fresh = t.fresh_entries and removed = t.removed_entries in
  t.fresh_entries <- [];
  t.removed_entries <- [];
  if not (quiet && List.for_all keep fresh) then (
    if exhaustive then
      Tbl.Int.filter_map_inplace (fun id e -> if keep id then Some e else None) t.entries
    else
      let drop id =
        if (not (keep id)) && Tbl.Int.mem t.entries id then Tbl.Int.remove t.entries id
      in
      List.iter drop fresh;
      List.iter drop removed);
  Tbl.Feature.clear t.by_literal;
  Shared.filter_queue
    (fun r ->
      alive r.ticket
      &&
      let key = Clause.key r.wanted in
      Tbl.Feature.replace t.by_literal key
        (r :: Option.value ~default:[] (Tbl.Feature.find_opt t.by_literal key));
      true)
    t.requests;
  (* The units and goals are clauses the engine noted right after retaining them, and a
     deactivation removes them ([remove]), so as with the entries only the ids registered or
     removed since can fail [keep]: removing those removes what the full scan removed. *)
  (if exhaustive then
     List.iter
       (fun index ->
         List.iter
           (fun (s : step) -> if not (keep s.id) then Index.remove index s.id)
           (Index.all index))
       [ t.units; t.goals ]
   else
     let drop id =
       if not (keep id) then (
         Index.remove t.units id;
         Index.remove t.goals id)
     in
     List.iter drop fresh;
     List.iter drop removed);
  Index.compact t.units;
  Index.compact t.goals;
  let prune queue =
    Shared.filter_queue (fun ((id, _) as key) -> alive key && Index.mem t.goals id) queue
  in
  prune t.goal_order;
  prune t.pending;
  Tbl.Pair.filter_map_inplace
    (fun ((id, _) as key) plan ->
      if
        alive key && Index.mem t.goals id
        && List.for_all (fun edge -> alive edge.using) plan.reverse
      then Some plan
      else (
        t.plan_invalidated <- t.plan_invalidated + 1;
        None))
    t.saved;
  Tbl.Pair.clear t.queued;
  Queue.iter (fun key -> Tbl.Pair.replace t.queued key ()) t.pending
