open Wire

(* A private consequence is never admitted on its own. Selected ordinary work
   requests it, and reconstruction requires a successful inference with that
   generation-checked consumer. Acceptance adds no priority feedback, and this
   store contributes no roots to the ordinary proof collector. *)
type acceptance = Retained | Unconditional_empty | Conditional_empty
type ticket = Goal.ticket
type request_id = { serial : int }

type consumer = {
  step : step;
  ticket : ticket;
  support : int list;
  selection : int list option;
  request : request_id;
}

type candidate =
  | Resolution of consumer * (int * int)
  | Outgoing of consumer * Equality_index.position
  | Incoming of consumer * Equality_index.position

type result = {
  consumer : consumer;
  raw : clause;
  rule : rule;
  mutable spent : bool;
  mutable accepted : bool;
}

type offer = { proof : Goal.recipe; materialized : int Tbl.Int.t }

(* Where a request cursor stands, as in Goal.scan, so that a cursor dropped
   under memory pressure continues exactly where it stopped. *)
type marks = {
  resolution : Index.mark;
  equality : Equality_index.mark;
  resolution_taken : int ref;
  equality_taken : int ref;
}

(* A request belongs to one selected ordinary work object, not merely its owner
   clause. Completion seals the private-recipe frontier. The remaining finite
   response cursor must drain before the request disappears; later offers cannot
   prolong it. Open ordinary continuations can still see newly arriving recipes. *)
type request = {
  id : request_id;
  consumer : consumer;
  mutable sealed : (int * int) option;
  mutable cursor : (offer * candidate) option Seq.t option;
  mutable marks : marks option;
  mutable pending : (offer * result) list;
  mutable seen : int * int;
  mutable cursor_epoch : int * int;
  mutable queued : bool;
}

type request_metrics = {
  mutable opened : int;
  mutable sealed : int;
  mutable drained : int;
  mutable invalidated : int;
  mutable slices : int;
  mutable resumed : int;
}

type metrics = {
  mutable offered : int;
  mutable merged : int;
  mutable invalidated : int;
  mutable blocked : int;
  mutable slices : int;
  mutable resumed : int;
  mutable resolution_attempts : int;
  mutable outgoing_attempts : int;
  mutable incoming_attempts : int;
  mutable conclusions : int;
  mutable tautologies : int;
  mutable stale_results : int;
  mutable ancestor_recorded : int;
  mutable emit_calls : int;
  mutable direct_recorded : int;
  mutable accepted : int;
  mutable retained : int;
  mutable unconditional : int;
  mutable conditional : int;
  mutable feedback : int;
}

type t = {
  calculus : Calculus.t;
  terms : Term.arena;
  offers : offer Tbl.Int.t;
  mutable fresh_offers : offer list;  (** offers added since the last [collect] *)
  memo : int Tbl.Clause_ints.t;
  ancestor_ids : unit Tbl.Int.t;
  direct_ids : unit Tbl.Int.t;
  accepted_ids : unit Tbl.Int.t;
  metrics : metrics;
  recipe_index : Index.t;
  recipe_equality : Equality_index.t;
  requests : request Tbl.Int.t;
  request_owners : int list Tbl.Int.t;
  request_ready : int Queue.t;
  request_sweep : int Queue.t;
  mutable request_refresh_left : int;
  mutable next_request : int;
  request_metrics : request_metrics;
}

let create ~(calculus : Calculus.t) () =
  let terms = Term.create () in
  let own =
    Calculus.create ~variable_positions:calculus.variable_positions ~ordered:calculus.ordered
      ~selection:calculus.selection ~strategy:calculus.strategy ~order:calculus.order
      ~memo:calculus.memo terms
  in
  {
    (* Selection changes made by the ordinary engine apply to consumers here.
       The unifier and effort counters remain independent of ordinary scheduling. *)
    calculus = { own with selected = calculus.selected };
    terms;
    offers = Tbl.Int.create 128;
    fresh_offers = [];
    memo = Tbl.Clause_ints.create 128;
    ancestor_ids = Tbl.Int.create 128;
    direct_ids = Tbl.Int.create 128;
    accepted_ids = Tbl.Int.create 128;
    metrics =
      {
        offered = 0;
        merged = 0;
        invalidated = 0;
        blocked = 0;
        slices = 0;
        resumed = 0;
        resolution_attempts = 0;
        outgoing_attempts = 0;
        incoming_attempts = 0;
        conclusions = 0;
        tautologies = 0;
        stale_results = 0;
        ancestor_recorded = 0;
        emit_calls = 0;
        direct_recorded = 0;
        accepted = 0;
        retained = 0;
        unconditional = 0;
        conditional = 0;
        feedback = 0;
      };
    recipe_index = Index.create ();
    recipe_equality = Equality_index.create ();
    requests = Tbl.Int.create 128;
    request_owners = Tbl.Int.create 128;
    request_ready = Queue.create ();
    request_sweep = Queue.create ();
    request_refresh_left = 0;
    next_request = 0;
    request_metrics =
      { opened = 0; sealed = 0; drained = 0; invalidated = 0; slices = 0; resumed = 0 };
  }

let recipe_epoch t = (t.recipe_index.generation, t.recipe_equality.generation)
let key (p : Goal.recipe) = (p.step.clause, p.support)
let valid ~alive (p : Goal.recipe) = List.for_all alive p.leaves

let forget t id =
  match Tbl.Int.find_opt t.offers id with
  | None -> ()
  | Some o ->
      if Tbl.Clause_ints.find_opt t.memo (key o.proof) = Some id then
        Tbl.Clause_ints.remove t.memo (key o.proof);
      Tbl.Int.remove t.offers id;
      Index.remove t.recipe_index id;
      Equality_index.remove t.recipe_equality id;
      t.metrics.invalidated <- t.metrics.invalidated + 1

let offer t ~guard ~alive ~blocked (proof : Goal.recipe) =
  guard ();
  if proof.height <= 0 || proof.step.id >= 0 || proof.step.clause = [] then
    invalid_arg "Goal_transfer.offer: expected a nonempty virtual consequence";
  t.metrics.offered <- t.metrics.offered + 1;
  if not (valid ~alive proof) then t.metrics.invalidated <- t.metrics.invalidated + 1
  else if blocked proof.support then t.metrics.blocked <- t.metrics.blocked + 1
  else
    let old =
      Option.bind (Tbl.Clause_ints.find_opt t.memo (key proof)) (Tbl.Int.find_opt t.offers)
    in
    match old with
    | Some o when valid ~alive o.proof -> t.metrics.merged <- t.metrics.merged + 1
    | _ ->
        Option.iter (fun o -> forget t o.proof.step.id) old;
        let o = { proof; materialized = Tbl.Int.create 16 } in
        Tbl.Int.add t.offers proof.step.id o;
        t.fresh_offers <- o :: t.fresh_offers;
        Tbl.Clause_ints.replace t.memo (key proof) proof.step.id;
        Index.add t.recipe_index proof.step;
        Equality_index.add t.recipe_equality proof.step;
        t.request_refresh_left <- Queue.length t.request_sweep

let enqueue_request t (q : request) =
  if not q.queued then (
    q.queued <- true;
    Queue.add q.id.serial t.request_ready)

let retire_request t ~drained serial =
  match Tbl.Int.find_opt t.requests serial with
  | None -> ()
  | Some q ->
      Tbl.Int.remove t.requests serial;
      let owner = q.consumer.step.id in
      let others =
        Option.value ~default:[] (Tbl.Int.find_opt t.request_owners owner)
        |> List.filter (( <> ) serial)
      in
      if others = [] then Tbl.Int.remove t.request_owners owner
      else Tbl.Int.replace t.request_owners owner others;
      if drained then t.request_metrics.drained <- t.request_metrics.drained + 1
      else t.request_metrics.invalidated <- t.request_metrics.invalidated + 1

let invalidate_requests t owner =
  Option.value ~default:[] (Tbl.Int.find_opt t.request_owners owner)
  |> List.iter (retire_request t ~drained:false)

let selection_changed = invalidate_requests
let remove = invalidate_requests

let current t ~alive (c : consumer) =
  alive c.ticket
  && c.selection = Calculus.selected t.calculus c.step
  && Option.fold ~none:false
       ~some:(fun (q : request) -> q.consumer == c)
       (Tbl.Int.find_opt t.requests c.request.serial)

let request t ?previous ~support ((id, _) as ticket) (step : step) =
  if id < 0 || id <> step.id then invalid_arg "Goal_transfer.request: invalid ordinary ticket";
  let selection = Calculus.selected t.calculus step in
  let previous = Option.bind previous (fun token -> Tbl.Int.find_opt t.requests token.serial) in
  match previous with
  | Some q when q.consumer.ticket = ticket && q.consumer.selection = selection && q.sealed = None ->
      q.id
  | _ ->
      Option.iter (fun (q : request) -> retire_request t ~drained:false q.id.serial) previous;
      if t.next_request = max_int then invalid_arg "Goal_transfer.request: serial overflow";
      t.next_request <- t.next_request + 1;
      let token = { serial = t.next_request } in
      let q =
        {
          id = token;
          consumer = { step; ticket; support; selection; request = token };
          sealed = None;
          cursor = None;
          marks = None;
          pending = [];
          seen = (0, 0);
          cursor_epoch = (0, 0);
          queued = false;
        }
      in
      Tbl.Int.add t.requests token.serial q;
      let owners = Option.value ~default:[] (Tbl.Int.find_opt t.request_owners id) in
      Tbl.Int.replace t.request_owners id (token.serial :: owners);
      Queue.add token.serial t.request_sweep;
      t.request_metrics.opened <- t.request_metrics.opened + 1;
      enqueue_request t q;
      token

let complete_request t token =
  match Tbl.Int.find_opt t.requests token.serial with
  | Some q when q.sealed = None ->
      q.sealed <- Some (recipe_epoch t);
      t.request_metrics.sealed <- t.request_metrics.sealed + 1;
      enqueue_request t q
  | _ -> ()

let consumer_count t = Tbl.Int.length t.requests

let request_counts t =
  Tbl.Int.fold
    (fun _ (q : request) (open_, draining) ->
      if q.sealed = None then (open_ + 1, draining) else (open_, draining + 1))
    t.requests (0, 0)

let has_work t = t.request_refresh_left > 0 || not (Queue.is_empty t.request_ready)
let effort t = t.calculus.attempts + t.recipe_index.postings + t.recipe_equality.postings

let actual table (step : step) =
  if step.id < 0 then invalid_arg "Goal_transfer: recorder returned a virtual ID";
  Tbl.Int.replace table step.id ()

let reconstruct t ~guard ~alive ~blocked ~record o consumer =
  let exception Stale in
  let check () =
    guard ();
    if
      (not (valid ~alive o.proof && current t ~alive consumer))
      || blocked (Goal.union o.proof.support consumer.support)
    then raise Stale
  in
  let rec materialize (p : Goal.recipe) =
    check ();
    if p.height = 0 then p.step.id
    else
      match Tbl.Int.find_opt o.materialized p.step.id with
      | Some id -> id
      | None ->
          List.iter (fun parent -> ignore (materialize parent)) p.parents;
          check ();
          let step = record p.raw (Goal.map_rule lookup p.step.rule) in
          actual t.ancestor_ids step;
          t.metrics.ancestor_recorded <- t.metrics.ancestor_recorded + 1;
          Tbl.Int.add o.materialized p.step.id step.id;
          step.id
  and lookup id = if id >= 0 then id else Tbl.Int.find o.materialized id in
  try
    ignore (materialize o.proof);
    check ();
    Some lookup
  with Stale -> None

let consume t ~guard ~alive ~blocked ~record ~emit o (result : result) =
  match reconstruct t ~guard ~alive ~blocked ~record o result.consumer with
  | None -> t.metrics.stale_results <- t.metrics.stale_results + 1
  | Some lookup ->
      let recorded step =
        actual t.direct_ids step;
        t.metrics.direct_recorded <- t.metrics.direct_recorded + 1;
        result.spent <- true
      in
      let accepted kind step =
        actual t.accepted_ids step;
        (match kind with
        | Retained -> t.metrics.retained <- t.metrics.retained + 1
        | Unconditional_empty -> t.metrics.unconditional <- t.metrics.unconditional + 1
        | Conditional_empty -> t.metrics.conditional <- t.metrics.conditional + 1);
        result.spent <- true;
        if not result.accepted then (
          result.accepted <- true;
          t.metrics.accepted <- t.metrics.accepted + 1)
      in
      t.metrics.emit_calls <- t.metrics.emit_calls + 1;
      emit ~recorded ~accepted result.raw (Goal.map_rule lookup result.rule)

let infer t ~guard ~alive ~blocked o candidate =
  let c, sequence =
    match candidate with
    | Resolution (c, position) ->
        t.metrics.resolution_attempts <- t.metrics.resolution_attempts + 1;
        (c, Calculus.resolve_cursor ~positions:[ position ] t.calculus o.proof.step c.step)
    | Outgoing (c, position) ->
        t.metrics.outgoing_attempts <- t.metrics.outgoing_attempts + 1;
        (c, Calculus.paramodulate_cursor ~positions:[ position ] t.calculus o.proof.step c.step)
    | Incoming (c, position) ->
        t.metrics.incoming_attempts <- t.metrics.incoming_attempts + 1;
        (c, Calculus.paramodulate_cursor ~positions:[ position ] t.calculus c.step o.proof.step)
  in
  guard ();
  if not (valid ~alive o.proof && current t ~alive c) then []
  else if blocked (Goal.union o.proof.support c.support) then (
    t.metrics.blocked <- t.metrics.blocked + 1;
    [])
  else
    let results = ref [] in
    Calculus.run sequence (fun raw rule ->
        let clause = Clause.normalize raw in
        t.metrics.conclusions <- t.metrics.conclusions + 1;
        if Clause.tautology_sorted clause then t.metrics.tautologies <- t.metrics.tautologies + 1
        else results := { consumer = c; raw; rule; spent = false; accepted = false } :: !results);
    List.rev !results

let request_target t (q : request) = Option.value ~default:(recipe_epoch t) q.sealed

let refresh_requests t ~guard ~alive =
  if t.request_refresh_left > 0 && not (Queue.is_empty t.request_sweep) then (
    guard ();
    let serial = Queue.take t.request_sweep in
    t.request_refresh_left <- max 0 (t.request_refresh_left - 1);
    match Tbl.Int.find_opt t.requests serial with
    | None -> ()
    | Some q ->
        if not (current t ~alive q.consumer) then retire_request t ~drained:false serial
        else (
          Queue.add serial t.request_sweep;
          if q.seen <> request_target t q then enqueue_request t q))

(* [from] continues a cursor dropped under memory pressure from its marks. *)
let request_cursor ?from t ~guard (q : request) =
  let marks =
    match from with
    | Some marks -> marks
    | None ->
        {
          resolution = Index.mark ();
          equality = Equality_index.mark ();
          resolution_taken = ref 0;
          equality_taken = ref 0;
        }
  in
  q.marks <- Some marks;
  let resumes = from <> None in
  let upto = Option.map (fun _ -> fst q.cursor_epoch) from
  and upto_equality = Option.map (fun _ -> snd q.cursor_epoch) from in
  let within table limit (step : step) =
    Option.fold ~none:false
      ~some:(fun generation -> generation <= limit)
      (Tbl.Int.find_opt table step.id)
  in
  let offered (step : step) = Tbl.Int.find_opt t.offers step.id in
  let resolution =
    Index.cursor ~since:(fst q.seen) ?upto
      ?from:(Option.map (fun m -> m.resolution) from)
      ~mark:marks.resolution ~guard t.recipe_index q.consumer.step.clause
    |> Seq.map (fun value ->
        Option.bind value (fun (step, (consumer_position, recipe_position)) ->
            if within t.recipe_index.live (fst q.cursor_epoch) step then
              Option.map
                (fun o -> (o, Resolution (q.consumer, (recipe_position, consumer_position))))
                (offered step)
            else None))
    |> Index.follow ~resumes
         ~visits:(fun () -> marks.resolution.visits)
         ~position:(fun () -> Index.position marks.resolution)
         ~taken:marks.resolution_taken
  in
  let equality =
    Equality_index.cursor ~since:(snd q.seen) ?upto:upto_equality
      ?from:(Option.map (fun m -> m.equality) from)
      ~mark:marks.equality ~guard t.recipe_equality ~variables:t.calculus.variable_positions
      q.consumer.step.clause
    |> Seq.map (fun value ->
        Option.bind value (fun (step, outgoing, position) ->
            if within t.recipe_equality.live (snd q.cursor_epoch) step then
              Option.map
                (fun o ->
                  ( o,
                    if outgoing then Incoming (q.consumer, position)
                    else Outgoing (q.consumer, position) ))
                (offered step)
            else None))
    |> Index.follow ~resumes
         ~visits:(fun () -> marks.equality.visits)
         ~position:(fun () -> Equality_index.position marks.equality)
         ~taken:marks.equality_taken
  in
  Calculus.interleave resolution equality

let advance ?(attempts = 16) t ~guard ~alive ~blocked ~record ~emit =
  guard ();
  t.calculus.guard <- guard;
  t.metrics.slices <- t.metrics.slices + 1;
  t.request_metrics.slices <- t.request_metrics.slices + 1;
  refresh_requests t ~guard ~alive;
  if not (Queue.is_empty t.request_ready) then
    let serial = Queue.take t.request_ready in
    match Tbl.Int.find_opt t.requests serial with
    | None -> ()
    | Some q ->
        q.queued <- false;
        if not (current t ~alive q.consumer) then retire_request t ~drained:false serial
        else
          let finished = ref false in
          Fun.protect
            ~finally:(fun () ->
              if (not !finished) && Tbl.Int.mem t.requests serial then enqueue_request t q)
            (fun () ->
              (match (q.cursor, q.marks) with
              | Some _, _ ->
                  t.metrics.resumed <- t.metrics.resumed + 1;
                  t.request_metrics.resumed <- t.request_metrics.resumed + 1
              | None, Some from ->
                  (* Dropped under memory pressure: continue the same scan. *)
                  t.metrics.resumed <- t.metrics.resumed + 1;
                  t.request_metrics.resumed <- t.request_metrics.resumed + 1;
                  q.cursor <- Some (request_cursor ~from t ~guard:(fun () -> t.calculus.guard ()) q)
              | None, None ->
                  q.cursor_epoch <- request_target t q;
                  q.cursor <- Some (request_cursor t ~guard:(fun () -> t.calculus.guard ()) q));
              let left = ref attempts in
              while !left > 0 && not !finished do
                guard ();
                decr left;
                if not (current t ~alive q.consumer) then (
                  retire_request t ~drained:false serial;
                  finished := true)
                else
                  match q.pending with
                  | (o, result) :: rest ->
                      Fun.protect
                        ~finally:(fun () -> if result.spent then q.pending <- rest)
                        (fun () ->
                          consume t ~guard ~alive ~blocked ~record ~emit o result;
                          q.pending <- rest)
                  | [] -> (
                      let sequence = Option.get q.cursor in
                      match sequence () with
                      | Seq.Nil ->
                          q.seen <- q.cursor_epoch;
                          q.cursor <- None;
                          q.marks <- None;
                          finished := true;
                          if q.seen <> request_target t q then enqueue_request t q
                          else if q.sealed <> None then retire_request t ~drained:true serial
                      | Seq.Cons (candidate, rest) ->
                          let results =
                            Option.fold ~none:[]
                              ~some:(fun (o, candidate) ->
                                if not (valid ~alive o.proof) then (
                                  forget t o.proof.step.id;
                                  [])
                                else
                                  infer t ~guard ~alive ~blocked o candidate
                                  |> List.map (fun result -> (o, result)))
                              candidate
                          in
                          q.pending <- results;
                          q.cursor <- Some rest)
              done)

let prune queue keep = Shared.filter_queue keep queue

(* [quiet]: as in Goal.collect, no ticket [alive] accepted at the previous collection has died
   since, so only the offers added since can be invalid; when none is, the offer scan would forget
   nothing and is skipped. Requests also depend on the selection memo and are always scanned. *)
let collect ?(quiet = false) t ~alive =
  if Unify.mark t.calculus.unifier <> 0 then
    invalid_arg "Goal_transfer.collect: inference in progress";
  let fresh = t.fresh_offers in
  t.fresh_offers <- [];
  (if not (quiet && List.for_all (fun o -> valid ~alive o.proof) fresh) then
     let dead =
       Tbl.Int.fold (fun id o ids -> if valid ~alive o.proof then ids else id :: ids) t.offers []
     in
     List.iter (forget t) dead);
  let dead =
    Tbl.Int.fold
      (fun serial (q : request) ids -> if current t ~alive q.consumer then ids else serial :: ids)
      t.requests []
  in
  List.iter (retire_request t ~drained:false) dead;
  (* Ordinary GC may reclaim every explanation node, including a partially
     reconstructed DAG. Forget actual IDs before reclaim, never pin them. The
     immutable virtual recipe and its live leaf tickets suffice to resume. *)
  Tbl.Int.iter (fun _ o -> Tbl.Int.clear o.materialized) t.offers;
  prune t.request_ready (fun serial ->
      Option.fold ~none:false
        ~some:(fun (q : request) -> q.queued)
        (Tbl.Int.find_opt t.requests serial));
  prune t.request_sweep (Tbl.Int.mem t.requests);
  t.request_refresh_left <- min t.request_refresh_left (Queue.length t.request_sweep);
  Index.compact t.recipe_index;
  Equality_index.compact t.recipe_equality;
  Term.clear t.terms

(* Memory pressure: as Goal.drop_cursors, forget suspended request cursors;
   each continues from its marks when the request next runs. *)
let drop_cursors t =
  Tbl.Int.fold
    (fun _ (q : request) dropped ->
      match (q.cursor, q.marks) with
      | Some _, Some marks ->
          q.cursor <- None;
          Equality_index.detach marks.equality;
          dropped + 1
      | _ -> dropped)
    t.requests 0
