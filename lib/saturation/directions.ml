open Wire

(* Share work, not just calls: a long continuation cannot indefinitely delay a
   first trial. The age turn also bounds starvation after a costly slice.
   Inactive lanes accrue no credit. These are internal jobs, not solver modes. *)
module Schedule = struct
  type kind = First | Demand | Continue

  type lane = {
    mutable service : float;
    mutable work : int;
    mutable runs : int;
    mutable last : int;
  }

  type t = { lanes : lane array; mutable turns : int }

  let index = function First -> 0 | Demand -> 1 | Continue -> 2
  let share = function First -> 1. | Demand -> 2. | Continue -> 2.

  let create () =
    { lanes = Array.init 3 (fun _ -> { service = 0.; work = 0; runs = 0; last = -1 }); turns = 0 }

  let choose t ready =
    match ready with
    | [] -> None
    | first :: rest ->
        let floor = List.fold_left (fun n k -> min n t.lanes.(index k).service) infinity ready in
        Array.iteri
          (fun i lane ->
            if not (List.exists (fun k -> index k = i) ready) then
              lane.service <- max floor lane.service)
          t.lanes;
        let better a b =
          let a = t.lanes.(index a) and b = t.lanes.(index b) in
          if t.turns mod 8 = 7 then a.last < b.last else a.service < b.service
        in
        Some (List.fold_left (fun best k -> if better k best then k else best) first rest)

  let charge t kind work =
    let lane = t.lanes.(index kind) and work = max 1 work in
    lane.work <- lane.work + work;
    lane.service <- lane.service +. (float work /. share kind);
    lane.runs <- lane.runs + 1;
    lane.last <- t.turns;
    t.turns <- t.turns + 1
end

(* Bounded alternative directions. Keep the ordinary selection and indices
   stable; publish only the sampled conclusions with their primitive proofs.
   Entries and previews do not pin proof ancestors. *)
type proposal = { pivot : int; conclusions : (clause * rule) list }
type arm = { mutable attempts : int; mutable generated : int; mutable admitted : int }

type entry = {
  generation : int;
  mutable seen : int;
  mutable rounds : int;
  mutable admitted : int;
  mutable previous : int;
  mutable productive : bool;
  arms : arm Tbl.Int.t;
  mutable added : int list;
}

type t = {
  entries : entry Tbl.Int.t;
  queue : (int * int) Queue.t;
  probe : Calculus.t;
  mutable probes : int;
  mutable retries : int;
  mutable useful : int;
  mutable rejected : int;
  requested : (int * int) Queue.t;
  requests : unit Tbl.Pair.t;
  mutable demand_requests : int;
  mutable demand_selected : int;
}

(* The probe follows the worker's strategy and order; it shares the memo of
   default selections, which is a pure function of the clause. *)
let create ?strategy ?order ?memo () =
  {
    entries = Tbl.Int.create 128;
    queue = Queue.create ();
    probe = Calculus.create ~ordered:true ?strategy ?order ?memo (Term.create ());
    probes = 0;
    retries = 0;
    useful = 0;
    rejected = 0;
    requested = Queue.create ();
    requests = Tbl.Pair.create 128;
    demand_requests = 0;
    demand_selected = 0;
  }

let request t ticket =
  if not (Tbl.Pair.mem t.requests ticket) then (
    if Queue.length t.requested >= 128 then Tbl.Pair.remove t.requests (Queue.take t.requested);
    Queue.add ticket t.requested;
    Tbl.Pair.add t.requests ticket ();
    t.demand_requests <- t.demand_requests + 1)

let demanded t ~alive =
  let rec take left =
    if left = 0 || Queue.is_empty t.requested then None
    else
      let ticket = Queue.take t.requested in
      Tbl.Pair.remove t.requests ticket;
      if alive ticket then (
        t.demand_selected <- t.demand_selected + 1;
        Some ticket)
      else take (left - 1)
  in
  take 8

let pivots = function
  | Resolve (p, i, q, j, _) | Paramodulate (p, i, _, q, j, _, _) -> [ (p, i); (q, j) ]
  | Factor (p, i, _, _) | Equality_resolve (p, i, _) | Equality_factor (p, i, _, _, _, _) ->
      [ (p, i) ]
  | Input _ | Component _ -> []

let observe t status rule =
  pivots rule
  |> List.iter (fun (id, pivot) ->
      match Tbl.Int.find_opt t.entries id with
      | None -> ()
      | Some e -> (
          let a =
            match Tbl.Int.find_opt e.arms pivot with
            | Some a -> a
            | None ->
                let a = { attempts = 0; generated = 0; admitted = 0 } in
                Tbl.Int.add e.arms pivot a;
                a
          in
          match status with
          | "attempt" -> a.attempts <- a.attempts + 1
          | "conclusion" -> a.generated <- a.generated + 1
          | "admitted" ->
              a.admitted <- a.admitted + 1;
              e.admitted <- e.admitted + 1;
              if List.mem pivot e.added then t.useful <- t.useful + 1
          | _ -> ()))

let register t ~epoch ((id, generation) as ticket) =
  if not (Tbl.Int.mem t.entries id) then (
    Tbl.Int.add t.entries id
      {
        generation;
        seen = epoch;
        rounds = 0;
        admitted = 0;
        previous = 0;
        productive = false;
        arms = Tbl.Int.create 4;
        added = [];
      };
    Queue.add ticket t.queue)

let remove t id = Tbl.Int.remove t.entries id

let compact t ~alive =
  let tickets = Queue.to_seq t.queue |> Seq.filter alive |> List.of_seq in
  Queue.clear t.queue;
  List.iter (fun x -> Queue.add x t.queue) tickets;
  Tbl.Int.filter_map_inplace
    (fun id e -> if alive (id, e.generation) then Some e else None)
    t.entries;
  let requested = Queue.to_seq t.requested |> Seq.filter alive |> List.of_seq in
  Queue.clear t.requested;
  Tbl.Pair.clear t.requests;
  List.iter
    (fun ticket ->
      Queue.add ticket t.requested;
      Tbl.Pair.add t.requests ticket ())
    requested

let choose t ~guard ~calculus ~index ~equalities ~fresh (step : step) round =
  let chosen = Calculus.selected calculus step in
  match chosen with
  | None -> None
  | Some chosen ->
      let maximum =
        Option.map fst (Ordering.positive_maximum ~order:calculus.Calculus.order step.clause)
      in
      let candidates =
        List.mapi (fun i l -> (i, l)) step.clause
        |> List.filter (fun (i, l) ->
            (not (List.mem i chosen)) && ((not l.positive) || maximum = Some i))
      in
      let candidates =
        List.mapi (fun n x -> ((n + round) mod max 1 (List.length candidates), x)) candidates
        |> List.sort compare |> List.map snd |> List.to_seq |> Seq.take 4 |> List.of_seq
      in
      let best = ref None in
      t.probe.guard <- guard;
      Fun.protect
        ~finally:(fun () ->
          Tbl.Int.clear t.probe.selected;
          Term.clear t.probe.unifier.arena)
        (fun () ->
          List.iter
            (fun (pivot, literal) ->
              guard ();
              Tbl.Int.clear t.probe.selected;
              Tbl.Int.replace t.probe.selected step.id (Some [ pivot ]);
              let copy (s : step) =
                if s.id <> step.id then
                  Tbl.Int.replace t.probe.selected s.id (Calculus.selected calculus s)
              in
              let resolutions =
                Index.sample ~guard ~limit:4 ~budget:32 index literal
                |> List.to_seq
                |> Seq.flat_map (fun side ->
                    copy side;
                    Calculus.resolve_cursor t.probe step side)
              in
              let equations =
                Equality_index.matches ~guard ~budget:64 ~eligible:(( = ) pivot) equalities
                  ~variables:false step.clause
                |> List.to_seq
                |> Seq.flat_map (fun (side, outgoing, incoming) ->
                    copy side;
                    Calculus.interleave
                      (Calculus.paramodulate_cursor ~positions:outgoing t.probe step side)
                      (Calculus.paramodulate_cursor ~positions:incoming t.probe side step))
              in
              let stream = Calculus.interleave resolutions equations in
              let novel = Tbl.Clause.create 8 and attempts = ref 0 in
              let emit raw rule =
                let clause = Clause.normalize raw in
                if (not (Clause.tautology_sorted clause)) && fresh (Wire.parents rule) clause then
                  Tbl.Clause.replace novel clause (raw, rule)
              in
              stream |> Seq.take 16
              |> Seq.iter (fun f ->
                  incr attempts;
                  f emit);
              t.probes <- t.probes + !attempts;
              let rank (clause, _) = (List.length clause, Clause.weight clause) in
              let conclusions =
                Tbl.Clause.to_seq novel |> List.of_seq
                |> List.sort (fun a b ->
                    let c = compare (rank a) (rank b) in
                    if c = 0 then compare a b else c)
              in
              match conclusions with
              | [] -> t.rejected <- t.rejected + 1
              | (clause, conclusion) :: _ -> (
                  let score =
                    float (1 + Clause.weight step.clause)
                    /. float ((1 + !attempts) * (1 + Clause.weight clause))
                  in
                  match !best with
                  | Some (old, _) when old >= score -> ()
                  | _ -> best := Some (score, { pivot; conclusions = [ conclusion ] })))
            candidates);
      Option.map snd !best

let next t ~guard ~epoch ~alive ~get ~calculus ~index ~equalities ~fresh =
  let rec inspect left =
    if left = 0 || Queue.is_empty t.queue then None
    else (
      guard ();
      let ((id, generation) as ticket) = Queue.take t.queue in
      match Tbl.Int.find_opt t.entries id with
      | Some e when e.generation = generation && alive ticket ->
          Queue.add ticket t.queue;
          let changed = e.admitted > e.previous in
          let delay = (if e.productive then 128 else 16) * (1 lsl min 5 e.rounds) in
          if changed then (
            e.seen <- epoch;
            e.previous <- e.admitted;
            e.productive <- true;
            inspect (left - 1))
          else if epoch - e.seen < delay then inspect (left - 1)
          else (
            e.seen <- epoch;
            let selected = choose t ~guard ~calculus ~index ~equalities ~fresh (get id) e.rounds in
            e.rounds <- e.rounds + 1;
            match selected with
            | None -> None
            | Some proposal ->
                e.added <- List.sort_uniq compare (proposal.pivot :: e.added);
                t.retries <- t.retries + 1;
                Some (ticket, proposal))
      | _ -> inspect (left - 1))
  in
  inspect 8

(* Tickets refer to retained-index generations, not mutable unifier state. A
   retired or reactivated premise invalidates old work before it can emit. *)
type ticket = int * int
type group = { parents : ticket list; start : unit -> Calculus.inference Seq.t }

type work = {
  owner : ticket;
  mutable groups : group Seq.t;
  mutable current : (ticket list * Calculus.inference Seq.t) option;
}

let prepare ?(unit_retained = true) ?partners ~guard ~calculus ~index ~retained ~equalities ~indexed
    ~equality_indexed ~ticket (given : step) =
  let owner = ticket given in
  let group other start =
    { parents = (if other.id = given.id then [ owner ] else [ owner; ticket other ]); start }
  in
  let eligible = Calculus.candidates calculus given in
  (* A unit given also resolves with Passive, unless [unit_retained] is off (E). *)
  let resolution_index =
    if unit_retained && List.length given.clause = 1 then retained else index
  in
  let resolutions =
    if indexed then
      let hits = Index.cursor ~guard ~eligible resolution_index given.clause in
      (* [partners] puts the resolution partners in another prover's order (a Vampire slice
         member: its substitution tree's); the cursor's order otherwise. *)
      let hits =
        match partners with
        | None -> hits
        | Some order ->
            Seq.filter_map Fun.id hits |> List.of_seq |> order |> List.to_seq |> Seq.map Option.some
      in
      hits
      |> Seq.map (function
        | None -> group given (fun () -> Seq.empty)
        | Some (other, _) when other.id = given.id -> group given (fun () -> Seq.empty)
        | Some (other, position) ->
            group other (fun () ->
                Calculus.resolve_cursor ~positions:[ position ] calculus given other))
    else
      Index.brute_partners resolution_index
      |> List.to_seq
      |> Seq.map (fun other -> group other (fun () -> Calculus.resolve_cursor calculus given other))
  in
  let equalities =
    if equality_indexed then
      Equality_index.cursor ~eligible ~guard equalities
        ~variables:calculus.Calculus.variable_positions given.clause
      |> Seq.map (function
        | None -> group given (fun () -> Seq.empty)
        | Some (other, _, _) when other.id = given.id -> group given (fun () -> Seq.empty)
        | Some (other, outgoing, position) ->
            group other (fun () ->
                if outgoing then
                  Calculus.paramodulate_cursor ~positions:[ position ] calculus given other
                else Calculus.paramodulate_cursor ~positions:[ position ] calculus other given))
    else
      let count = Tbl.Int.length index.live in
      equalities.baseline <- equalities.baseline + count;
      equalities.candidates <- equalities.candidates + count;
      Index.all index |> List.to_seq
      |> Seq.map (fun other ->
          group other (fun () ->
              Seq.append
                (Calculus.paramodulate_cursor calculus given other)
                (Calculus.paramodulate_cursor calculus other given)))
  in
  {
    owner;
    current = None;
    groups =
      Seq.append
        (List.to_seq
           [
             group given (fun () -> Calculus.equality_factor_cursor calculus given);
             group given (fun () -> Calculus.resolve_cursor calculus given given);
             group given (fun () -> Calculus.paramodulate_cursor calculus given given);
           ])
        (Calculus.interleave resolutions equalities);
  }

(* Yield only after a complete attempt, including recursive shortening and
   rollback. Resumed work never carries arena handles across collection. *)
let advance ~quantum ~guard ~alive ~yield ~cancelled ~emit work =
  let rec advance left =
    guard ();
    if not (alive work.owner) then (
      cancelled ();
      true)
    else if left <= 0 || yield () then false
    else
      match work.current with
      | None -> (
          match work.groups () with
          | Seq.Nil -> true
          | Seq.Cons (group, rest) ->
              work.groups <- rest;
              if List.for_all alive group.parents then
                work.current <- Some (group.parents, group.start ())
              else cancelled ();
              advance (left - 1))
      | Some (parents, cursor) -> (
          if not (List.for_all alive parents) then (
            work.current <- None;
            cancelled ();
            advance (left - 1))
          else
            match cursor () with
            | Seq.Nil ->
                work.current <- None;
                advance (left - 1)
            | Seq.Cons (attempt, rest) ->
                work.current <- Some (parents, rest);
                attempt emit;
                advance (left - 1))
  in
  advance quantum
