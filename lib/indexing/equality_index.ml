open Wire

(* Equal terms share one posting per clause, retaining every literal/side/path.
   This avoids repeating a fingerprint and a full term comparison per occurrence. *)
type key = (symbol * int) option
type location = { literal : int; reverse : bool; path : int list }

type posting = {
  step : step;
  generation : int;
  term : term;
  locations : location list;
  fingerprint : Index.Fingerprint.t;
  cell : Index.cell;  (** the liveness of the [add] that made it, as in Index *)
}

type position = int * bool * int * int list

type t = {
  sources : posting list Tbl.Head_opt.t;
  targets : posting list Tbl.Head_opt.t;
  live : int Tbl.Int.t;
  cells : Index.cell Tbl.Int.t;  (** the cell of each live id's current generation *)
  mutable dirty_sources : key list;  (** as Index.dirty, per table *)
  mutable dirty_targets : key list;
  mutable stale : int;  (** adds removed or superseded since the last [compact] *)
  mutable generation : int;
  fingerprint : bool;
  mutable baseline : int;
  mutable candidates : int;
  mutable postings : int;
  mutable fingerprint_rejected : int;
  mutable occurrences : int;
}

let create ?(fingerprint = true) () =
  {
    sources = Tbl.Head_opt.create 32;
    targets = Tbl.Head_opt.create 32;
    live = Tbl.Int.create 128;
    cells = Tbl.Int.create 128;
    dirty_sources = [];
    dirty_targets = [];
    stale = 0;
    generation = 0;
    fingerprint;
    baseline = 0;
    candidates = 0;
    postings = 0;
    fingerprint_rejected = 0;
    occurrences = 0;
  }

let key = function V _ -> None | Fn (s, ts) -> Some (s, List.length ts)

let locations ?(eligible = fun _ -> true) ~sources ~variables clause =
  let groups = Tbl.Term.create 16 in
  let add term location =
    let old = Option.value ~default:[] (Tbl.Term.find_opt groups term) in
    Tbl.Term.replace groups term (location :: old)
  in
  List.iteri
    (fun literal l ->
      if eligible literal then
        if sources then
          match (l.positive, l.atom) with
          | true, E (s, t) when s <> t ->
              add s { literal; reverse = false; path = [] };
              add t { literal; reverse = true; path = [] }
          | _ -> ()
        else
          List.iter
            (fun (path, term) -> add term { literal; reverse = false; path })
            (Clause.positions ~variables l))
    clause;
  Tbl.Term.fold (fun term positions acc -> (term, positions) :: acc) groups []

(* Every bucket key a posting of [clause] can have: those of its atoms' argument subterms (sources
   are equation sides, targets any subterm), variables included. *)
let rec term_keys acc t =
  let acc = key t :: acc in
  match t with V _ -> acc | Fn (_, ts) -> List.fold_left term_keys acc ts

(* An add leaves the index (its id is removed or added again): its postings become stale. As in
   Index, the buckets are recomputed from the clause (a superset of those posted to). *)
let retire t (cell : Index.cell) =
  cell.alive <- false;
  t.stale <- t.stale + 1;
  let keys =
    List.fold_left
      (fun acc l -> List.fold_left term_keys acc (Clause.atom_terms l.atom))
      [] cell.clause
  in
  t.dirty_sources <- List.rev_append keys t.dirty_sources;
  t.dirty_targets <- List.rev_append keys t.dirty_targets

let add ?eligible ?(targets = true) t (s : step) =
  if t.generation = max_int then invalid_arg "Equality_index: generation overflow";
  t.generation <- t.generation + 1;
  let generation = t.generation in
  Tbl.Int.replace t.live s.id generation;
  Option.iter (retire t) (Tbl.Int.find_opt t.cells s.id);
  let cell = { Index.alive = true; clause = s.clause; postings = 0 } in
  Tbl.Int.replace t.cells s.id cell;
  let post table (term, locations) =
    let k = key term in
    let fingerprint = if t.fingerprint then Index.Fingerprint.term term else [||] in
    let locations =
      match eligible with
      | None -> locations
      | Some eligible ->
          if List.for_all (fun p -> eligible p.literal) locations then locations
          else List.filter (fun p -> eligible p.literal) locations
    in
    let p = { step = s; generation; term; locations; fingerprint; cell } in
    Tbl.Head_opt.replace table k (p :: Option.value ~default:[] (Tbl.Head_opt.find_opt table k))
  in
  List.iter (post t.sources) (locations ?eligible ~sources:true ~variables:true s.clause);
  (* Keep all target terms for backward rewriting, even when no occurrence is
     eligible for inference. Empty location lists are skipped only by matches. *)
  if targets then List.iter (post t.targets) (locations ~sources:false ~variables:true s.clause)

let remove t id =
  Tbl.Int.remove t.live id;
  Option.iter (retire t) (Tbl.Int.find_opt t.cells id);
  Tbl.Int.remove t.cells id

(* Whether [live] still maps the posting's id to its generation, read from its cell. *)
let[@inline] current (_ : t) p = p.cell.Index.alive

(* Every bucket filtered: the reference for [compact] in the unit tests. *)
let compact_all t =
  let compact table =
    Tbl.Head_opt.filter_map_inplace
      (fun _ xs -> match Shared.filter (current t) xs with [] -> None | xs -> Some xs)
      table
  in
  t.dirty_sources <- [];
  t.dirty_targets <- [];
  t.stale <- 0;
  compact t.sources;
  compact t.targets

(* As Index.compact: only the buckets that removed or superseded adds posted to can change. *)
let compact t =
  if t.stale > 0 then (
    if
      (* With at least as many dirty marks as buckets, the full sweep costs no more. *)
      List.compare_length_with t.dirty_sources (Tbl.Head_opt.length t.sources) >= 0
      || List.compare_length_with t.dirty_targets (Tbl.Head_opt.length t.targets) >= 0
    then compact_all t
    else
      let compact table keys =
        let seen = Tbl.Head_opt.create 16 in
        List.iter
          (fun k ->
            if not (Tbl.Head_opt.mem seen k) then (
              Tbl.Head_opt.add seen k ();
              match Tbl.Head_opt.find_opt table k with
              | None -> ()
              | Some xs -> (
                  match Shared.filter (current t) xs with
                  | [] -> Tbl.Head_opt.remove table k
                  | ys -> if ys != xs then Tbl.Head_opt.replace table k ys)))
          keys
      in
      let sources = t.dirty_sources and targets = t.dirty_targets in
      t.dirty_sources <- [];
      t.dirty_targets <- [];
      t.stale <- 0;
      compact t.sources sources;
      compact t.targets targets)

let query ?(guard = fun () -> ()) ?(inference = false) t table ~variables term visit =
  let fingerprint = if t.fingerprint then Index.Fingerprint.term term else [||] in
  let inspect bucket =
    List.iter
      (fun p ->
        guard ();
        t.postings <- t.postings + 1;
        if current t p && ((not inference) || p.locations <> []) && (variables || key p.term <> None)
        then
          if t.fingerprint && not (Index.Fingerprint.compatible fingerprint p.fingerprint) then
            t.fingerprint_rejected <- t.fingerprint_rejected + 1
          else if Index.compatible term p.term then visit p)
      bucket
  in
  match key term with
  | None -> Tbl.Head_opt.iter (fun _ bucket -> inspect bucket) table
  | Some _ as k ->
      inspect (Option.value ~default:[] (Tbl.Head_opt.find_opt table k));
      if variables then inspect (Option.value ~default:[] (Tbl.Head_opt.find_opt table None))

let matches ?(guard = fun () -> ()) ?(budget = max_int) ?eligible t ~variables clause =
  let exception Exhausted in
  let remaining = ref budget in
  let guard () =
    guard ();
    if !remaining <= 0 then raise Exhausted;
    decr remaining
  in
  t.baseline <- t.baseline + Tbl.Int.length t.live;
  let found = Tbl.Int.create 16 in
  let collect outgoing needle_locations p =
    let out_, in_ =
      match Tbl.Int.find_opt found p.step.id with
      | Some (_, out_, in_) -> (out_, in_)
      | None ->
          let out_ = ref [] and in_ = ref [] in
          Tbl.Int.add found p.step.id (p.step, out_, in_);
          (out_, in_)
    in
    List.iter
      (fun needle ->
        List.iter
          (fun stored ->
            guard ();
            let source, target = if outgoing then (needle, stored) else (stored, needle) in
            let pair = (source.literal, source.reverse, target.literal, target.path) in
            let result = if outgoing then out_ else in_ in
            result := pair :: !result)
          p.locations)
      needle_locations
  in
  (try
     List.iter
       (fun (term, positions) ->
         query ~guard ~inference:true t t.targets ~variables term (collect true positions))
       (locations ?eligible ~sources:true ~variables:true clause);
     List.iter
       (fun (term, positions) ->
         query ~guard ~inference:true t t.sources ~variables:true term (collect false positions))
       (locations ?eligible ~sources:false ~variables clause)
   with Exhausted -> ());
  let result =
    Tbl.Int.fold
      (fun _ (s, out_, in_) acc ->
        let out_ = List.sort_uniq compare !out_ and in_ = List.sort_uniq compare !in_ in
        t.occurrences <- t.occurrences + List.length out_ + List.length in_;
        (s, out_, in_) :: acc)
      found []
    |> List.sort (fun ((a : step), _, _) (b, _, _) -> compare a.id b.id)
  in
  t.candidates <- t.candidates + List.length result;
  result

let partners t ~variables clause =
  List.map (fun (s, out_, in_) -> (s, out_ <> [], in_ <> [])) (matches t ~variables clause)

(* Where a cursor stands, as in Index.mark: the query being scanned, its
   current and later buckets, and the generation and ordinal of the posting
   entered last in the current bucket. [detach] keeps only the bucket keys,
   so a dropped cursor holds no posting list. *)
type mark = {
  mutable query : int;
  mutable buckets : (key * posting list) list;
  mutable keys : key list;
  mutable entered : int;
  mutable ordinal : int;
  mutable visits : int;
}

let mark () = { query = -1; buckets = []; keys = []; entered = max_int; ordinal = 0; visits = 0 }

let position m =
  let bucket = match m.buckets with (k, _) :: _ -> Some k | [] -> List.nth_opt m.keys 0 in
  (m.query, bucket, m.entered, m.ordinal)

let detach m =
  if m.buckets <> [] then m.keys <- List.map fst m.buckets;
  m.buckets <- []

let rec below bound = function
  | (p : posting) :: rest when p.generation > bound -> below bound rest
  | xs -> xs

(* As in Index.cursor, each posting and each position pair is resumable work.
   Snapshot bucket heads rather than collecting every partner before yielding.
   [mark], [from] and [upto] are as in Index.cursor. A bucket created after
   the original snapshot holds only newer postings, so continuing a query
   over the remaining keys of its mark misses nothing. *)
let cursor ?(since = 0) ?(upto = max_int) ?from ?mark ?(guard = fun () -> ()) ?eligible t ~variables
    clause =
  let start, entered, ordinal, remaining =
    match from with
    | Some m ->
        (m.query, m.entered, m.ordinal, if m.buckets <> [] then List.map fst m.buckets else m.keys)
    | None -> (-1, max_int, 0, [])
  in
  let bucket table k = (k, Option.value ~default:[] (Tbl.Head_opt.find_opt table k)) in
  let needles first outgoing table variables terms =
    List.mapi
      (fun i (term, positions) ->
        let query = first + i in
        let buckets =
          if query = start then List.map (bucket table) remaining
          else
            match key term with
            | None -> Tbl.Head_opt.to_seq table |> List.of_seq
            | Some _ as k -> bucket table k :: (if variables then [ bucket table None ] else [])
        in
        (query, outgoing, variables, term, positions, Index.Fingerprint.term term, buckets))
      terms
  in
  let targets = locations ?eligible ~sources:true ~variables:true clause in
  let queries =
    needles 0 true t.targets variables targets
    @ needles (List.length targets) false t.sources true
        (locations ?eligible ~sources:false ~variables clause)
    |> List.filter (fun (query, _, _, _, _, _, _) -> query >= start)
  in
  let rec scan outgoing variables term positions fingerprint previous count = function
    | [] -> Seq.empty
    | (p : posting) :: rest when p.generation > since ->
        fun () ->
          guard ();
          let count = if p.generation = previous then count + 1 else 1 in
          Option.iter
            (fun m ->
              m.entered <- p.generation;
              m.ordinal <- count;
              m.visits <- m.visits + 1)
            mark;
          t.postings <- t.postings + 1;
          let tail = scan outgoing variables term positions fingerprint p.generation count rest in
          let pairs =
            if (not (current t p)) || p.locations = [] || ((not variables) && key p.term = None)
            then Seq.empty
            else if t.fingerprint && not (Index.Fingerprint.compatible fingerprint p.fingerprint)
            then (
              t.fingerprint_rejected <- t.fingerprint_rejected + 1;
              Seq.empty)
            else if not (Index.compatible term p.term) then Seq.empty
            else
              List.to_seq positions
              |> Seq.flat_map (fun needle ->
                  List.to_seq p.locations
                  |> Seq.map (fun stored ->
                      guard ();
                      t.occurrences <- t.occurrences + 1;
                      let source, target =
                        if outgoing then (needle, stored) else (stored, needle)
                      in
                      if current t p then
                        Some
                          ( p.step,
                            outgoing,
                            (source.literal, source.reverse, target.literal, target.path) )
                      else None))
          in
          Seq.Cons (None, Seq.append pairs tail)
    | _ -> Seq.empty
  in
  let rec walk = function
    | [] -> Seq.empty
    | (query, outgoing, variables, term, positions, fp, buckets) :: later ->
        (* Only the first bucket of the resumed query continues inside. *)
        let rec visit resumed = function
          | [] -> walk later
          | (_, xs) :: rest as here ->
              fun () ->
                Option.iter
                  (fun m ->
                    m.query <- query;
                    m.buckets <- here;
                    m.entered <- max_int;
                    m.ordinal <- 0)
                  mark;
                let scanned =
                  if resumed && entered <= upto then
                    scan outgoing variables term positions fp entered (ordinal - 1)
                      (Index.resume_at
                         ~generation:(fun (p : posting) -> p.generation)
                         entered ordinal (below entered xs))
                  else scan outgoing variables term positions fp (-1) 0 (below upto xs)
                in
                Seq.append scanned (visit false rest) ()
        in
        visit (query = start) buckets
  in
  walk queries

(* Compatibility overapproximates one-way matching. Rewriting still proves each step. *)
let rewrite_targets ?guard t lhs =
  let found = Tbl.Int.create 16 in
  query ?guard t t.targets ~variables:false lhs (fun p -> Tbl.Int.replace found p.step.id p.step);
  Tbl.Int.to_seq_values found |> List.of_seq |> List.sort (fun (a : step) b -> compare a.id b.id)
