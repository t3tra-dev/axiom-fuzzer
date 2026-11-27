open Wire

(* Four prefix-closed samples; Below is distinct from an absent argument.
   Variables are never treated as fixed symbols. Full compatibility still follows.
   A sample is an int: [variable], [below], [absent], or the head's Intern.head_code (>= 0), which
   is equal for two heads exactly when their symbols and arities are, so a compatibility test
   compares ints only. *)
module Fingerprint = struct
  type t = int array

  let variable = -1
  let below = -2
  let absent = -3

  let rec at term = function
    | [] -> ( match term with V _ -> variable | Fn (s, ts) -> Intern.head_code s (List.length ts))
    | i :: path -> (
        match term with
        | V _ -> below
        | Fn (_, ts) -> ( match List.nth_opt ts i with None -> absent | Some t -> at t path))

  let term t = [| at t []; at t [ 0 ]; at t [ 1 ]; at t [ 0; 0 ] |]

  let atom a =
    let args = Clause.atom_terms a in
    let sample i path = match List.nth_opt args i with None -> absent | Some t -> at t path in
    [| sample 0 []; sample 1 []; sample 0 [ 0 ]; sample 1 [ 0 ] |]

  (* Below is compatible with everything, Absent only with Absent (and Below), Variable with
     everything but Absent, a head with an equal head or Variable. *)
  let[@inline] cell (x : int) (y : int) =
    x = y || x = below || y = below || (x = variable && y <> absent) || (y = variable && x <> absent)

  (* Both arguments are fingerprints of [term] or [atom] (four samples). *)
  let compatible ?(reverse = false) (a : t) (b : t) =
    if Array.length a <> 4 || Array.length b <> 4 then invalid_arg "Fingerprint.compatible";
    if reverse then
      cell (Array.unsafe_get a 0) (Array.unsafe_get b 1)
      && cell (Array.unsafe_get a 1) (Array.unsafe_get b 0)
      && cell (Array.unsafe_get a 2) (Array.unsafe_get b 3)
      && cell (Array.unsafe_get a 3) (Array.unsafe_get b 2)
    else
      cell (Array.unsafe_get a 0) (Array.unsafe_get b 0)
      && cell (Array.unsafe_get a 1) (Array.unsafe_get b 1)
      && cell (Array.unsafe_get a 2) (Array.unsafe_get b 2)
      && cell (Array.unsafe_get a 3) (Array.unsafe_get b 3)
end

(* The liveness of one [add]: shared by every posting (and the [all] entry) that add created,
   cleared when its step is removed or added again. [alive] is the same predicate as [current] on
   the posting's id and generation, read without hashing the id. The memory is one small block per
   add that is still live or still has postings in [buckets] (compaction drops the stale ones), so
   it is bounded by the indexed state, never by the largest proof id or the run length. It is not
   part of the deterministic footprint, which counts postings ([size]). *)
type cell = {
  mutable alive : bool;
  clause : clause;  (** the indexed clause, whose literal keys locate the add's buckets *)
  mutable postings : int;  (** the postings the add made (Index only) *)
}

type posting = {
  step : step;
  generation : int;
  literal : int;
  value : atom;
  fingerprint : Fingerprint.t;
  cell : cell;
}

type feature = Clause.feature

type t = {
  buckets : posting list Tbl.Feature.t;
  live : int Tbl.Int.t;
  cells : cell Tbl.Int.t;  (** the cell of each live id's current generation *)
  mutable dirty : feature list;
      (** buckets that may hold stale postings, since the last [compact] (repeats allowed) *)
  mutable stale : int;  (** adds removed or superseded since the last [compact] *)
  mutable stale_postings : int;  (** their postings, all still in [buckets] *)
  mutable removals : int;
      (** adds removed or superseded so far: while it is unchanged, every (id, generation) that was
          [current] still is (generations only grow), and every id that was [mem] still is *)
  mutable generation : int;
  mutable all : (step * cell) list;
  mutable cached : step list option;
  fingerprint : bool;
  mutable candidates : int;
  mutable scans : int;
  mutable postings : int;
  mutable fingerprint_rejected : int;
  mutable occurrences : int;
  mutable size : int;
      (** Postings held in [buckets], stale ones included until [compact]: a deterministic size for
          the memory budget's footprint (Engine.footprint). *)
}

let create ?(fingerprint = true) () =
  {
    buckets = Tbl.Feature.create 32;
    live = Tbl.Int.create 128;
    cells = Tbl.Int.create 128;
    dirty = [];
    stale = 0;
    stale_postings = 0;
    removals = 0;
    generation = 0;
    all = [];
    cached = None;
    fingerprint;
    candidates = 0;
    scans = 0;
    postings = 0;
    fingerprint_rejected = 0;
    occurrences = 0;
    size = 0;
  }

(* An add leaves the index (its id is removed or added again): its postings become stale. They are
   in the buckets of its clause's literal keys (every literal, a superset of the eligible ones:
   filtering a bucket without a stale posting changes nothing), recomputed here so that no key is
   kept per live posting. *)
let retire t (cell : cell) =
  cell.alive <- false;
  t.stale <- t.stale + 1;
  t.stale_postings <- t.stale_postings + cell.postings;
  t.removals <- t.removals + 1;
  t.dirty <- List.fold_left (fun dirty l -> Clause.key l :: dirty) t.dirty cell.clause

let add ?(eligible = fun _ -> true) t (s : step) =
  if t.generation = max_int then invalid_arg "Index: generation overflow";
  t.generation <- t.generation + 1;
  let generation = t.generation in
  Tbl.Int.replace t.live s.id generation;
  (* Adding a live id again retires its earlier postings, as [current] does. *)
  Option.iter (retire t) (Tbl.Int.find_opt t.cells s.id);
  let cell = { alive = true; clause = s.clause; postings = 0 } in
  t.cached <- None;
  t.all <- (s, cell) :: t.all;
  List.iteri
    (fun literal l ->
      if eligible literal then (
        let key = Clause.key l in
        let old = Option.value ~default:[] (Tbl.Feature.find_opt t.buckets key) in
        let fingerprint = if t.fingerprint then Fingerprint.atom l.atom else [||] in
        t.size <- t.size + 1;
        cell.postings <- cell.postings + 1;
        Tbl.Feature.replace t.buckets key
          ({ step = s; generation; literal; value = l.atom; fingerprint; cell } :: old)))
    s.clause;
  Tbl.Int.replace t.cells s.id cell

let mem t id = Tbl.Int.mem t.live id

(* Without the option [find_opt] allocates for every hit: tickets are checked very often. *)
let current t id generation =
  match Tbl.Int.find t.live id with g -> Int.equal g generation | exception Not_found -> false

(* [current] on a posting of [t]'s own id and generation. *)
let[@inline] live (p : posting) = p.cell.alive

let remove t id =
  if mem t id then (
    Tbl.Int.remove t.live id;
    Option.iter (retire t) (Tbl.Int.find_opt t.cells id);
    Tbl.Int.remove t.cells id;
    t.cached <- None)

(* Every bucket filtered, as compaction did before it tracked [dirty]: [compact] gives the same
   tables, lists (physically, through Shared.filter), [all] and [size]. The reference of the unit
   tests. *)
let compact_all t =
  t.all <- Shared.filter (fun (_, c) -> c.alive) t.all;
  t.cached <- None;
  t.size <- 0;
  t.dirty <- [];
  t.stale <- 0;
  t.stale_postings <- 0;
  Tbl.Feature.filter_map_inplace
    (fun _ xs ->
      match Shared.filter live xs with
      | [] -> None
      | xs ->
          t.size <- t.size + List.length xs;
          Some xs)
    t.buckets

(* Drops the postings of removed or superseded adds. Only the buckets those adds posted to can
   hold a stale posting; every other bucket would be kept as it is (physically), so only the
   [dirty] ones are filtered. Replacing or removing a key in place leaves the order of the other
   keys as filtering the whole table does. Exactly the stale postings go, so [size] drops by their
   count. *)
let compact t =
  if t.stale > 0 then
    (* With at least as many dirty marks as buckets, the full sweep costs no more. *)
    if List.compare_length_with t.dirty (Tbl.Feature.length t.buckets) >= 0 then compact_all t
    else (
      t.all <- Shared.filter (fun (_, c) -> c.alive) t.all;
      t.cached <- None;
      let dirty = t.dirty and seen = Tbl.Feature.create 16 in
      t.dirty <- [];
      t.size <- t.size - t.stale_postings;
      t.stale <- 0;
      t.stale_postings <- 0;
      List.iter
        (fun key ->
          if not (Tbl.Feature.mem seen key) then (
            Tbl.Feature.add seen key ();
            match Tbl.Feature.find_opt t.buckets key with
            | None -> ()
            | Some xs -> (
                match Shared.filter live xs with
                | [] -> Tbl.Feature.remove t.buckets key
                | ys -> if ys != xs then Tbl.Feature.replace t.buckets key ys)))
        dirty)

let compatible = Unify.compatible

let atoms a b =
  match (a, b) with
  | P (p, xs), P (q, ys) ->
      Sym.name p q && List.compare_lengths xs ys = 0 && List.for_all2 compatible xs ys
  | D (p, xs), D (q, ys) ->
      Sym.def p q && List.compare_lengths xs ys = 0 && List.for_all2 compatible xs ys
  | E (x, y), E (u, v) -> (compatible x u && compatible y v) || (compatible x v && compatible y u)
  | _ -> false

let fingerprint_matches t atom fingerprint (p : posting) =
  (not t.fingerprint)
  || Fingerprint.compatible fingerprint p.fingerprint
  ||
  match atom with
  | E _ -> Fingerprint.compatible ~reverse:true fingerprint p.fingerprint
  | _ -> false

let bucket t l =
  Option.value ~default:[]
    (Tbl.Feature.find_opt t.buckets (Clause.key { l with positive = not l.positive }))

let matches ?(guard = fun () -> ()) ?(eligible = fun _ -> true) t clause =
  t.scans <- t.scans + Tbl.Int.length t.live;
  let found = Tbl.Int.create 16 in
  List.iteri
    (fun i l ->
      if eligible i then
        let fingerprint = if t.fingerprint then Fingerprint.atom l.atom else [||] in
        List.iter
          (fun p ->
            guard ();
            t.postings <- t.postings + 1;
            if live p then
              if not (fingerprint_matches t l.atom fingerprint p) then
                t.fingerprint_rejected <- t.fingerprint_rejected + 1
              else if atoms l.atom p.value then
                let pairs =
                  match Tbl.Int.find_opt found p.step.id with
                  | Some (_, pairs) -> pairs
                  | None ->
                      let pairs = ref [] in
                      Tbl.Int.add found p.step.id (p.step, pairs);
                      pairs
                in
                pairs := (i, p.literal) :: !pairs)
          (bucket t l))
    clause;
  let result =
    Tbl.Int.fold
      (fun _ (s, pairs) xs ->
        let pairs = List.sort_uniq compare !pairs in
        t.occurrences <- t.occurrences + List.length pairs;
        (s, pairs) :: xs)
      found []
    |> List.sort (fun ((a : step), _) (b, _) -> compare a.id b.id)
  in
  t.candidates <- t.candidates + List.length result;
  result

let partners t clause = List.map fst (matches t clause)

(* Where a cursor stands, without holding any posting list: the needle (clause
   literal) being scanned, the generation of the posting entered last there
   and its ordinal among the adjacent postings of that generation (one clause
   can post several literals to a bucket). Posting lists are newest first and
   compaction removes a clause's postings together, so the rest of that needle
   starts at that posting. [visits] counts posting entries. *)
type mark = {
  mutable needle : int;
  mutable entered : int;
  mutable ordinal : int;
  mutable visits : int;
}

let mark () = { needle = -1; entered = max_int; ordinal = 0; visits = 0 }
let position m = (m.needle, m.entered, m.ordinal)

(* The postings from the [ordinal]-th one of generation [entered] on, if it is
   still listed, and otherwise from the first older one. *)
let resume_at ~generation entered ordinal xs =
  let rec skip n xs =
    match xs with p :: rest when n > 0 && generation p = entered -> skip (n - 1) rest | _ -> xs
  in
  skip (ordinal - 1) xs

(* Count the elements a consumer takes from a stream derived from a marked
   cursor, per posting entered ([taken] restarts at each entry). A stream
   rebuilt from the mark re-enters that posting first; with [resumes] it skips
   the [taken] elements consumed there before, so the rebuilt stream continues
   exactly where the dropped one stopped. A posting that has meanwhile left
   the index is not re-entered, and then nothing is skipped. *)
let follow ~resumes ~visits ~position ~(taken : int ref) stream =
  let saved = position () and skip = ref (if resumes then !taken else 0) in
  let last = ref (visits ()) and first = ref true in
  Seq.filter_map
    (fun x ->
      let v = visits () in
      if v <> !last then (
        if not (!first && position () = saved) then skip := 0;
        last := v;
        taken := 0)
      else if !first then skip := 0;
      first := false;
      incr taken;
      if !skip > 0 then (
        decr skip;
        None)
      else Some x)
    stream

let rec below bound = function
  | (p : posting) :: rest when p.generation > bound -> below bound rest
  | xs -> xs

(* A snapshot of posting lists, advanced one posting at a time. None is a unit
   of scanning work, not exhaustion. New generations are handled by a later
   delta query; retirement is checked when a suspended query resumes.
   [mark] follows the scan. [from] continues the scan a mark describes over
   the current lists from its last posting; [upto] is the generation the
   original snapshot ended at. Postings retired meanwhile are not visited, so
   the continuation yields the original cursor's remaining hits; [follow]
   skips the elements of the re-entered posting that were already taken. *)
let cursor ?(since = 0) ?(upto = max_int) ?from ?mark ?(guard = fun () -> ())
    ?(eligible = fun _ -> true) t clause =
  let start, entered, ordinal =
    match from with Some (m : mark) -> (m.needle, m.entered, m.ordinal) | None -> (-1, max_int, 0)
  in
  let needles =
    List.mapi (fun i l -> (i, l)) clause
    |> List.filter (fun (i, _) -> eligible i && i >= start)
    |> List.map (fun (i, l) -> (i, l.atom, Fingerprint.atom l.atom, bucket t l))
  in
  let rec scan i atom fp previous count = function
    | [] -> Seq.empty
    | (p : posting) :: rest when p.generation > since ->
        fun () ->
          guard ();
          let count = if p.generation = previous then count + 1 else 1 in
          Option.iter
            (fun (m : mark) ->
              m.needle <- i;
              m.entered <- p.generation;
              m.ordinal <- count;
              m.visits <- m.visits + 1)
            mark;
          t.postings <- t.postings + 1;
          let hit =
            if not (live p) then None
            else if not (fingerprint_matches t atom fp p) then (
              t.fingerprint_rejected <- t.fingerprint_rejected + 1;
              None)
            else if atoms atom p.value then (
              t.occurrences <- t.occurrences + 1;
              Some (p.step, (i, p.literal)))
            else None
          in
          Seq.Cons (hit, scan i atom fp p.generation count rest)
    | _ -> Seq.empty
  in
  List.to_seq needles
  |> Seq.flat_map (fun (i, atom, fp, xs) ->
      if i = start && entered <= upto then
        let xs = below entered xs in
        scan i atom fp entered (ordinal - 1)
          (resume_at ~generation:(fun (p : posting) -> p.generation) entered ordinal xs)
      else scan i atom fp (-1) 0 (below (if i = start then min upto entered else upto) xs))

(* Bounded hint query, separate from the exhaustive inference index query. *)
let sample ?(budget = 128) ?(limit = 16) ~guard t literal =
  let fp = Fingerprint.atom literal.atom and seen = Tbl.Int.create limit in
  let rec visit left remaining found = function
    | [] -> List.rev found
    | _ when left = 0 || remaining = 0 -> List.rev found
    | p :: rest ->
        guard ();
        if
          live p
          && (not (Tbl.Int.mem seen p.step.id))
          && fingerprint_matches t literal.atom fp p
          && atoms literal.atom p.value
        then (
          Tbl.Int.add seen p.step.id ();
          visit (left - 1) (remaining - 1) (p.step :: found) rest)
        else visit (left - 1) remaining found rest
  in
  visit budget limit [] (bucket t literal)

(* Compare a bounded set of negative selections with the admissible direction
   having a unique maximal positive literal. Keep the negative direction when
   adding that positive pivot; post-substitution maximality still governs the
   positive inference. None means unrestricted maximal-literal inference.
   Exhausted estimates are unknown, never artificial zeros. [default] is the
   strategy's selection before the lookahead (production: the first negative
   literal); [order] is the worker's KBO instance. *)
let lookahead ?(guard = fun () -> ()) ?(order = Ordering.standard) ?default t ~budget clause =
  let default =
    match default with Some selection -> selection | None -> Ordering.first_negative clause
  in
  let rec negatives i left acc = function
    | [] -> List.rev acc
    | _ when left = 0 -> List.rev acc
    | l :: rest ->
        if l.positive then negatives (i + 1) left acc rest
        else negatives (i + 1) (left - 1) ((Some i, l) :: acc) rest
  in
  let choices = negatives 0 (min 7 budget) [] clause in
  let maximum =
    if budget > List.length choices then Ordering.positive_maximum ~order clause else None
  in
  let choices =
    if budget > List.length choices then
      match maximum with Some (_, l) -> (None, l) :: choices | None -> choices
    else choices
  in
  match choices with
  | [] -> (Option.map (fun i -> [ i ]) default, 0, 0)
  | [ (choice, _) ] -> (Option.map (fun i -> [ i ]) choice, 0, 0)
  | _ ->
      let limit = budget / List.length choices in
      let work = ref 0 and exhausted = ref 0 in
      let negative = ref None and positive = ref None in
      let negative_open = ref false in
      List.iter
        (fun (i, l) ->
          let fp = if t.fingerprint then Fingerprint.atom l.atom else [||] in
          let rec count left n = function
            | [] -> (true, n)
            | p :: rest when not (live p) ->
                guard ();
                count left n rest
            | _ when left = 0 ->
                incr exhausted;
                (false, n)
            | p :: rest ->
                guard ();
                incr work;
                let yes = fingerprint_matches t l.atom fp p && atoms l.atom p.value in
                count (left - 1) (if yes then n + 1 else n) rest
          in
          let exact, n = count limit 0 (bucket t l) in
          match i with
          | None -> positive := Some (exact, n)
          | Some i -> (
              if (not exact) || n > 0 then negative_open := true;
              if exact then
                match !negative with
                | None -> negative := Some (n, i)
                | Some (old, _) when n < old -> negative := Some (n, i)
                | _ -> ()))
        choices;
      let selected = match !negative with None -> default | Some (_, i) -> Some i in
      let baseline = Option.map (fun i -> [ i ]) selected in
      let selected =
        match (!positive, maximum, selected) with
        (* Preserve negative selection when no positive connection was observed.
           Among negative choices keep the existing fanout minimization; a new
           direction must offer productive work, not just an empty bucket. *)
        | Some (_, n), Some (p, _), Some negative_index when n > 0 && not !negative_open ->
            Some [ negative_index; p ]
        | _ -> baseline
      in
      (selected, !work, !exhausted)

let all t =
  match t.cached with
  | Some xs -> xs
  | None ->
      let xs =
        List.fold_left (fun acc ((s : step), c) -> if c.alive then s :: acc else acc) [] t.all
      in
      t.cached <- Some xs;
      xs

let brute_partners t =
  let count = Tbl.Int.length t.live in
  t.scans <- t.scans + count;
  t.candidates <- t.candidates + count;
  all t
