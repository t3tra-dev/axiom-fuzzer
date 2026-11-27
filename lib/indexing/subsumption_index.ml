open Wire
(** Subsumption candidates of a clause set.

    Forward and backward queries go through a feature-vector index (Feature_vector, E's FVI): its
    vector test only drops clauses that cannot subsume (forward) or be subsumed by (backward) the
    query under multiset subsumption ([Subsumption.subsumes]), and the survivors still pass the
    literal prefilter [possible]. The answers are the possible candidates of the earlier feature-set
    trie (which [possible] alone decides) minus clauses whose subsumption test fails, in the same
    order (ascending ids), so the first subsumer, every subsumed clause and every search decision
    stay the same; only the failing tests are no longer run.

    The budgeted subsumption-resolution query ([resolution]) still walks a trie over distinct signed
    predicate/arity features, whose visiting order decides what its budget reaches; an index created
    with [~resolution:false] does not keep that trie.

    Trie removal costs the length of the removed clause's feature path, amortized: [remove] marks
    the entry dead, updates the live count of its node and prunes emptied nodes on that path at once
    (exactly when an eager removal would), and leaves the dead entry in its node's list until dead
    entries outnumber the live ones there. Every query skips dead entries before it tests, counts or
    charges them, so it sees the live entries in insertion order, as with eager removal. All clauses
    with one feature set share a node, so an eager list filter per removal made a mass removal (the
    memory budget's trimming) quadratic. *)

type key = Clause.feature

type item = { step : step; prints : int array; mask : int }
(** An indexed clause with its literal prints ([prints]) and its head mask ([mask]), the
    feature-vector index's item. *)

type entry = { step : step; mutable dead : bool; vector : item Feature_vector.entry }

type node = {
  children : node Tbl.Feature.t;
  mutable terminal : entry list;  (** newest first; may hold dead entries *)
  mutable size : int;  (** live entries in [terminal] *)
  mutable stale : int;  (** dead entries in [terminal] *)
}

type t = {
  root : node;  (** the feature-set trie of [resolution]; empty without it *)
  trie : bool;
  vectors : item Feature_vector.t;
  symbols : Feature_vector.table;
  live : entry Tbl.Int.t;
  mutable baseline : int;
  mutable candidates : int;
}

let node () = { children = Tbl.Feature.create 4; terminal = []; size = 0; stale = 0 }

let create ?(resolution = true) () =
  {
    root = node ();
    trie = resolution;
    vectors = Feature_vector.create ();
    symbols = Feature_vector.table ();
    live = Tbl.Int.create 128;
    baseline = 0;
    candidates = 0;
  }

(* Stdlib.compare on the string keys the features replaced (Clause.key_view). *)
let compare_feature = Clause.compare_feature
let features c = List.map Clause.key c |> List.sort_uniq compare_feature

(* {2 Literal prints}

   [possible c d] holds iff every literal [p] of [c] has a literal [t] of [d] with the same sign
   and [atom_pure p.atom t.atom]. Each literal gets a print of [print_size] ints: its signed
   feature ([Clause.key]), then four samples of its atom's arguments (the first two arguments'
   heads and their first arguments' heads, as Index.Fingerprint samples an atom), each
   [Index.Fingerprint.variable], [below], [absent] or an Intern.head_code. [atom_pure p t] needs
   equal features, and at every sample where [p] has a head, the same head in [t] (in one of the
   two orientations of an equation): one-way matching keeps the pattern's symbols in place. So
   [possible_prints] skips the [atom_pure] calls that must fail and answers as [possible]. *)
let print_size = 5

let prints (c : clause) =
  let a = Array.make (print_size * List.length c) 0 in
  List.iteri
    (fun i (l : literal) ->
      let f = Index.Fingerprint.atom l.atom in
      a.(print_size * i) <- Clause.key l;
      for k = 0 to 3 do
        a.((print_size * i) + 1 + k) <- f.(k)
      done)
    c;
  a

(* {2 Head masks}

   A necessary condition of [possible c d] in one word per clause. [mask c (prints c)] has a bit
   for the signed feature of every literal of [c], and one for every head sample of a literal (a
   sample of its print that is an Intern.head_code), made of the literal's feature, the sample's
   place and the head, where the places of an equation's two sides are taken together (its two
   top samples share a place, and so do its two samples below them). If [possible c d], every
   literal [p] of [c] has a literal [t] of [d] with its feature such that [atom_pure p.atom t.atom]
   (in one of the two orientations of an equation), and one-way matching keeps every head of [p] in
   place, so [t] has the same head at the same place: every bit of [mask c] is a bit of [mask d]
   ([masked]). A bit may stand for several of these (63 bits); the test only gets weaker. So a
   query skips the print test of the entries whose mask is not [masked], whose answer must be
   false, and answers as [possible_prints]. *)
let mask (c : clause) (prints : int array) =
  let bit f place h =
    1
    lsl (Tbl.Hash.finish (Tbl.Hash.mix (Tbl.Hash.mix (Tbl.Hash.mix Tbl.Hash.seed f) place) h) mod 63)
  in
  let m = ref 0 in
  List.iteri
    (fun i (l : literal) ->
      let at = print_size * i in
      let feature = Array.unsafe_get prints at in
      let equation = match l.atom with E _ -> true | P _ | D _ -> false in
      m := !m lor bit feature 6 (-1);
      for k = 0 to 3 do
        let head = Array.unsafe_get prints (at + 1 + k) in
        if head >= 0 then m := !m lor bit feature (if equation then k / 2 else 2 + k) head
      done)
    c;
  !m

let[@inline] masked pattern instance = pattern land lnot instance = 0

let add t (s : step) =
  if Tbl.Int.mem t.live s.id then invalid_arg "duplicate subsumption index id";
  let vector =
    let prints = prints s.clause in
    Feature_vector.add t.vectors
      { step = s; prints; mask = mask s.clause prints }
      (Feature_vector.vector t.symbols s.clause)
  in
  let e = { step = s; dead = false; vector } in
  Tbl.Int.add t.live s.id e;
  let rec insert n = function
    | [] ->
        n.terminal <- e :: n.terminal;
        n.size <- n.size + 1
    | key :: rest ->
        let child =
          match Tbl.Feature.find_opt n.children key with
          | Some x -> x
          | None ->
              let x = node () in
              Tbl.Feature.add n.children key x;
              x
        in
        insert child rest
  in
  if t.trie then insert t.root (features s.clause)

let remove t id =
  match Tbl.Int.find_opt t.live id with
  | None -> ()
  | Some e ->
      Tbl.Int.remove t.live id;
      e.dead <- true;
      Feature_vector.remove t.vectors e.vector;
      let rec erase n = function
        | [] ->
            n.size <- n.size - 1;
            if n.size = 0 then (
              n.terminal <- [];
              n.stale <- 0)
            else (
              n.stale <- n.stale + 1;
              if n.stale > n.size then (
                n.terminal <- List.filter (fun e -> not e.dead) n.terminal;
                n.stale <- 0))
        | key :: rest ->
            let child = Tbl.Feature.find n.children key in
            erase child rest;
            if child.size = 0 && Tbl.Feature.length child.children = 0 then
              Tbl.Feature.remove n.children key
      in
      if t.trie then erase t.root (features e.step.clause)

let rec matches ?(guard = fun () -> ()) p t =
  guard ();
  match (p, t) with
  | V _, _ -> true
  | Fn (f, ps), Fn (g, ts) ->
      Sym.equal f g && List.compare_lengths ps ts = 0 && List.for_all2 (matches ~guard) ps ts
  | _ -> false

let atom ?(guard = fun () -> ()) p t =
  match (p, t) with
  | P (p, ps), P (q, ts) ->
      Sym.name p q && List.compare_lengths ps ts = 0 && List.for_all2 matches ps ts
  | D (p, ps), D (q, ts) ->
      Sym.def p q && List.compare_lengths ps ts = 0 && List.for_all2 (matches ~guard) ps ts
  | E (s, t), E (u, v) ->
      (matches ~guard s u && matches ~guard t v) || (matches ~guard s v && matches ~guard t u)
  | _ -> false

(* [matches] and [atom] without a guard are pure, so walking the argument lists pairwise and
   failing on a length mismatch gives the same answer as comparing the lengths first. *)
let rec matches_pure p t =
  match (p, t) with
  | V _, _ -> true
  | Fn (f, ps), Fn (g, ts) -> Sym.equal f g && matches_list ps ts
  | _ -> false

and matches_list ps ts =
  match (ps, ts) with
  | [], [] -> true
  | p :: ps, t :: ts -> matches_pure p t && matches_list ps ts
  | _ -> false

let atom_pure p t =
  match (p, t) with
  | P (p, ps), P (q, ts) -> Sym.name p q && matches_list ps ts
  | D (p, ps), D (q, ts) -> Sym.def p q && matches_list ps ts
  | E (s, t), E (u, v) ->
      (matches_pure s u && matches_pure t v) || (matches_pure s v && matches_pure t u)
  | _ -> false

(* [atom] with its default (no-op) guard, as before. *)
let possible c d =
  let rec exists (p : literal) = function
    | [] -> false
    | (t : literal) :: ts ->
        (Bool.equal p.positive t.positive && atom_pure p.atom t.atom) || exists p ts
  in
  List.for_all (fun p -> exists p d) c

(* Pattern sample [x] against instance sample [y]. *)
let[@inline] sample (x : int) (y : int) = x < 0 || x = y

let[@inline] compatible (pp : int array) i (tp : int array) j equation =
  let p = print_size * i and t = print_size * j in
  Int.equal (Array.unsafe_get pp p) (Array.unsafe_get tp t)
  && (sample (Array.unsafe_get pp (p + 1)) (Array.unsafe_get tp (t + 1))
      && sample (Array.unsafe_get pp (p + 2)) (Array.unsafe_get tp (t + 2))
      && sample (Array.unsafe_get pp (p + 3)) (Array.unsafe_get tp (t + 3))
      && sample (Array.unsafe_get pp (p + 4)) (Array.unsafe_get tp (t + 4))
     || equation
        && sample (Array.unsafe_get pp (p + 1)) (Array.unsafe_get tp (t + 2))
        && sample (Array.unsafe_get pp (p + 2)) (Array.unsafe_get tp (t + 1))
        && sample (Array.unsafe_get pp (p + 3)) (Array.unsafe_get tp (t + 4))
        && sample (Array.unsafe_get pp (p + 4)) (Array.unsafe_get tp (t + 3)))

(* [possible c d] with [cp = prints c] and [dp = prints d] (top-level loops: no closure per
   call). *)
let rec print_exists cp i (p : literal) equation dp j = function
  | [] -> false
  | (t : literal) :: ts ->
      (compatible cp i dp j equation && atom_pure p.atom t.atom)
      || print_exists cp i p equation dp (j + 1) ts

let rec print_all cp i dp d = function
  | [] -> true
  | (p : literal) :: ps ->
      let equation = match p.atom with E _ -> true | P _ | D _ -> false in
      print_exists cp i p equation dp 0 d && print_all cp (i + 1) dp d ps

let possible_prints cp c dp d = print_all cp 0 dp d c
let by_id (a : step) (b : step) = compare a.id b.id

(* The live clauses that may subsume [clause] (vector at most its vector and [possible]), by
   ascending id. *)
let forward t clause =
  t.baseline <- t.baseline + Tbl.Int.length t.live;
  let output = ref [] in
  let qp = prints clause in
  let qm = mask clause qp in
  Feature_vector.forward t.vectors (Feature_vector.vector t.symbols clause) (fun e ->
      let it = e.item in
      if masked it.mask qm && possible_prints it.prints it.step.clause qp clause then
        output := it.step :: !output);
  let result = List.sort by_id !output in
  t.candidates <- t.candidates + List.length result;
  result

(* Existence-only forward query: stops at the first candidate of [forward] (in the index's own
   order) that satisfies [accept], without building and sorting the whole candidate list. Its
   answer is [List.exists accept (forward t clause)]. *)
let exists_forward t clause accept =
  let exception Found in
  t.baseline <- t.baseline + Tbl.Int.length t.live;
  try
    let qp = prints clause in
    let qm = mask clause qp in
    Feature_vector.forward t.vectors (Feature_vector.vector t.symbols clause) (fun e ->
        let it = e.item in
        if masked it.mask qm && possible_prints it.prints it.step.clause qp clause then (
          t.candidates <- t.candidates + 1;
          if accept it.step then raise Found));
    false
  with Found -> true

(* Allow one opposite signed feature in the side premise. The exact matcher
   checks the shared substitution and which literal is removed. This bounded
   query is a simplification heuristic; exhaustion only leaves a clause intact. *)
let resolution ?(budget = 256) ?(guard = fun () -> ()) t clause =
  if not t.trie then invalid_arg "Subsumption_index.resolution: index without its trie";
  let exception Exhausted in
  let left = ref budget and found = Tbl.Int.create 16 in
  let tick () =
    guard ();
    decr left;
    if !left < 0 then raise Exhausted
  in
  let keys = features clause in
  let rec mem k = function [] -> false | x :: xs -> Int.equal x k || mem k xs in
  let feasible side =
    List.exists
      (fun p -> List.exists (fun t -> p.positive <> t.positive && atom ~guard p.atom t.atom) clause)
      side
    && List.for_all (fun p -> List.exists (fun t -> atom ~guard p.atom t.atom) clause) side
  in
  let rec visit n flipped pivot =
    if pivot then
      List.iter
        (fun e ->
          if not e.dead then (
            tick ();
            let s = e.step in
            if feasible s.clause then Tbl.Int.replace found s.id s))
        n.terminal;
    Tbl.Feature.iter
      (fun key child ->
        tick ();
        let opposite = mem (Clause.flip_feature key) keys in
        if mem key keys then visit child flipped (pivot || opposite)
        else if (not flipped) && opposite then visit child true true)
      n.children
  in
  (try visit t.root false false with Exhausted -> ());
  Tbl.Int.fold (fun _ s xs -> s :: xs) found [] |> List.sort (fun (a : step) b -> compare a.id b.id)

(* The live clauses whose vector is at least [clause]'s, by ascending id, without the literal
   prefilter: the clauses a positive unit equation may subsume by E's equational unit subsumption
   (the unit's sides matched below the top of a literal, where the literal prints do not apply;
   the vector test still does, since every symbol occurrence of the unit keeps its polarity in the
   subsumed literal). *)
let backward_vector t clause =
  t.baseline <- t.baseline + Tbl.Int.length t.live;
  let output = ref [] in
  Feature_vector.backward t.vectors (Feature_vector.vector t.symbols clause) (fun e ->
      output := e.item.step :: !output);
  let result = List.sort by_id !output in
  t.candidates <- t.candidates + List.length result;
  result

(* The live clauses [clause] may subsume (vector at least its vector and [possible]), by
   ascending id. *)
let backward t clause =
  t.baseline <- t.baseline + Tbl.Int.length t.live;
  let output = ref [] in
  let qp = prints clause in
  let qm = mask clause qp in
  Feature_vector.backward t.vectors (Feature_vector.vector t.symbols clause) (fun e ->
      let it = e.item in
      if masked qm it.mask && possible_prints qp clause it.prints it.step.clause then
        output := it.step :: !output);
  let result = List.sort by_id !output in
  t.candidates <- t.candidates + List.length result;
  result
