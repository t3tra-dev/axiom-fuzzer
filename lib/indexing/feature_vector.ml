open Wire
(** Feature-vector indexing for clause subsumption (E's FVI; S. Schulz, "Simple and Efficient Clause
    Subsumption with Feature Vector Indexing", 2013).

    A clause's vector counts, per polarity, its literals, its symbols (variables count 1, every
    function symbol 1) and the occurrences of each symbol slot (predicate, definition, equality and
    function symbols). If [c] subsumes [d] by multiset subsumption ([Subsumption.subsumes]: an
    injective literal map that keeps polarity and predicate, atoms matched one-way, equations in
    either orientation), every feature of [c] is at most the same feature of [d]: matching keeps
    every symbol occurrence of a pattern literal at the same position of its image and replaces a
    variable by a term of at least one symbol, and the map is injective. Saturating every count at
    [ceiling] and adding the counts of the symbols that share a slot keep that order. So the vector
    test only rejects clauses that cannot subsume (forward) or be subsumed (backward); it never
    rejects a subsumer.

    Symbols get slots in the order an index first sees them (a deterministic function of the
    search); slot [i mod slots] once more than [slots] symbols are known. Each index has its own
    table, used for its entries and its queries alike.

    Vectors are packed seven 8-bit lanes to an OCaml int with every lane's top bit clear, so a
    lane-wise [<=] over a word is one subtraction (SWAR): [((d lor high) - c) land high = high] iff
    every lane of [c] is at most the lane of [d] (no lane borrows, since a lane of [d lor high] is
    at least 128 and a lane of [c] at most 127).

    The index is a burst trie over the vectors: a leaf keeps its entries (newest first, dead ones
    until they outnumber the live ones) and, once it holds more than its limit, splits on the
    feature with the most distinct values among its live entries; an inner node routes an entry by
    that one feature. A query visits the children whose key is at most (forward) or at least
    (backward) the query's value of the node's feature and tests the whole vector at the leaves. *)

let lanes = 7
let words = 5
let length = lanes * words
let ceiling = 127
let high = 0x0080808080808080
let slots = (length - 4) / 2

(* Feature positions. *)
let positive_literals = 0
let negative_literals = 1
let positive_size = 2
let negative_size = 3
let[@inline] slot_feature slot positive = 4 + (2 * slot) + if positive then 0 else 1

module Symbols = Hashtbl.Make (struct
  type t = symbol

  let equal = Sym.equal
  let hash f = Tbl.Hash.finish (Tbl.Hash.symbol Tbl.Hash.seed f)
end)

module Names = Hashtbl.Make (struct
  type t = string

  let equal = String.equal
  let hash = Hashtbl.hash
end)

type table = {
  functions : int Symbols.t;
  predicates : int Names.t;
  definitions : int Tbl.Pair.t;
  mutable known : int;  (** symbols with a slot; slot 0 is equality *)
  counts : int array;  (** scratch of [vector] *)
}

let table () =
  {
    functions = Symbols.create 64;
    predicates = Names.create 32;
    definitions = Tbl.Pair.create 16;
    known = 1;
    counts = Array.make length 0;
  }

let fresh t =
  let i = t.known in
  t.known <- i + 1;
  i mod slots

let function_slot t f =
  match Symbols.find_opt t.functions f with
  | Some i -> i
  | None ->
      let i = fresh t in
      Symbols.add t.functions f i;
      i

let predicate_slot t p =
  match Names.find_opt t.predicates p with
  | Some i -> i
  | None ->
      let i = fresh t in
      Names.add t.predicates p i;
      i

let definition_slot t d =
  match Tbl.Pair.find_opt t.definitions d with
  | Some i -> i
  | None ->
      let i = fresh t in
      Tbl.Pair.add t.definitions d i;
      i

type vector = int array
(** [words] packed words *)

let[@inline] lane (v : vector) feature =
  (Array.unsafe_get v (feature / lanes) lsr (8 * (feature mod lanes))) land 0x7f

let pack counts =
  Array.init words (fun w ->
      let word = ref 0 in
      for j = lanes - 1 downto 0 do
        word := (!word lsl 8) lor min ceiling counts.((w * lanes) + j)
      done;
      !word)

(** The vector of [clause] under [t]'s slots (new symbols get slots). *)
let vector t (clause : clause) =
  let counts = t.counts in
  Array.fill counts 0 length 0;
  let bump feature = counts.(feature) <- counts.(feature) + 1 in
  List.iter
    (fun (l : literal) ->
      let positive = l.positive in
      let size = if positive then positive_size else negative_size in
      bump (if positive then positive_literals else negative_literals);
      let symbol slot =
        bump size;
        bump (slot_feature slot positive)
      in
      let rec term = function
        | V _ -> bump size
        | Fn (f, ts) ->
            symbol (function_slot t f);
            List.iter term ts
      in
      match l.atom with
      | P (p, ts) ->
          symbol (predicate_slot t p);
          List.iter term ts
      | D (d, ts) ->
          symbol (definition_slot t d);
          List.iter term ts
      | E (x, y) ->
          symbol 0;
          term x;
          term y)
    clause;
  pack counts

(* Every lane of word [i] of [a] at most the lane of [b]. *)
let[@inline] word_below (a : vector) (b : vector) i =
  ((Array.unsafe_get b i lor high) - Array.unsafe_get a i) land high = high

(* Every lane of [a] at most the lane of [b]: the [words] word tests, written out (no closure is
   allocated per test). *)
let () = assert (words = 5)

let[@inline] below (a : vector) (b : vector) =
  word_below a b 0 && word_below a b 1 && word_below a b 2 && word_below a b 3 && word_below a b 4

type 'a entry = { item : 'a; vector : vector; mutable dead : bool }

type 'a node = {
  mutable feature : int;  (** the split feature; [-1] for a leaf *)
  mutable keys : int array;  (** ascending *)
  mutable kids : 'a node array;
  mutable bucket : 'a entry list;  (** a leaf's entries, newest first, dead ones included *)
  mutable live : int;  (** live entries in the subtree *)
  mutable stale : int;  (** dead entries in [bucket] *)
  mutable limit : int;  (** a leaf splits once [bucket] is longer *)
  mutable uniform : vector option;
      (** a leaf whose live entries all have this vector (found when a split fails): a query tests
          it once for all of them *)
}

let initial_limit = 16

let leaf () =
  {
    feature = -1;
    keys = [||];
    kids = [||];
    bucket = [];
    live = 0;
    stale = 0;
    limit = initial_limit;
    uniform = None;
  }

let same (a : vector) (b : vector) =
  a == b
  || Int.equal (Array.unsafe_get a 0) (Array.unsafe_get b 0)
     && Int.equal (Array.unsafe_get a 1) (Array.unsafe_get b 1)
     && Int.equal (Array.unsafe_get a 2) (Array.unsafe_get b 2)
     && Int.equal (Array.unsafe_get a 3) (Array.unsafe_get b 3)
     && Int.equal (Array.unsafe_get a 4) (Array.unsafe_get b 4)

type 'a t = { root : 'a node; mutable nodes : int }

let create () = { root = leaf (); nodes = 1 }

(* The feature with the most distinct values among [entries]; [-1] when all vectors are equal. *)
let split_feature entries =
  let seen = Array.make (ceiling + 1) (-1) in
  let best = ref (-1) and best_count = ref 1 in
  for feature = 0 to length - 1 do
    let count = ref 0 in
    List.iter
      (fun e ->
        let x = lane e.vector feature in
        if seen.(x) <> feature then (
          seen.(x) <- feature;
          incr count))
      entries;
    if !count > !best_count then (
      best := feature;
      best_count := !count)
  done;
  !best

(* The position of [x] in [keys], or [-(insertion point) - 1]. *)
let search keys x =
  let rec go lo hi =
    if lo >= hi then -lo - 1
    else
      let mid = (lo + hi) / 2 in
      let k = Array.unsafe_get keys mid in
      if k = x then mid else if k < x then go (mid + 1) hi else go lo mid
  in
  go 0 (Array.length keys)

let child t n x =
  let i = search n.keys x in
  if i >= 0 then n.kids.(i)
  else
    let i = -i - 1 in
    let kid = leaf () in
    let size = Array.length n.keys in
    n.keys <-
      Array.init (size + 1) (fun j ->
          if j < i then n.keys.(j) else if j = i then x else n.keys.(j - 1));
    n.kids <-
      Array.init (size + 1) (fun j ->
          if j < i then n.kids.(j) else if j = i then kid else n.kids.(j - 1));
    t.nodes <- t.nodes + 1;
    kid

let rec insert t n e =
  n.live <- n.live + 1;
  if n.feature >= 0 then insert t (child t n (lane e.vector n.feature)) e
  else (
    n.bucket <- e :: n.bucket;
    (match n.uniform with Some v when not (same v e.vector) -> n.uniform <- None | _ -> ());
    if n.live + n.stale > n.limit then split t n)

and split t n =
  let live = List.filter (fun e -> not e.dead) n.bucket in
  n.bucket <- live;
  n.stale <- 0;
  match split_feature live with
  | -1 ->
      n.limit <- 2 * max n.limit n.live;
      n.uniform <- (match live with e :: _ -> Some e.vector | [] -> None)
  | feature ->
      n.feature <- feature;
      n.uniform <- None;
      n.bucket <- [];
      n.live <- 0;
      (* Oldest first, so that every child's bucket stays newest first. *)
      List.iter (fun e -> insert t n e) (List.rev live)

let add t item vector =
  let e = { item; vector; dead = false } in
  insert t t.root e;
  e

let rec erase t n e =
  n.live <- n.live - 1;
  if n.feature < 0 then
    if n.live = 0 then (
      n.bucket <- [];
      n.stale <- 0;
      n.uniform <- None)
    else (
      n.stale <- n.stale + 1;
      if n.stale > n.live then (
        n.bucket <- List.filter (fun e -> not e.dead) n.bucket;
        n.stale <- 0))
  else
    let i = search n.keys (lane e.vector n.feature) in
    let kid = n.kids.(i) in
    erase t kid e;
    if kid.live = 0 then (
      t.nodes <- t.nodes - 1;
      let size = Array.length n.keys in
      n.keys <- Array.init (size - 1) (fun j -> if j < i then n.keys.(j) else n.keys.(j + 1));
      n.kids <- Array.init (size - 1) (fun j -> if j < i then n.kids.(j) else n.kids.(j + 1));
      if size = 1 then (
        n.feature <- -1;
        n.limit <- initial_limit))

(** Marks [e] dead and takes it out of the counts; the entry must be live in [t]. *)
let remove t e =
  if not e.dead then (
    e.dead <- true;
    erase t t.root e)

(** [f] on every live entry whose vector is at most [v] (the possible subsumers of a clause with
    vector [v]), in the trie's order. *)
let forward t v f =
  let rec visit n =
    if n.live > 0 then
      if n.feature < 0 then
        match n.uniform with
        | Some u -> if below u v then List.iter (fun e -> if not e.dead then f e) n.bucket
        | None -> List.iter (fun e -> if (not e.dead) && below e.vector v then f e) n.bucket
      else
        let x = lane v n.feature and keys = n.keys and kids = n.kids in
        let size = Array.length keys in
        let rec loop i =
          if i < size && Array.unsafe_get keys i <= x then (
            visit (Array.unsafe_get kids i);
            loop (i + 1))
        in
        loop 0
  in
  visit t.root

(** [f] on every live entry whose vector is at least [v] (the clauses a clause with vector [v] may
    subsume), in the trie's order. *)
let backward t v f =
  let rec visit n =
    if n.live > 0 then
      if n.feature < 0 then
        match n.uniform with
        | Some u -> if below v u then List.iter (fun e -> if not e.dead then f e) n.bucket
        | None -> List.iter (fun e -> if (not e.dead) && below v e.vector then f e) n.bucket
      else
        let x = lane v n.feature and keys = n.keys and kids = n.kids in
        let size = Array.length keys in
        let start = search keys x in
        let rec loop i =
          if i < size then (
            visit (Array.unsafe_get kids i);
            loop (i + 1))
        in
        loop (if start >= 0 then start else -start - 1)
  in
  visit t.root

let size t = t.root.live

(** Empties [t]: the root becomes an empty leaf again and every entry is dropped (the release of an
    engine that ended, [Engine.release]). *)
let clear t =
  let r = t.root in
  r.feature <- -1;
  r.keys <- [||];
  r.kids <- [||];
  r.bucket <- [];
  r.live <- 0;
  r.stale <- 0;
  r.limit <- initial_limit;
  r.uniform <- None;
  t.nodes <- 1
