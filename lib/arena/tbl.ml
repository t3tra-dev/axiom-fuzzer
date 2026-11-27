(* Search-side hash tables: one [Hashtbl.Make] instance per key type.

   Stdlib's generic tables hash with [seeded_hash_param 10 100]: only the first
   10 meaningful words of a key (breadth first) contribute, so clause, literal
   and ground-term keys that share a prefix fall into one bucket and every
   lookup walks a long chain of polymorphic comparisons. These tables hash the
   whole key with explicit, monomorphic functions and compare keys with
   monomorphic structural equality, which agrees with [compare a b = 0] on all
   of these key types (no floats, functions or cycles). Lookups therefore have
   exactly the generic semantics; only bucket positions, and so the iteration
   order of [iter]/[fold], differ. Integer keys hash to themselves, so dense
   proof-node ids spread over consecutive buckets.

   The kernel and the verified elaborator keep their own Stdlib tables; nothing
   here is trusted. *)

open Wire

module Hash = struct
  (* FNV-style word mixing; [finish] folds high bits into the low bits that
     select a bucket. Both stay in OCaml ints and never allocate. *)
  let[@inline] mix h x = h lxor x * 0x100000001b3
  let seed = 0x2545f4914f6cdd1d

  let[@inline] finish h =
    let h = h lxor (h lsr 32) in
    let h = h * 0x3f51afd7ed558ccd in
    h lxor (h lsr 29) land max_int

  let[@inline] int x = x land max_int
  let[@inline] pair (a, b) = finish (mix (mix seed a) b)

  let ints xs =
    let rec go h = function [] -> h | x :: xs -> go (mix h x) xs in
    finish (go seed xs)

  (* [String.hash] of the symbol and predicate names, which every term, atom and clause hash
     mixes in, through a direct-mapped cache keyed by the physical string. Clausification shares
     one name string per name (Intern), so the few names of a search hit their entry, and a hit
     returns the value [String.hash] gave before: every table keeps its buckets and its iteration
     order. An entry is an immutable (string, hash) pair, replaced as a whole on a miss, so Domains
     that race on a slot can only see some complete pair; a pair is used only for the string it
     was computed from ([==]), whatever was stored before or after. The cache keeps at most
     [names] strings alive. *)
  let names = 8192
  let cache : (string * int) array = Array.make names ("", String.hash "")

  (* The slot: the length and three bytes of [s], mixed (no loop over the string). *)
  let[@inline] slot s =
    let n = String.length s in
    let h =
      if n = 0 then 0
      else
        ((((n * 31) + Char.code (String.unsafe_get s 0)) * 31)
        + Char.code (String.unsafe_get s (n - 1)))
        * 31
        + Char.code (String.unsafe_get s (n lsr 1))
    in
    ((h * 0x9e3779b97f4a7c1) lsr 50) land (names - 1)

  let[@inline] string_hash s =
    let i = slot s in
    let key, h = Array.unsafe_get cache i in
    if key == s then h
    else
      let h = String.hash s in
      Array.unsafe_set cache i (s, h);
      h

  let[@inline] string h s = mix h (string_hash s)

  let[@inline] symbol h = function
    | Original s -> string (mix h 1) s
    | Skolem (a, b) -> mix (mix (mix h 2) a) b

  (* Children are closed by an end marker, so [f(g(a),b)] and [f(g(a,b))]
     differ. The whole tree is visited, as by structural equality. *)
  let rec term_into h = function
    | V (a, b) -> mix (mix (mix h 3) a) b
    | Fn (f, ts) -> mix (terms_into (symbol h f) ts) 5

  and terms_into h = function [] -> h | t :: ts -> terms_into (term_into h t) ts

  let atom_into h = function
    | P (p, ts) -> mix (terms_into (string (mix h 7) p) ts) 5
    | E (s, t) -> term_into (term_into (mix h 11) s) t
    | D ((a, b), ts) -> mix (terms_into (mix (mix (mix h 13) a) b) ts) 5

  let[@inline] literal_into h (l : literal) =
    atom_into (mix h (if l.positive then 17 else 19)) l.atom

  let rec clause_into h = function [] -> mix h 23 | l :: ls -> clause_into (literal_into h l) ls
  let term t = finish (term_into seed t)
  let atom a = finish (atom_into seed a)
  let literal l = finish (literal_into seed l)
  let clause c = finish (clause_into seed c)

  let clause_ints (c, xs) =
    let rec go h = function [] -> h | x :: xs -> go (mix h x) xs in
    finish (go (clause_into seed c) xs)

  (* The hash of the string key the feature replaced (Intern.legacy_hash), so tables keyed by
     features keep their bucket positions and iteration order. *)
  let[@inline] feature (f : Intern.feature) = Intern.feature_hash f
  let[@inline] head ((f, n) : symbol * int) = finish (mix (symbol seed f) n)
  let head_opt = function None -> 0 | Some h -> head h
end

module Equal = struct
  let[@inline] pair ((a, b) : int * int) ((c, d) : int * int) = Int.equal a c && Int.equal b d

  let rec ints xs ys =
    xs == ys
    ||
    match (xs, ys) with
    | [], [] -> true
    | x :: xs, y :: ys -> Int.equal x y && ints xs ys
    | _ -> false

  let rec term s t =
    s == t
    ||
    match (s, t) with
    | V x, V y -> Sym.var x y
    | Fn (f, xs), Fn (g, ys) -> Sym.equal f g && terms xs ys
    | _ -> false

  and terms xs ys =
    xs == ys
    ||
    match (xs, ys) with
    | [], [] -> true
    | x :: xs, y :: ys -> term x y && terms xs ys
    | _ -> false

  let atom a b =
    a == b
    ||
    match (a, b) with
    | P (p, xs), P (q, ys) -> Sym.name p q && terms xs ys
    | E (s, t), E (u, v) -> term s u && term t v
    | D (d, xs), D (e, ys) -> Sym.def d e && terms xs ys
    | _ -> false

  let[@inline] literal (a : literal) (b : literal) =
    a == b || (Bool.equal a.positive b.positive && atom a.atom b.atom)

  let rec clause a b =
    a == b
    ||
    match (a, b) with
    | [], [] -> true
    | l :: ls, m :: ms -> literal l m && clause ls ms
    | _ -> false

  let clause_ints ((c, xs) : clause * int list) (d, ys) = ints xs ys && clause c d
  let[@inline] feature (f : Intern.feature) g = Intern.feature_equal f g
  let[@inline] head ((f, n) : symbol * int) (g, m) = Int.equal n m && Sym.equal f g

  let head_opt a b =
    match (a, b) with None, None -> true | Some a, Some b -> head a b | _ -> false
end

module Int = Hashtbl.Make (struct
  type t = int

  let equal = Stdlib.Int.equal
  let hash = Hash.int
end)

(* Variables, tickets and definition ids. *)
module Pair = Hashtbl.Make (struct
  type t = int * int

  let equal = Equal.pair
  let hash = Hash.pair
end)

module Ints = Hashtbl.Make (struct
  type t = int list

  let equal = Equal.ints
  let hash = Hash.ints
end)

module Term = Hashtbl.Make (struct
  type t = term

  let equal = Equal.term
  let hash = Hash.term
end)

module Atom = Hashtbl.Make (struct
  type t = atom

  let equal = Equal.atom
  let hash = Hash.atom
end)

module Literal = Hashtbl.Make (struct
  type t = literal

  let equal = Equal.literal
  let hash = Hash.literal
end)

module Clause = Hashtbl.Make (struct
  type t = clause

  let equal = Equal.clause
  let hash = Hash.clause
end)

(* Variant keys and (clause, AVATAR support) memo keys. *)
module Clause_ints = Hashtbl.Make (struct
  type t = clause * int list

  let equal = Equal.clause_ints
  let hash = Hash.clause_ints
end)

(* Signed predicate/arity features ([Clause.key]), interned as ints (Intern.feature). *)
module Feature = Hashtbl.Make (struct
  type t = Intern.feature

  let equal = Equal.feature
  let hash = Hash.feature
end)

(* Function symbol and arity. *)
module Head = Hashtbl.Make (struct
  type t = symbol * int

  let equal = Equal.head
  let hash = Hash.head
end)

module Head_opt = Hashtbl.Make (struct
  type t = (symbol * int) option

  let equal = Equal.head_opt
  let hash = Hash.head_opt
end)
