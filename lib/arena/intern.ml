(* Search-side interning of symbols and literal features, per OCaml Domain.

   Wire terms name symbols by strings ([Original of string]) and predicates by strings, so every
   symbol comparison was a C string comparison, and [Clause.key] built a string per literal. This
   module keeps, for the Domain that runs a search:

   - canonical symbols: one [Original name] block and one name string per distinct name, which
     clausification uses, so equal symbols of the search are physically equal and [Sym.equal]
     answers through its [==] fast path (only physical sharing changes: no comparison, hash or
     search decision can observe it);
   - interned literal features: [Clause.key]'s signed predicate/arity key as an immediate int
     ([feature]), with the hash and the order of the string keys it replaces kept per feature.
     Definition atoms ([D]) are not interned: their feature encodes (axiom id, index, arity)
     directly, and their name and hash are recomputed or read from a small fixed cache, because
     every clausified schema instance can bring new definitions.

   Nothing here is trusted or certified, and nothing leaves the Domain: a [feature] is meaningful
   only in the Domain that made it (an engine and its indexes live in one Domain), and canonical
   symbols are an optimization only (symbols from elsewhere still compare and hash correctly). The
   tables grow with the distinct names and predicate/arity pairs of the inputs, never with the
   search or the number of instances. *)

(* FNV-style word mixing: the same definitions as Tbl.Hash's (legacy_hash must equal the hash
   Tbl.Hash gave the string keys). *)
let[@inline] mix h x = h lxor x * 0x100000001b3
let seed = 0x2545f4914f6cdd1d

let[@inline] finish h =
  let h = h lxor (h lsr 32) in
  let h = h * 0x3f51afd7ed558ccd in
  h lxor (h lsr 29) land max_int

module Names = Hashtbl.Make (struct
  type t = string

  let equal = String.equal
  let hash = String.hash
end)

(* (definition id, definition index, arity) *)
module Defs = Hashtbl.Make (struct
  type t = int * int * int

  let equal ((a, b, c) : t) (x, y, z) = Int.equal a x && Int.equal b y && Int.equal c z
  let hash (a, b, c) = finish (mix (mix (mix seed a) b) c)
end)

(* (legacy feature name, arity) *)
module Keys = Hashtbl.Make (struct
  type t = string * int

  let equal ((a, n) : t) (b, m) = Int.equal n m && String.equal a b
  let hash (a, n) = finish (mix (mix seed (String.hash a)) n)
end)

let predicate_slots = 1024
let definition_slots = 1024
let head_slots = 1024

type state = {
  names : string Names.t;  (** canonical name strings *)
  originals : Wire.symbol Names.t;  (** canonical [Original] blocks, by name *)
  predicate_keys : string array;  (** predicate feature cache, direct-mapped by [slot] *)
  predicate_arity : int array;
  predicate_ids : int array;
  keys : int Keys.t;  (** feature ids by legacy name and arity *)
  defs : int Defs.t;  (** feature ids of definition atoms *)
  mutable count : int;
  mutable feature_names : string array;  (** by feature id *)
  mutable feature_arity : int array;
  mutable feature_hash : int array;  (** by [feature]: id * 2 + polarity *)
  definition_keys : int array;  (** definition feature cache, direct-mapped: the feature *)
  definition_names : string array;  (** its legacy name *)
  definition_hash : int array;  (** its legacy hash *)
  heads : int Keys.t;  (** head codes of named function symbols, by (name, arity) *)
  skolem_heads : int Defs.t;  (** head codes of Skolem symbols outside the encoding ranges *)
  mutable head_count : int;
  head_keys : string array;  (** head code cache, direct-mapped by [slot]: the name *)
  head_arity : int array;
  head_ids : int array;
}

(* A cheap, allocation-free cache slot for a string (below [slots], a power of two): its length
   and three of its bytes. Distinct names rarely share one; a shared slot only costs a
   lookup. *)
let[@inline] slot slots s =
  let n = String.length s in
  if n = 0 then 0
  else
    let a = Char.code (String.unsafe_get s 0)
    and b = Char.code (String.unsafe_get s (n - 1))
    and c = Char.code (String.unsafe_get s (n lsr 1)) in
    ((n * 0x9e3779b1 lxor (a * 0x85ebca6b) lxor (b * 0xc2b2ae35) lxor (c * 0x27d4eb2f)) lsr 11)
    land (slots - 1)

(* [feature]: an interned (kind, name, arity) id times two, plus one when the literal is positive.
   Its hash is the hash of the key [Clause.key] built before: [(positive, (name, arity))] with name
   ["p:" ^ predicate], ["d:a:i"] or ["="], hashed as Tbl.Hash.feature did. *)
type feature = int

let legacy_hash positive name arity =
  finish (mix (mix (mix seed (if positive then 17 else 19)) (String.hash name)) arity)

let register st name arity =
  let id = st.count in
  if id = Array.length st.feature_names then (
    let grow a fill =
      let b = Array.make (2 * Array.length a) fill in
      Array.blit a 0 b 0 (Array.length a);
      b
    in
    st.feature_names <- grow st.feature_names "";
    st.feature_arity <- grow st.feature_arity 0;
    let h = Array.make (4 * id) 0 in
    Array.blit st.feature_hash 0 h 0 (2 * id);
    st.feature_hash <- h);
  st.count <- id + 1;
  st.feature_names.(id) <- name;
  st.feature_arity.(id) <- arity;
  st.feature_hash.(2 * id) <- legacy_hash false name arity;
  st.feature_hash.((2 * id) + 1) <- legacy_hash true name arity;
  Keys.add st.keys (name, arity) id;
  id

let create () =
  let st =
    {
      names = Names.create 64;
      originals = Names.create 64;
      predicate_keys = Array.make predicate_slots "";
      predicate_arity = Array.make predicate_slots (-1);
      predicate_ids = Array.make predicate_slots 0;
      keys = Keys.create 64;
      defs = Defs.create 16;
      count = 0;
      feature_names = Array.make 64 "";
      feature_arity = Array.make 64 0;
      feature_hash = Array.make 128 0;
      definition_keys = Array.make definition_slots (-1);
      definition_names = Array.make definition_slots "";
      definition_hash = Array.make definition_slots 0;
      heads = Keys.create 64;
      skolem_heads = Defs.create 16;
      head_count = 0;
      head_keys = Array.make head_slots "";
      head_arity = Array.make head_slots (-1);
      head_ids = Array.make head_slots 0;
    }
  in
  (* Feature id 0 is the equality atom. *)
  ignore (register st "=" 2);
  st

let key = Domain.DLS.new_key create
let[@inline] state () = Domain.DLS.get key

(* -- canonical symbols ------------------------------------------------------------------------- *)

let canonical_name st s =
  match Names.find_opt st.names s with
  | Some c -> c
  | None ->
      Names.add st.names s s;
      s

let name s = canonical_name (state ()) s

let original s =
  let st = state () in
  match Names.find_opt st.originals s with
  | Some f -> f
  | None ->
      let s = canonical_name st s in
      let f = Wire.Original s in
      Names.add st.originals s f;
      f

(* -- literal features -------------------------------------------------------------------------- *)

let[@inline] signed id positive = (id lsl 1) lor if positive then 1 else 0
let equality positive = signed 0 positive

let predicate_id st p arity =
  match Keys.find_opt st.keys ("p:" ^ p, arity) with
  | Some id -> id
  | None -> register st ("p:" ^ p) arity

let predicate positive p arity =
  let st = state () in
  let i = slot predicate_slots p in
  let id =
    if
      Array.unsafe_get st.predicate_keys i == p
      && Int.equal (Array.unsafe_get st.predicate_arity i) arity
    then Array.unsafe_get st.predicate_ids i
    else
      let id = predicate_id st p arity in
      Array.unsafe_set st.predicate_keys i p;
      Array.unsafe_set st.predicate_arity i arity;
      Array.unsafe_set st.predicate_ids i id;
      id
  in
  signed id positive

(* A definition atom's feature: bit 61 set, then the axiom id (30 bits), the definition index
   (20 bits) and the arity (10 bits) above the polarity bit. Interned ids stay far below bit 61.
   Definitions outside these ranges (never seen in practice) are interned like predicates. *)
let definition_tag = 1 lsl 61

let definition positive (a, i) arity =
  if a >= 0 && a < 1 lsl 30 && i >= 0 && i < 1 lsl 20 && arity >= 0 && arity < 1 lsl 10 then
    definition_tag lor (a lsl 31) lor (i lsl 11) lor (arity lsl 1) lor if positive then 1 else 0
  else
    let st = state () in
    let id =
      match Defs.find_opt st.defs (a, i, arity) with
      | Some id -> id
      | None ->
          let name = Printf.sprintf "d:%d:%d" a i in
          let id =
            match Keys.find_opt st.keys (name, arity) with
            | Some id -> id
            | None -> register st name arity
          in
          Defs.add st.defs (a, i, arity) id;
          id
    in
    signed id positive

let[@inline] is_definition (f : feature) = f land definition_tag <> 0

(* The cache entry of a definition feature, filled on a miss. *)
let definition_entry st (f : feature) =
  let k = (f lsr 11) lxor (f lsr 31) lxor (f lsr 1) land (definition_slots - 1) in
  if not (Int.equal (Array.unsafe_get st.definition_keys k) f) then (
    let name =
      Printf.sprintf "d:%d:%d" ((f lsr 31) land ((1 lsl 30) - 1)) ((f lsr 11) land ((1 lsl 20) - 1))
    in
    Array.unsafe_set st.definition_keys k f;
    Array.unsafe_set st.definition_names k name;
    Array.unsafe_set st.definition_hash k (legacy_hash (f land 1 = 1) name ((f lsr 1) land 1023)));
  k

let feature_hash (f : feature) =
  let st = state () in
  if is_definition f then Array.unsafe_get st.definition_hash (definition_entry st f)
  else st.feature_hash.(f)

let[@inline] feature_equal (f : feature) g = Int.equal f g
let[@inline] positive (f : feature) = f land 1 = 1
let[@inline] flip (f : feature) = f lxor 1

let feature_name (f : feature) =
  let st = state () in
  if is_definition f then Array.unsafe_get st.definition_names (definition_entry st f)
  else st.feature_names.(f lsr 1)

let feature_arity (f : feature) =
  if is_definition f then (f lsr 1) land 1023 else (state ()).feature_arity.(f lsr 1)

(* The key [Clause.key] returned before: (positive, (name, arity)). *)
let view f = (positive f, (feature_name f, feature_arity f))

(* Stdlib.compare on the keys [view] gives: polarity, then name, then arity. *)
let compare_feature (f : feature) (g : feature) =
  if Int.equal f g then 0
  else
    let x = Bool.compare (positive f) (positive g) in
    if x <> 0 then x
    else
      let x = String.compare (feature_name f) (feature_name g) in
      if x <> 0 then x else Int.compare (feature_arity f) (feature_arity g)

(* -- head codes -------------------------------------------------------------------------------- *)

(* [head_code f arity]: an int that stands for the function symbol [f] applied to [arity]
   arguments in this Domain's searches: two (symbol, arity) pairs get the same code exactly when
   their symbols are equal ([Sym.equal]) and their arities are. Codes are non-negative. A Skolem
   symbol is encoded directly (bit 60, then its two fields and the arity); a named symbol gets the
   next id of a table keyed by (name, arity), read through a direct-mapped cache keyed by the
   physical name string (clausification's canonical names hit it). Like features, codes mean
   nothing outside their Domain. The table grows with the distinct (name, arity) pairs. *)
let skolem_tag = 1 lsl 60

let fresh_head st =
  let id = st.head_count in
  st.head_count <- id + 1;
  id

let head_code (f : Wire.symbol) arity =
  match f with
  | Wire.Skolem (a, b)
    when a >= 0 && a < 1 lsl 25 && b >= 0 && b < 1 lsl 25 && arity >= 0 && arity < 1 lsl 10 ->
      skolem_tag lor (a lsl 35) lor (b lsl 10) lor arity
  | Wire.Skolem (a, b) -> (
      let st = state () in
      match Defs.find_opt st.skolem_heads (a, b, arity) with
      | Some id -> id
      | None ->
          let id = fresh_head st in
          Defs.add st.skolem_heads (a, b, arity) id;
          id)
  | Wire.Original name ->
      let st = state () in
      let i = slot head_slots name in
      if
        Array.unsafe_get st.head_keys i == name
        && Int.equal (Array.unsafe_get st.head_arity i) arity
      then Array.unsafe_get st.head_ids i
      else
        let id =
          match Keys.find_opt st.heads (name, arity) with
          | Some id -> id
          | None ->
              let id = fresh_head st in
              Keys.add st.heads (name, arity) id;
              id
        in
        Array.unsafe_set st.head_keys i name;
        Array.unsafe_set st.head_arity i arity;
        Array.unsafe_set st.head_ids i id;
        id
