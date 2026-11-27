(* Observational-equivalence (OE) enumeration of schema conditions, used only
   on the search side of the schema probe lane. Nothing here is trusted: a
   condition is merely a candidate whose schema instance the lane may probe,
   and every resulting proof is checked by the ordinary kernel.

   The conditions are the theory's own first-order formulas, enumerated
   bottom-up over its signature as in enumerative program synthesis (TRANSIT,
   Udupa et al. PLDI 2013; ESCHER, Albarghouthi et al. CAV 2013; EUSolver,
   Alur et al. TACAS 2017):

   - atoms over the level variables, the constants and depth-1 applications
     of the function symbols (to variables and constants);
   - negation, binary conjunction and disjunction;
   - existential and universal quantifiers, which lower the level.

   A level-k formula has its free variables among v0 .. v(k-1). v0 is the
   condition's principal variable (Wire.F 0); the others are bound by the
   quantifiers that close the formula down to level 1, the level of a
   condition. Two formulas of one level are observationally equivalent when
   they have the same truth table: the same value under every assignment of
   their variables in every structure of a pool (the probe lane's
   finite-model pool). Only the first formula of each class and level is
   kept, and only kept formulas are combined further, so the enumeration
   walks semantic classes instead of syntax.

   Order. Formulas are built in buckets (level k, size s). Bucket (k, s) can
   reach level 1 only through k - 1 quantifiers, at size s + k - 1, so the
   buckets are built on anti-diagonals d = k + s - 1, highest level first
   (bucket (k, s) uses (k + 1, s - 1) of the same diagonal and smaller sizes
   of its own level): the level is not fixed in advance but grows with the
   size (K and size are diagonalised). A level exists only while its truth
   tables over the first pool fit [table_bits] bits, which bounds K by the
   pool (a rebuild on a refined pool keeps K). Inside a bucket
   the linear constructions come first (negations, then quantifiers), then
   the pairs of each size split, in diagonal order over the two operand
   lists, so a bucket cut by its caps keeps the combinations of the earliest
   (smallest, first-found) operands.

   There is no condition prior and no tuned formula set: the grammar is the
   theory's own formula language, reordered by semantic novelty on the
   theory's own models.

   Budgets are deterministic. [advance] stops after a quota of steps (about
   one word operation each: a fixed cost per candidate plus the table words
   and bits it reads, writes and hashes), never after a wall-clock time; a bucket keeps at most [bucket_cap] formulas and
   examines at most [examine_factor] times as many candidates; the bank's
   footprint is capped in words ([word_cap]); the diagonal is capped by
   [max_diagonal]. *)

type term = Var of int | App of string * term list

type form =
  | Pred of string * term list
  | Eq of term * term
  | Not of form
  | And of form * form
  | Or of form * form
  | Ex of form
  | All of form

let rec size = function
  | Pred _ | Eq _ -> 1
  | Not f | Ex f | All f -> 1 + size f
  | And (f, g) | Or (f, g) -> 1 + size f + size g

(* De Bruijn conversion of a formula of [level] variables: v0 is Free 0, vj
   (j >= 1) is bound by the j-th enclosing quantifier from the outside, i.e.
   (level - 1 - j) binders up. *)
let rec wire_term level = function
  | Var 0 -> Wire.F 0
  | Var j -> Wire.B (level - 1 - j)
  | App (s, ts) -> Wire.App (s, List.map (wire_term level) ts)

let rec wire level = function
  | Pred (p, ts) -> Wire.Pred (p, List.map (wire_term level) ts)
  | Eq (a, b) -> Wire.Eq (wire_term level a, wire_term level b)
  | Not f -> Wire.Neg (wire level f)
  | And (f, g) -> Wire.Conj [ wire level f; wire level g ]
  | Or (f, g) -> Wire.Disj [ wire level f; wire level g ]
  | Ex f -> Wire.Ex (wire (level + 1) f)
  | All f -> Wire.All (wire (level + 1) f)

(* A level-1 formula as a schema condition (Free 0 is the principal variable). *)
let condition f = wire 1 f

(* ---------- truth tables ---------- *)

(* Step costs, in about one word operation each: a candidate's class lookup,
   one atom evaluation (per assignment), and one chunk of a projection. *)
let candidate_steps = 24
let atom_steps = 24
let bit_steps = 4
let rec pow n k = if k = 0 then 1 else n * pow n (k - 1)

(* Per level k, model i of size n has n^k bits at offsets.(k).(i); the index
   of an assignment is v0 + n*v1 + n^2*v2 + ... *)
type layout = { sizes : int array; offsets : int array array; bits : int array }

let layout sizes levels =
  let offsets =
    Array.init (levels + 1) (fun k ->
        let acc = ref 0 in
        Array.map
          (fun n ->
            let o = !acc in
            acc := !acc + pow n k;
            o)
          sizes)
  in
  let bits = Array.init (levels + 1) (fun k -> Array.fold_left (fun a n -> a + pow n k) 0 sizes) in
  { sizes; offsets; bits }

(* A truth table: 63 bits per word (all the bits of an OCaml int). *)
type table = int array

let word_bits = 63
let nwords bits = (bits + word_bits - 1) / word_bits
let get (b : table) i = (Array.unsafe_get b (i / word_bits) lsr (i mod word_bits)) land 1 = 1

let set (b : table) i =
  let j = i / word_bits in
  Array.unsafe_set b j (Array.unsafe_get b j lor (1 lsl (i mod word_bits)))

let negate bits (a : table) : table =
  let n = Array.length a in
  let r = Array.make n 0 in
  for i = 0 to n - 1 do
    Array.unsafe_set r i (lnot (Array.unsafe_get a i))
  done;
  (* Clear the bits past the table's end. *)
  let used = bits - ((n - 1) * word_bits) in
  if n > 0 && used < word_bits then r.(n - 1) <- r.(n - 1) land ((1 lsl used) - 1);
  r

let combine ~conj (a : table) (b : table) : table =
  let n = Array.length a in
  let r = Array.make n 0 in
  if conj then
    for i = 0 to n - 1 do
      Array.unsafe_set r i (Array.unsafe_get a i land Array.unsafe_get b i)
    done
  else
    for i = 0 to n - 1 do
      Array.unsafe_set r i (Array.unsafe_get a i lor Array.unsafe_get b i)
    done;
  r

(* Classes of one level: tables hashed over every word. *)
module Classes = Hashtbl.Make (struct
  type t = table

  let equal (a : t) (b : t) =
    let n = Array.length a in
    n = Array.length b
    &&
    let rec go i = i >= n || (Array.unsafe_get a i = Array.unsafe_get b i && go (i + 1)) in
    go 0

  let hash (a : t) =
    let h = ref (Array.length a) in
    for i = 0 to Array.length a - 1 do
      h := !h lxor Array.unsafe_get a i * 0x2545F4914F6CDD1D
    done;
    !h lxor (!h lsr 31) land max_int
end)

(* Bits [pos, pos + len) of [t] as an int (len <= 62), and their insertion. *)
let chunk = 62

let extract (t : table) pos len =
  let w = pos / word_bits and b = pos mod word_bits in
  let lo = Array.unsafe_get t w lsr b in
  let v =
    if b + len > word_bits then lo lor (Array.unsafe_get t (w + 1) lsl (word_bits - b)) else lo
  in
  v land ((1 lsl len) - 1)

let insert (r : table) pos len v =
  let w = pos / word_bits and b = pos mod word_bits in
  Array.unsafe_set r w (Array.unsafe_get r w lor (v lsl b));
  if b + len > word_bits then
    Array.unsafe_set r (w + 1) (Array.unsafe_get r (w + 1) lor (v lsr (word_bits - b)))

(* Quantify the top variable v_k of a level-(k+1) table: a level-k table. In
   model m of size n, the level-(k+1) block is n consecutive level-k blocks
   (one per value of v_k), so the result is their bitwise disjunction
   (conjunction), [chunk] bits at a time. *)
let project lay ~exists k t =
  let r = Array.make (nwords lay.bits.(k)) 0 in
  Array.iteri
    (fun m n ->
      let o1 = lay.offsets.(k + 1).(m) and o0 = lay.offsets.(k).(m) in
      let block = pow n k in
      let c = ref 0 in
      while !c < block do
        let len = min chunk (block - !c) in
        let acc = ref (if exists then 0 else (1 lsl len) - 1) in
        for j = 0 to n - 1 do
          let x = extract t (o1 + (block * j) + !c) len in
          acc := if exists then !acc lor x else !acc land x
        done;
        insert r (o0 + !c) len !acc;
        c := !c + len
      done)
    lay.sizes;
  r

(* Steps of one projection to level k: one per chunk read or written. *)
let project_steps lay k =
  let total = ref 0 in
  Array.iter
    (fun n ->
      let chunks = (pow n k + chunk - 1) / chunk in
      total := !total + (bit_steps * (n + 1) * chunks))
    lay.sizes;
  !total

(* Value of [t] under assignment [idx] of level k in model [m]: variables
   decode the mixed-radix index; an unknown symbol raises Not_found. *)
let rec value (m : Semantic.model) idx = function
  | Var j -> idx / pow m.size j mod m.size
  | App (s, ts) ->
      let args = List.map (value m idx) ts in
      (Hashtbl.find m.funs (s, List.length ts)).(Semantic.index m.size args)

let holds (m : Semantic.model) idx = function
  | Pred (p, ts) -> (
      match Hashtbl.find_opt m.preds (p, List.length ts) with
      | Some table -> table.(Semantic.index m.size (List.map (value m idx) ts))
      | None -> false)
  | Eq (a, b) -> value m idx a = value m idx b
  | _ -> invalid_arg "Observational.holds: not an atom"

let atom_table lay models k f =
  let r = Array.make (nwords lay.bits.(k)) 0 in
  Array.iteri
    (fun i (m : Semantic.model) ->
      let o = lay.offsets.(k).(i) in
      for idx = 0 to pow m.size k - 1 do
        if try holds m idx f with Not_found | Invalid_argument _ -> false then set r (o + idx)
      done)
    models;
  r

(* Terms of level k: the variables, the constants, and every function symbol
   applied to variables and constants (depth <= 1). Atoms: every predicate
   applied to terms, and the equalities between two distinct terms. *)
let terms signature k =
  let vars = List.init k (fun j -> Var j) in
  let funs = Signature.functions signature in
  let consts = List.filter_map (fun (s, a) -> if a = 0 then Some (App (s, [])) else None) funs in
  let base = vars @ consts in
  let rec tuples pool n =
    if n = 0 then [ [] ]
    else List.concat_map (fun t -> List.map (fun r -> t :: r) (tuples pool (n - 1))) pool
  in
  let apps =
    List.concat_map
      (fun (s, a) -> if a = 0 then [] else List.map (fun ts -> App (s, ts)) (tuples base a))
      funs
  in
  (base @ apps, tuples)

let atoms signature k =
  let ts, tuples = terms signature k in
  let preds =
    List.concat_map
      (fun (p, a) -> List.map (fun args -> Pred (p, args)) (tuples ts a))
      (Signature.predicates signature)
  in
  let arr = Array.of_list ts in
  let eqs = ref [] in
  Array.iteri (fun i s -> Array.iteri (fun j t -> if i < j then eqs := Eq (s, t) :: !eqs) arr) arr;
  Array.of_list (preds @ List.rev !eqs)

(* ---------- the bank ---------- *)

type entry = { form : form; table : table }

(* Construction stage of the current bucket (level k, size s). *)
type stage =
  | Atoms of int  (** next atom (size 1) *)
  | Negations of int  (** next formula of (k, s - 1) *)
  | Quantifiers of int * bool  (** next formula of (k + 1, s - 1); [true]: its universal is next *)
  | Pairs of int * int * int * bool
      (** split s1 (with s2 = s - 1 - s1), pair diagonal, first index; [true]: the disjunction of
          the pair is next *)

type t = {
  signature : Signature.t;
  models : Semantic.model array;
  lay : layout;
  levels : int;  (** K: the highest level whose tables fit [table_bits] *)
  atoms_of : form array array;  (** per level 1..K *)
  seen : unit Classes.t array;  (** classes per level *)
  banks : (int * int, entry array) Hashtbl.t;  (** finished buckets *)
  project_cost : int array;  (** steps of one projection to each level *)
  bucket_cap : int;
  examine_cap : int;
  word_cap : int;
  max_diagonal : int;
  mutable diagonal : int;
  mutable level : int;
  mutable stage : stage;
  mutable current : entry list;  (** kept formulas of the current bucket, newest first *)
  mutable count : int;  (** kept in the current bucket *)
  mutable tried : int;  (** examined in the current bucket *)
  mutable words : int;  (** footprint of the bank (words, estimated per entry) *)
  mutable steps : int;
  mutable examined : int;
  mutable kept : int;
  mutable finished : bool;
}

let table_bits = 4_096
let max_levels = 8
let examine_factor = 16

(* Estimated words of one kept entry: the table block, the entry and form
   nodes, the class table binding and the bank slot. *)
let entry_words table = 16 + Array.length table

(* The highest level whose tables over [pool] fit [table_bits] bits. *)
let fitting_levels (pool : Semantic.pool) =
  let sizes = Array.of_list (List.map (fun (m : Semantic.model) -> m.size) pool.models) in
  let full = layout sizes max_levels in
  let rec top k = if k < max_levels && full.bits.(k + 1) <= table_bits then top (k + 1) else k in
  if sizes = [||] then 0 else top 0

(* [levels] (default: [fitting_levels pool]) fixes K, e.g. across rebuilds on
   a pool that counter-models refined. *)
let create ?(bucket_cap = 10_000) ?(word_cap = 8_000_000) ?(max_diagonal = 24) ?levels signature
    (pool : Semantic.pool) =
  let models = Array.of_list pool.models in
  let sizes = Array.map (fun (m : Semantic.model) -> m.size) models in
  let levels =
    if models = [||] then 0 else min max_levels (Option.value levels ~default:(fitting_levels pool))
  in
  let lay = layout sizes levels in
  {
    signature;
    models;
    lay;
    levels;
    atoms_of = Array.init (levels + 1) (fun k -> if k = 0 then [||] else atoms signature k);
    seen = Array.init (levels + 1) (fun _ -> Classes.create 1024);
    project_cost = Array.init (levels + 1) (fun k -> if k < levels then project_steps lay k else 0);
    banks = Hashtbl.create 64;
    bucket_cap = max 1 bucket_cap;
    examine_cap = examine_factor * max 1 bucket_cap;
    word_cap;
    max_diagonal;
    diagonal = 1;
    level = 1;
    stage = Atoms 0;
    current = [];
    count = 0;
    tried = 0;
    words = 0;
    steps = 0;
    examined = 0;
    kept = 0;
    finished = levels = 0;
  }

let levels e = e.levels
let models e = e.models

(* The extension of a level-1 table in model [i]: bit x is the value at
   v0 = x. Only for models of at most 62 elements. *)
let extension e table i =
  let o = e.lay.offsets.(1).(i) in
  let r = ref 0 in
  for x = e.models.(i).size - 1 downto 0 do
    r := (!r lsl 1) lor if get table (o + x) then 1 else 0
  done;
  !r

(* The extension of a level-1 formula in a model outside the bank, by direct
   evaluation (bit x is its value at v0 = x), and its cost in steps. Only for
   models of at most 62 elements. *)
let extension_in f (m : Semantic.model) =
  let n = m.size in
  let env = Array.make (max_levels + 2) 0 in
  let ops = ref 0 in
  let rec term = function
    | Var j -> env.(j)
    | App (s, ts) -> (Hashtbl.find m.funs (s, List.length ts)).(Semantic.index n (List.map term ts))
  in
  let rec holds level f =
    incr ops;
    match f with
    | Pred (p, ts) -> (
        match Hashtbl.find_opt m.preds (p, List.length ts) with
        | Some table -> table.(Semantic.index n (List.map term ts))
        | None -> false)
    | Eq (a, b) -> term a = term b
    | Not g -> not (holds level g)
    | And (g, h) -> holds level g && holds level h
    | Or (g, h) -> holds level g || holds level h
    | Ex g ->
        let r = ref false and i = ref 0 in
        while (not !r) && !i < n do
          env.(level) <- !i;
          r := holds (level + 1) g;
          incr i
        done;
        !r
    | All g ->
        let r = ref true and i = ref 0 in
        while !r && !i < n do
          env.(level) <- !i;
          r := holds (level + 1) g;
          incr i
        done;
        !r
  in
  let r = ref 0 in
  for x = n - 1 downto 0 do
    env.(0) <- x;
    r :=
      (!r lsl 1) lor if try holds 1 f with Not_found | Invalid_argument _ -> false then 1 else 0
  done;
  (!r, atom_steps * !ops)

let finished e = e.finished
let steps e = e.steps
let examined e = e.examined
let kept e = e.kept
let words e = e.words
let diagonal e = e.diagonal
let bank e k s = Option.value ~default:[||] (Hashtbl.find_opt e.banks (k, s))
let size_of e = e.diagonal - e.level + 1

(* The first stage of bucket (k, s). *)
let first_stage s = if s = 1 then Atoms 0 else Negations 0

(* Freeze the current bucket and move to the next one: the next lower level
   of this diagonal, else the top level of the next diagonal. *)
let next_bucket e =
  Hashtbl.replace e.banks (e.level, size_of e) (Array.of_list (List.rev e.current));
  e.current <- [];
  e.count <- 0;
  e.tried <- 0;
  if e.level > 1 then e.level <- e.level - 1
  else (
    e.diagonal <- e.diagonal + 1;
    e.level <- min e.levels e.diagonal);
  if e.diagonal > e.max_diagonal then e.finished <- true else e.stage <- first_stage (size_of e)

(* Examine one candidate whose table cost [cost] steps to compute (see
   [step]); hashing and comparing it costs one step per word, and the class
   lookup a fixed overhead. [true] when [emit] asks the caller's turn to stop. *)
let consider e k form table ~cost ~emit =
  e.examined <- e.examined + 1;
  e.tried <- e.tried + 1;
  e.steps <- e.steps + candidate_steps + cost + (2 * Array.length table);
  if Classes.mem e.seen.(k) table then false
  else (
    Classes.add e.seen.(k) table ();
    e.current <- { form; table } :: e.current;
    e.count <- e.count + 1;
    e.kept <- e.kept + 1;
    e.words <- e.words + entry_words table;
    if e.words >= e.word_cap then e.finished <- true;
    k = 1 && emit form table)

(* The next valid pair (s1, diagonal, i) at or after the given one, for the
   operand buckets of size s1 and s - 1 - s1 (s1 <= s2; i < j inside one
   bucket), or [None] after the last split. *)
let rec next_pair e s s1 diag i =
  let s2 = s - 1 - s1 in
  if s1 > s2 then None
  else
    let n1 = Array.length (bank e e.level s1) and n2 = Array.length (bank e e.level s2) in
    if n1 = 0 || n2 = 0 || diag > n1 + n2 - 2 then next_pair e s (s1 + 1) 0 0
    else
      let lo = max i (max 0 (diag - (n2 - 1))) and hi = min diag (n1 - 1) in
      (* Inside one bucket only i < j = diag - i. *)
      let hi = if s1 <> s2 then hi else if diag = 0 then -1 else min hi ((diag - 1) / 2) in
      if lo > hi then next_pair e s s1 (diag + 1) 0 else Some (s1, diag, lo)

(* One construction step of the current bucket. *)
let step e ~emit =
  let k = e.level and s = size_of e in
  let bits = e.lay.bits.(k) in
  let full () = e.count >= e.bucket_cap || e.tried >= e.examine_cap in
  match e.stage with
  | _ when full () ->
      next_bucket e;
      false
  | Atoms i ->
      let atoms = e.atoms_of.(k) in
      if i >= Array.length atoms then (
        next_bucket e;
        false)
      else (
        e.stage <- Atoms (i + 1);
        let f = atoms.(i) in
        let table = atom_table e.lay e.models k f in
        consider e k f table ~cost:(atom_steps * bits) ~emit)
  | Negations i ->
      let b = bank e k (s - 1) in
      if i >= Array.length b then (
        e.stage <- (if k < e.levels then Quantifiers (0, false) else Pairs (1, 0, 0, false));
        false)
      else (
        e.stage <- Negations (i + 1);
        match b.(i).form with
        | Not _ -> false
        | f -> consider e k (Not f) (negate bits b.(i).table) ~cost:(Array.length b.(i).table) ~emit)
  | Quantifiers (i, universal) ->
      let b = bank e (k + 1) (s - 1) in
      if i >= Array.length b then (
        e.stage <- Pairs (1, 0, 0, false);
        false)
      else (
        e.stage <- (if universal then Quantifiers (i + 1, false) else Quantifiers (i, true));
        let x = b.(i) in
        let table = project e.lay ~exists:(not universal) k x.table in
        consider e k
          (if universal then All x.form else Ex x.form)
          table ~cost:e.project_cost.(k) ~emit)
  | Pairs (s1, diag, i, disjunction) -> (
      match next_pair e s s1 diag i with
      | None ->
          next_bucket e;
          false
      | Some (s1, diag, i) ->
          let j = diag - i in
          let a = (bank e k s1).(i) and b = (bank e k (s - 1 - s1)).(j) in
          e.stage <-
            (if disjunction then Pairs (s1, diag, i + 1, false) else Pairs (s1, diag, i, true));
          let table = combine ~conj:(not disjunction) a.table b.table in
          consider e k
            (if disjunction then Or (a.form, b.form) else And (a.form, b.form))
            table
            ~cost:(2 * Array.length table)
            ~emit)

(* Build until [quota] more steps are spent, the bank is finished, or [emit]
   (called with every new level-1 formula and its table, i.e. every new
   condition class) returns [true]. *)
let advance e ~quota ~emit =
  let stop = if quota >= max_int - e.steps then max_int else e.steps + max 1 quota in
  let halted = ref false in
  while (not e.finished) && (not !halted) && e.steps < stop do
    halted := step e ~emit
  done

(* Whole enumeration at once with a fixed pool (tests and offline tools):
   the first [limit] condition classes, in discovery order. *)
let enumerate ?bucket_cap ?word_cap ?max_diagonal ~limit signature pool =
  let e = create ?bucket_cap ?word_cap ?max_diagonal signature pool in
  let out = ref [] and n = ref 0 in
  while (not e.finished) && !n < limit do
    advance e ~quota:max_int ~emit:(fun f _ ->
        out := f :: !out;
        incr n;
        !n >= limit)
  done;
  List.rev !out
