open Wire
(** Term orderings of the search: unit-weight KBO (including variable multiplicities), the default,
    or a lexicographic path ordering (LPO) that a strategy installs with its precedence. Both extend
    to literals by the standard multiset encoding: s=t maps to [{s,t}], s<>t to [{s,s,t,t}].
    Predicate atoms use a separate head namespace and a private truth constant. An ordering only
    restricts which inferences and rewrites the search performs; the kernel never consults it. *)

type head = Truth | Function of symbol | Predicate of string | Definition of (int * int)
type tree = Var of variable | App of head * tree list

let rec of_term = function V v -> Var v | Fn (f, ts) -> App (Function f, List.map of_term ts)

(* (head, arity) keys with monomorphic hashing and equality: a lookup in the installed table
   answers exactly as the generic table does, without the polymorphic hash and comparison of the
   key's symbol (a KBO comparison of a strategy order makes one lookup per symbol occurrence). *)
module Heads = Hashtbl.Make (struct
  type t = head * int

  let equal ((a, n) : t) ((b, m) : t) =
    Int.equal n m
    &&
    match (a, b) with
    | Truth, Truth -> true
    | Function f, Function g -> Sym.equal f g
    | Predicate p, Predicate q -> String.equal p q
    | Definition (x, y), Definition (u, v) -> Int.equal x u && Int.equal y v
    | _ -> false

  let hash ((h, n) : t) =
    let open Tbl.Hash in
    finish
      (mix
         (match h with
         | Truth -> mix seed 29
         | Function f -> symbol seed f
         | Predicate p -> string (mix seed 31) p
         | Definition (a, b) -> mix (mix (mix seed 37) a) b)
         n)
end)

(** [Kbo]: Knuth-Bendix ordering with the table's symbol weights (unit weights without a table).
    [Lpo]: E's LPO4 (ORDERINGS/cto_lpo.c [lpo4_greater], Loechner's lpo_4 without caching) on the
    precedence alone; the table's weights are ignored. *)
type kind = Kbo | Lpo

(* A term-ordering instance. The standard order is KBO; it compares (head,
   arity) with OCaml's [compare] (alphabetical by symbol) and gives every symbol
   weight 1. A strategy may install a precedence table from the input clauses
   instead: (head, arity) -> (rank within its head class, symbol weight);
   symbols first seen later rank above every known one; and with it the LPO.
   One engine owns one order, fixed before its first input clause, so
   comparisons never change during a search. *)
type order = {
  mutable table : (head * int, int * int) Hashtbl.t option;
  owned : bool;
  mutable unified : bool;
      (** E's precedence (OCBFunCompare, cto_ocb.h:227): the truth constant is smallest, every other
          known symbol compares by its rank whatever its head class, and symbols first seen after
          installation are smaller than every known one. *)
  mutable heads : (int * int) Heads.t;  (** [table]'s entries, for the lookups *)
  mutable kind : kind;
  symbols : symbol array;
      (** A direct-mapped cache of [heads]' answers for function symbols, keyed by the physical
          symbol and its arity ([wire_kbo]); [symbol_arity] is -1 in an empty slot. *)
  symbol_arity : int array;
  symbol_known : bool array;  (** whether [heads] has an entry *)
  symbol_rank : int array;
  symbol_weight : int array;
  mutable vampire : vampire option;
      (** Vampire's literal comparison ({!vampire_literal_compare}) instead of the multiset
          encoding, for a Vampire slice member. *)
}

and vampire = {
  levels : (head * int, int) Hashtbl.t;
  reverse : bool;
  ids : (head * int, int) Hashtbl.t;
      (** Vampire's symbol numbers (order of first occurrence), for the selection functions' lexical
          tie-break. *)
}
(** Vampire's literal order (Kernel/Ordering.cpp PrecedenceOrdering::compare): predicate levels
    ([levels], equality below every predicate), then for two equations the comparison of their
    argument pairs (Kernel/Ordering_Equality.cpp), for two predicate atoms the term ordering on the
    atoms (KBO with the predicate precedence of the table, LPO: the arguments lexicographically for
    one predicate, the precedence otherwise). Polarity only decides between complementary literals
    (the negative one is smaller) and, with [reverse] (lcm=reverse), puts negative predicate
    literals below positive ones. *)

let symbol_slots = 256

let make ~owned =
  {
    table = None;
    owned;
    unified = false;
    heads = Heads.create 1;
    kind = Kbo;
    symbols = Array.make symbol_slots (Skolem (-1, -1));
    symbol_arity = Array.make symbol_slots (-1);
    symbol_known = Array.make symbol_slots false;
    symbol_rank = Array.make symbol_slots 0;
    symbol_weight = Array.make symbol_slots 1;
    vampire = None;
  }

let standard = make ~owned:false
let create () = make ~owned:true
let kind order = order.kind

(* The installed table never changes afterwards; the symbol cache starts empty with it. *)
let set_table order tbl =
  order.table <- Some tbl;
  order.heads <- Heads.of_seq (Hashtbl.to_seq tbl);
  Array.fill order.symbol_arity 0 symbol_slots (-1)

let class_index = function Truth -> 0 | Function _ -> 1 | Predicate _ -> 2 | Definition _ -> 3

(** A symbol's position in the installed precedence table (E's prec_weights for an E instance); 0
    without a table and for symbols outside it. *)
let rank order key = match Heads.find_opt order.heads key with Some (r, _) -> r | None -> 0

let compare_heads order ((f, n) as a) ((g, m) as b) =
  match order.table with
  | None -> compare a b
  | Some _ when order.unified -> (
      match (f, g) with
      | Truth, Truth -> 0
      | Truth, _ -> -1
      | _, Truth -> 1
      | _ -> (
          match (Heads.find_opt order.heads a, Heads.find_opt order.heads b) with
          | Some (x, _), Some (y, _) -> compare x y
          | Some _, None -> 1
          | None, Some _ -> -1
          | None, None -> compare (f, n) (g, m)))
  | Some _ -> (
      let c = compare (class_index f) (class_index g) in
      if c <> 0 then c
      else
        match (Heads.find_opt order.heads a, Heads.find_opt order.heads b) with
        | Some (x, _), Some (y, _) -> compare x y
        (* A weight-0 unary symbol (rank max_int, see Eorder.table) stays the greatest
           function symbol even against symbols first seen after installation. *)
        | Some (x, _), None -> if x = max_int then 1 else -1
        | None, Some (y, _) -> if y = max_int then -1 else 1
        | None, None -> compare (f, n) (g, m))

(* [compare (Function f, n) (Function g, m)], the precedence without a table: OCaml's order on
   symbols (Original before Skolem, names as strings, Skolem fields as ints), then the arity. Only
   its sign is used. *)
let compare_plain (f : symbol) n (g : symbol) m =
  let c =
    match (f, g) with
    | Original a, Original b -> if a == b then 0 else String.compare a b
    | Original _, Skolem _ -> -1
    | Skolem _, Original _ -> 1
    | Skolem (a, b), Skolem (c, d) ->
        let x = Int.compare a c in
        if x <> 0 then x else Int.compare b d
  in
  if c <> 0 then c else Int.compare n m

(* The cache slot of [heads]' entry for [f] with [n] arguments, filled on a miss. *)
let symbol_slot order (f : symbol) n =
  let h =
    match f with
    | Original s -> Tbl.Hash.string_hash s
    | Skolem (a, b) -> Tbl.Hash.mix (Tbl.Hash.mix Tbl.Hash.seed a) b
  in
  let i = Tbl.Hash.finish (Tbl.Hash.mix h n) land (symbol_slots - 1) in
  if
    not
      (Array.unsafe_get order.symbols i == f && Int.equal (Array.unsafe_get order.symbol_arity i) n)
  then (
    let known, rank, weight =
      match Heads.find_opt order.heads (Function f, n) with
      | Some (r, w) -> (true, r, w)
      | None -> (false, 0, 1)
    in
    Array.unsafe_set order.symbols i f;
    Array.unsafe_set order.symbol_arity i n;
    Array.unsafe_set order.symbol_known i known;
    Array.unsafe_set order.symbol_rank i rank;
    Array.unsafe_set order.symbol_weight i weight);
  i

(* [compare_heads order (Function f, n) (Function g, m)] (its sign). *)
let compare_functions order (f : symbol) n (g : symbol) m =
  match order.table with
  | None -> compare_plain f n g m
  | Some _ -> (
      (* Each symbol's entry is read before the other's lookup, which may reuse its slot. *)
      let i = symbol_slot order f n in
      let x = Array.unsafe_get order.symbol_rank i
      and known_f = Array.unsafe_get order.symbol_known i in
      let j = symbol_slot order g m in
      let y = Array.unsafe_get order.symbol_rank j
      and known_g = Array.unsafe_get order.symbol_known j in
      match (known_f, known_g) with
      | true, true -> Int.compare x y
      | true, false -> if order.unified || x = max_int then 1 else -1
      | false, true -> if order.unified || y = max_int then -1 else 1
      | false, false -> compare_plain f n g m)

let rec unit_weight = function
  | Var _ -> 1
  | App (_, ts) -> 1 + List.fold_left (fun n t -> n + unit_weight t) 0 ts

let weight order t =
  match order.table with
  | None -> unit_weight t
  | Some _ ->
      let rec weight = function
        | Var _ -> 1
        | App (f, ts) ->
            let w =
              match Heads.find_opt order.heads (f, List.length ts) with
              | Some (_, w) -> w
              | None -> 1
            in
            w + List.fold_left (fun n t -> n + weight t) 0 ts
      in
      weight t

(* [weight] on a Wire term, without the tree copy: the symbol weights and the number of variable
   occurrences, separately (a variable weighs 1 in [weight]). *)
let wire_weights order term =
  let symbol f n =
    match order.table with
    | None -> 1
    | Some _ -> (
        match Heads.find_opt order.heads (Function f, n) with Some (_, w) -> w | None -> 1)
  in
  let rec go (w, v) = function
    | V _ -> (w, v + 1)
    | Fn (f, ts) -> List.fold_left go (w + symbol f (List.length ts), v) ts
  in
  go (0, 0) term

(* E's invfreq precedence: frequent symbols are small; arity, then name break
   ties. With [weights], invfreqrank symbol weights: the most frequent symbol
   weighs 1 and constants always weigh 1, so the order stays admissible. *)
let install order ~weights (clauses : clause list) =
  if not order.owned then invalid_arg "Ordering.install: the standard order is shared";
  if order.table <> None then invalid_arg "Ordering.install: precedence already installed";
  let freq = Hashtbl.create 64 in
  let bump key =
    Hashtbl.replace freq key (1 + Option.value ~default:0 (Hashtbl.find_opt freq key))
  in
  let rec visit = function
    | V _ -> ()
    | Fn (f, ts) ->
        bump (Function f, List.length ts);
        List.iter visit ts
  in
  List.iter
    (List.iter (fun l ->
         match l.atom with
         | E (s, t) ->
             visit s;
             visit t
         | P (p, ts) ->
             bump (Predicate p, List.length ts);
             List.iter visit ts
         | D (p, ts) ->
             bump (Definition p, List.length ts);
             List.iter visit ts))
    clauses;
  let symbols = Hashtbl.fold (fun k n acc -> (k, n) :: acc) freq [] in
  let tbl = Hashtbl.create 64 in
  List.iter
    (fun cls ->
      let members =
        List.filter (fun ((h, _), _) -> class_index h = cls) symbols
        |> List.sort (fun ((ha, na), fa) ((hb, nb), fb) -> compare (-fa, na, ha) (-fb, nb, hb))
      in
      let distinct = List.sort_uniq (fun a b -> compare b a) (List.map snd members) in
      List.iteri
        (fun rank (((_, arity) as key), f) ->
          let w =
            if (not weights) || arity = 0 then 1
            else
              let rec position i = function
                | [] -> 1
                | x :: rest -> if x = f then i else position (i + 1) rest
              in
              position 1 distinct
          in
          Hashtbl.replace tbl key (rank, w))
        members)
    [ 1; 2; 3 ];
  set_table order tbl

(* Install an explicit (rank, weight) table, e.g. an E precedence (Eorder.table),
   and the ordering that uses it. *)
let install_table ?(unified = false) ?(kind = Kbo) ?vampire order tbl =
  if not order.owned then invalid_arg "Ordering.install_table: the standard order is shared";
  if order.table <> None then invalid_arg "Ordering.install_table: precedence already installed";
  set_table order tbl;
  order.unified <- unified;
  order.kind <- kind;
  order.vampire <- vampire

(* s = f(...f(x)...) for unary symbols f; with equal weights these weigh 0. *)
let rec unary_chain_over s x =
  match s with App (_, [ Var y ]) -> y = x | App (_, [ u ]) -> unary_chain_over u x | _ -> false

(* Monomorphic versions of what [kbo_greater] used polymorphic equality, hash tables and table
   lookups for: the same answers on every tree. *)
let head_equal a b =
  match (a, b) with
  | Truth, Truth -> true
  | Function f, Function g -> Sym.equal f g
  | Predicate p, Predicate q -> String.equal p q
  | Definition (x, y), Definition (u, v) -> Int.equal x u && Int.equal y v
  | _ -> false

let rec tree_equal s t =
  s == t
  ||
  match (s, t) with
  | Var x, Var y -> Sym.var x y
  | App (f, xs), App (g, ys) -> head_equal f g && trees_equal xs ys
  | _ -> false

and trees_equal xs ys =
  match (xs, ys) with
  | [], [] -> true
  | x :: xs, y :: ys -> tree_equal x y && trees_equal xs ys
  | _ -> false

(* [dominates_variables] with the counts of [t]'s variables in a short list. *)
type tree_balance = { tvar : variable; mutable tcount : int }

let tree_dominates s t =
  let cells = ref [] in
  let rec bump d = function
    | Var v -> (
        match List.find_opt (fun c -> Sym.var c.tvar v) !cells with
        | Some c -> c.tcount <- c.tcount + d
        | None -> cells := { tvar = v; tcount = d } :: !cells)
    | App (_, ts) -> List.iter (bump d) ts
  in
  bump (-1) t;
  match !cells with
  | [] -> true
  | _ ->
      bump 1 s;
      List.for_all (fun c -> c.tcount >= 0) !cells

(* [weight order t], function symbols' weights read through the symbol cache. *)
let tree_weight order t =
  match order.table with
  | None -> unit_weight t
  | Some _ ->
      let rec go n = function
        | Var _ -> n + 1
        | App (Function f, ts) ->
            let w = Array.unsafe_get order.symbol_weight (symbol_slot order f (List.length ts)) in
            List.fold_left go (n + w) ts
        | App (h, ts) ->
            let w =
              match Heads.find_opt order.heads (h, List.length ts) with
              | Some (_, w) -> w
              | None -> 1
            in
            List.fold_left go (n + w) ts
      in
      go 0 t

(* [compare_heads] (its sign), two function heads through [compare_functions]. *)
let tree_precedence order f n g m =
  match (f, g) with
  | Function f, Function g -> compare_functions order f n g m
  | _ -> compare_heads order (f, n) (g, m)

let rec kbo_greater order s t =
  (not (tree_equal s t))
  &&
  let ws = tree_weight order s and wt = tree_weight order t in
  (ws > wt || ws = wt)
  && tree_dominates s t
  && (ws > wt
     ||
     match (s, t) with
     (* KBO case for a weight-0 unary symbol: f^n(x) > x (never reached with
        positive weights, where f^n(x) is heavier than x). *)
     | App _, Var x -> unary_chain_over s x
     | App (f, xs), App (g, ys) ->
         let precedence = tree_precedence order f (List.length xs) g (List.length ys) in
         precedence > 0 || (precedence = 0 && lex order xs ys)
     | _ -> false)

and lex order xs ys =
  match (xs, ys) with
  | x :: xs, y :: ys -> if tree_equal x y then lex order xs ys else kbo_greater order x y
  | _ -> false

(* The LPO precedence: the installed head comparison, made strict on distinct
   symbols (equal ranks fall back to OCaml's order of (head, arity)), so that
   precedence-equal heads are the same symbol with the same arity. *)
let lpo_precedence order a b =
  let c = compare_heads order a b in
  if c <> 0 then c else compare a b

(* E's LPORecursionDepthLimit (cto_lpo.c:53): a comparison nested deeper than
   this answers "not greater", as in E. Answering "not greater" only adds
   inferences and withholds rewrites, so the search stays complete and
   rewriting terminates. *)
let lpo_depth_limit = 1000
let rec occurs x = function Var y -> x = y | App (_, ts) -> List.exists (occurs x) ts

(* lpo4_greater (cto_lpo.c:540): s >lpo t iff
   - f > g and s > t_j for every argument t_j (majo), or
   - f = g and the arguments are lexicographically greater, with s > t_j for the
     arguments after the first difference (lex_ma), or
   - some argument s_i >= t (alpha). A variable is never greater; s > x iff x
     occurs in s. *)
let rec lpo_greater order depth s t =
  depth <= lpo_depth_limit
  &&
  match (s, t) with
  | Var _, _ -> false
  | App _, Var x -> occurs x s
  | App (f, ss), App (g, ts) ->
      let c = lpo_precedence order (f, List.length ss) (g, List.length ts) in
      if c > 0 then lpo_majo order depth s ts
      else if c = 0 then lpo_lex_ma order depth s t ss ts
      else lpo_alpha order depth ss t

(* lpo4_alpha: some s_i >= t. *)
and lpo_alpha order depth ss t =
  List.exists (fun si -> si = t || lpo_greater order (depth + 1) si t) ss

(* lpo4_majo: s > t_j for every remaining t_j. *)
and lpo_majo order depth s ts = List.for_all (fun tj -> lpo_greater order (depth + 1) s tj) ts

(* lpo4_lex_ma: skip equal arguments; at the first difference s_i > t_i requires
   s > t_j for the later t_j, otherwise a later s_j must reach t (an earlier
   s_j = t_j or s_i itself never can). *)
and lpo_lex_ma order depth s t ss ts =
  match (ss, ts) with
  | [], _ -> false
  | _ :: _, [] -> true
  | si :: ss, ti :: ts ->
      if si = ti then lpo_lex_ma order depth s t ss ts
      else if lpo_greater order (depth + 1) si ti then lpo_majo order depth s ts
      else lpo_alpha order depth ss t

let greater_tree order s t =
  match order.kind with Kbo -> kbo_greater order s t | Lpo -> lpo_greater order 0 s t

(* {2 KBO on Wire terms}

   [wire_kbo order s t] = [kbo_greater order (of_term s) (of_term t)], computed on the Wire terms:
   no tree copy, variable counts in a short list instead of two hash tables, and the installed
   table's (rank, weight) of a function symbol read through [order]'s symbol cache. The relation
   is the same: the same weights, the same variable condition, the same precedence (the order
   [compare_heads] gives two function heads) and the same lexicographic recursion; only the order
   in which the pure conditions of one comparison are evaluated differs. *)

(* [weight order (of_term t)]. *)
let wire_weight order t =
  match order.table with
  | None ->
      let rec go n = function V _ -> n + 1 | Fn (_, ts) -> List.fold_left go (n + 1) ts in
      go 0 t
  | Some _ ->
      let rec go n = function
        | V _ -> n + 1
        | Fn (f, ts) ->
            List.fold_left go
              (n + Array.unsafe_get order.symbol_weight (symbol_slot order f (List.length ts)))
              ts
      in
      go 0 t

(* [dominates_variables (of_term s) (of_term t)]: every variable occurs in [s] at least as often
   as in [t]. *)
type balance = { var : variable; mutable count : int }

let wire_dominates s t =
  let cells = ref [] in
  let rec bump d = function
    | V v -> (
        match List.find_opt (fun c -> Sym.var c.var v) !cells with
        | Some c -> c.count <- c.count + d
        | None -> cells := { var = v; count = d } :: !cells)
    | Fn (_, ts) -> List.iter (bump d) ts
  in
  bump (-1) t;
  match !cells with
  | [] -> true
  | _ ->
      bump 1 s;
      List.for_all (fun c -> c.count >= 0) !cells

let rec wire_chain_over s x =
  match s with Fn (_, [ V y ]) -> Sym.var y x | Fn (_, [ u ]) -> wire_chain_over u x | _ -> false

let rec wire_kbo order s t =
  (not (Tbl.Equal.term s t))
  &&
  let ws = wire_weight order s and wt = wire_weight order t in
  (ws > wt || ws = wt)
  && wire_dominates s t
  && (ws > wt
     ||
     match (s, t) with
     | Fn _, V x -> wire_chain_over s x
     | Fn (f, xs), Fn (g, ys) ->
         let precedence = compare_functions order f (List.length xs) g (List.length ys) in
         precedence > 0 || (precedence = 0 && wire_lex order xs ys)
     | _ -> false)

and wire_lex order xs ys =
  match (xs, ys) with
  | x :: xs, y :: ys -> if Tbl.Equal.term x y then wire_lex order xs ys else wire_kbo order x y
  | _ -> false

let greater ?(order = standard) s t =
  match order.kind with
  | Kbo -> wire_kbo order s t
  | Lpo -> lpo_greater order 0 (of_term s) (of_term t)

let multiset_greater order xs ys =
  let rec remove_one x = function
    | [] -> None
    | y :: ys ->
        if tree_equal x y then Some ys else Option.map (fun rest -> y :: rest) (remove_one x ys)
  in
  let xs, ys =
    List.fold_left
      (fun (remaining, ys) x ->
        match remove_one x ys with Some ys -> (remaining, ys) | None -> (x :: remaining, ys))
      ([], ys) xs
  in
  (match xs with [] -> false | _ :: _ -> true)
  && List.for_all (fun y -> List.exists (fun x -> greater_tree order x y) xs) ys

let literal_terms l =
  let ts =
    match l.atom with
    | E (s, t) -> [ of_term s; of_term t ]
    | P (p, ts) -> [ App (Predicate p, List.map of_term ts); App (Truth, []) ]
    | D (p, ts) -> [ App (Definition p, List.map of_term ts); App (Truth, []) ]
  in
  if l.positive then ts else ts @ ts

type comparison = Greater | Less | Equal | Incomparable

let term_compare order s t =
  if s = t then Equal
  else if greater_tree order s t then Greater
  else if greater_tree order t s then Less
  else Incomparable

let reverse_comparison = function Greater -> Less | Less -> Greater | c -> c

(* Ordering::compareEqualities and its helpers, case by case. *)
let compare_equalities order (s1, s2) (t1, t2) =
  let cmp = term_compare order in
  let s1gt1_s2it2 s1 _s2 _t1 t2 = match cmp s1 t2 with Greater -> Greater | _ -> Incomparable in
  let s1gt1_s2lt2 s1 _s2 _t1 t2 =
    match cmp s1 t2 with Greater -> Greater | Less -> Less | _ -> Incomparable
  in
  let s1gt1 s1 s2 t1 t2 =
    match cmp s2 t2 with
    | Greater -> Greater
    | Incomparable -> s1gt1_s2it2 s1 s2 t1 t2
    | Less -> s1gt1_s2lt2 s1 s2 t1 t2
    | Equal -> Incomparable
  in
  let s1gt1_s1it2_s2it1 _s1 s2 _t1 t2 =
    match cmp s2 t2 with Greater -> Greater | _ -> Incomparable
  in
  let s1it1_s2it2 s1 s2 t1 t2 =
    match cmp s1 t2 with
    | Greater -> s1gt1_s1it2_s2it1 s1 s2 t2 t1
    | Less -> reverse_comparison (s1gt1_s1it2_s2it1 t2 t1 s1 s2)
    | _ -> Incomparable
  in
  let s1it1 s1 s2 t1 t2 =
    match cmp s2 t2 with
    | Greater -> s1gt1_s2it2 s2 s1 t2 t1
    | Incomparable -> s1it1_s2it2 s1 s2 t1 t2
    | Less -> reverse_comparison (s1gt1_s2it2 t2 t1 s2 s1)
    | Equal -> Incomparable
  in
  if s1 = t1 then cmp s2 t2
  else if s1 = t2 then cmp s2 t1
  else if s2 = t1 then cmp s1 t2
  else if s2 = t2 then cmp s1 t1
  else
    match cmp s1 t1 with
    | Greater -> s1gt1 s1 s2 t1 t2
    | Incomparable -> s1it1 s1 s2 t1 t2
    | Less -> reverse_comparison (s1gt1 t1 t2 s1 s2)
    | Equal -> Incomparable

let same_atom a b = a = b || match (a, b) with E (s, t), E (u, v) -> s = v && t = u | _ -> false

(** Vampire's comparison of two literals ([order.vampire] gives the predicate levels). *)
let vampire_literal_compare order (v : vampire) (l1 : literal) (l2 : literal) =
  if l1.positive = l2.positive && same_atom l1.atom l2.atom then Equal
  else if same_atom l1.atom l2.atom then if l1.positive then Greater else Less
  else
    let head (l : literal) =
      match l.atom with
      | E _ -> None
      | P (p, ts) -> Some (Predicate p, List.length ts)
      | D (d, ts) -> Some (Definition d, List.length ts)
    in
    let level = function
      | None -> 0
      | Some k -> 1 + Option.value ~default:0 (Hashtbl.find_opt v.levels k)
    in
    let h1 = head l1 and h2 = head l2 in
    let by_level = if h1 = h2 then 0 else compare (level h1) (level h2) in
    if by_level > 0 then Greater
    else if by_level < 0 then Less
    else
      match (l1.atom, l2.atom) with
      | E (s1, s2), E (t1, t2) ->
          compare_equalities order (of_term s1, of_term s2) (of_term t1, of_term t2)
      | _ ->
          let atom (l : literal) =
            match l.atom with
            | P (p, ts) -> App (Predicate p, List.map of_term ts)
            | D (d, ts) -> App (Definition d, List.map of_term ts)
            | E (s, t) -> App (Truth, [ of_term s; of_term t ])
          in
          let predicates () =
            match (order.kind, atom l1, atom l2) with
            | Lpo, App (p, xs), App (q, ys) ->
                if p = q && List.length xs = List.length ys then
                  let rec lex = function
                    | x :: xs, y :: ys -> (
                        match term_compare order x y with Equal -> lex (xs, ys) | c -> c)
                    | _ -> Equal
                  in
                  lex (xs, ys)
                else if lpo_precedence order (p, List.length xs) (q, List.length ys) > 0 then
                  Greater
                else Less
            | _, a, b -> term_compare order a b
          in
          if v.reverse && ((not l1.positive) || not l2.positive) then
            if (not l1.positive) && not l2.positive then reverse_comparison (predicates ())
            else if not l1.positive then Less
            else Greater
          else predicates ()

let literal_greater ?(order = standard) l r =
  match order.vampire with
  | Some v -> vampire_literal_compare order v l r = Greater
  | None -> multiset_greater order (literal_terms l) (literal_terms r)

let literal_equal l r = List.sort compare (literal_terms l) = List.sort compare (literal_terms r)

let first_negative clause =
  let rec find i = function
    | [] -> None
    | l :: rest -> if l.positive then find (i + 1) rest else Some i
  in
  find 0 clause

(* E's lit_sel_diff_weight: 100 * |w(lhs) - w(rhs)| + w(lhs) + w(rhs), with the
   truth constant (weight 1) as the right side of a predicate atom. *)
let rec plain_weight = function
  | V _ -> 1
  | Fn (_, ts) -> List.fold_left (fun n t -> n + plain_weight t) 1 ts

let complexity l =
  let a, b =
    match l.atom with
    | E (s, t) -> (plain_weight s, plain_weight t)
    | P (_, ts) | D (_, ts) -> (List.fold_left (fun n t -> n + plain_weight t) 1 ts, 1)
  in
  (100 * abs (a - b)) + a + b

let pure_variable l = match l.atom with E (V _, V _) -> true | _ -> false
let ground_literal l = Wire.variables [ l ] = []

let predicate_key l =
  match l.atom with
  | E _ -> `Eq
  | P (p, ts) -> `P (p, List.length ts)
  | D (d, ts) -> `D (d, List.length ts)

(* SelectMaxLComplexAvoidPosPred; [maximal] says whether the literal is maximal. *)
let best_negative ?(maximal = fun _ -> false) clause =
  let positives = List.filter (fun l -> l.positive) clause in
  let score i l =
    let w1 =
      (if maximal i then 0 else 100)
      + (if pure_variable l then 0 else 10)
      + if ground_literal l then 0 else 1
    in
    let w3 = List.length (List.filter (fun p -> predicate_key p = predicate_key l) positives) in
    (w1, -complexity l, w3)
  in
  let best = ref None in
  List.iteri
    (fun i l ->
      if not l.positive then
        let s = score i l in
        match !best with Some (old, _) when compare s old >= 0 -> () | _ -> best := Some (s, i))
    clause;
  Option.map snd !best

(* Vampire's selection 10 (Kernel/LiteralSelector.cpp: CompleteBestLiteralSelector<Comparator10>,
   ColoredFirst, NegativeEquality, MaximalSize, Negative, Lex): when the clause has a negative
   literal, the best negative literal: a negative equation before any other negative literal, then
   the greatest weight (symbol and variable occurrences, the predicate or equality symbol counting
   1), the first in clause order on a tie. Without a negative literal there is no selection. *)
let vampire_best_10 clause =
  let weight l =
    match l.atom with
    | E (s, t) -> 1 + plain_weight s + plain_weight t
    | P (_, ts) | D (_, ts) -> List.fold_left (fun n t -> n + plain_weight t) 1 ts
  in
  let best = ref None in
  List.iteri
    (fun i l ->
      if not l.positive then
        let key = ((match l.atom with E _ -> 0 | _ -> 1), -weight l) in
        match !best with Some (old, _) when compare key old >= 0 -> () | _ -> best := Some (key, i))
    clause;
  Option.map snd !best

(* [flags.(i)]: no other literal is greater than literal [i]. Without a
   substitution this is necessary for (strict) maximality after any
   substitution, because the order is stable under substitution. *)
let maximal_flags ?(order = standard) clause =
  let xs = Array.of_list clause in
  Array.mapi
    (fun i l ->
      let rec check j =
        j = Array.length xs || ((i = j || not (literal_greater ~order xs.(j) l)) && check (j + 1))
      in
      check 0)
    xs

let count_maximal flags = Array.fold_left (fun n b -> if b then n + 1 else n) 0 flags

(* SelectMaxLComplexAvoidPosPred with precomputed maximality [flags]. *)
let e_selection_with flags clause =
  if List.for_all (fun l -> l.positive) clause || count_maximal flags <= 1 then None
  else best_negative ~maximal:(fun i -> flags.(i)) clause

let e_selection ?order clause =
  if List.for_all (fun l -> l.positive) clause then None
  else e_selection_with (maximal_flags ?order clause) clause

(* The production selection, which the lookahead may revise. *)
let selected clause = first_negative clause

(* A unique maximal positive literal permits an admissible no-selection
   direction. A linear tournament followed by verification avoids a quadratic
   all-pairs maximality scan; incomparable literals fail verification. *)
let positive_maximum ?(order = standard) clause =
  match List.mapi (fun i l -> (i, l)) clause with
  | [] -> None
  | first :: rest ->
      let i, best =
        List.fold_left
          (fun ((_, old) as best) ((_, l) as next) ->
            if literal_greater ~order l old then next else best)
          first rest
      in
      if
        best.positive
        && List.for_all (fun (j, l) -> i = j || literal_greater ~order best l) (first :: rest)
      then Some (i, best)
      else None

(* [among j]: literal [j] takes part in the maximality comparison (default: every
   literal). E compares a selected literal only with literals it is comparable to. *)
let eligible ?(order = standard) ?(selection = true) ?(strict = false) ?among clause index app =
  match if selection then selected clause else None with
  | Some i -> i = index
  | None ->
      let literal = List.nth clause index in
      let pivot = lazy (literal_terms (Clause.map_literal app literal)) in
      let sorted_pivot = lazy (List.sort compare (Lazy.force pivot)) in
      let compared j = match among with None -> true | Some f -> f j in
      let blocks =
        match order.vampire with
        | Some v ->
            let pivot = lazy (Clause.map_literal app literal) in
            fun l ->
              let c =
                vampire_literal_compare order v (Clause.map_literal app l) (Lazy.force pivot)
              in
              c = Greater || (strict && c = Equal)
        | None ->
            fun l ->
              let terms = literal_terms (Clause.map_literal app l) in
              multiset_greater order terms (Lazy.force pivot)
              || (strict && List.sort compare terms = Lazy.force sorted_pivot)
      in
      let rec maximal j = function
        | [] -> true
        | l :: rest -> (j = index || (not (compared j)) || not (blocks l)) && maximal (j + 1) rest
      in
      maximal 0 clause

let not_less_or_equal ?(order = standard) lhs rhs =
  (not (Tbl.Equal.term lhs rhs)) && not (greater ~order rhs lhs)
