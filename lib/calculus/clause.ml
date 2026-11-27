open Wire

let map_atom f = function
  | P (s, ts) -> P (s, List.map f ts)
  | D (s, ts) -> D (s, List.map f ts)
  | E (x, y) ->
      let x = f x in
      let y = f y in
      E (x, y)

let map_literal f l = { l with atom = map_atom f l.atom }
let rec map_vars f = function V v -> f v | Fn (s, ts) -> Fn (s, List.map (map_vars f) ts)
let scope n c = List.map (map_literal (map_vars (fun (_, i) -> V (n, i)))) c

(* Stdlib.compare on Wire data, written out: the same sign for every pair of terms, atoms and
   literals (constructors in declaration order, then their fields left to right; strings by
   String.compare, as the polymorphic compare does), without the generic C traversal. *)
let compare_symbol (f : symbol) (g : symbol) =
  match (f, g) with
  | Original s, Original r -> String.compare s r
  | Original _, Skolem _ -> -1
  | Skolem _, Original _ -> 1
  | Skolem (a, b), Skolem (c, d) ->
      let x = Int.compare a c in
      if x <> 0 then x else Int.compare b d

let rec compare_term (s : term) (t : term) =
  if s == t then 0
  else
    match (s, t) with
    | V (a, b), V (c, d) ->
        let x = Int.compare a c in
        if x <> 0 then x else Int.compare b d
    | V _, Fn _ -> -1
    | Fn _, V _ -> 1
    | Fn (f, ss), Fn (g, ts) ->
        let x = compare_symbol f g in
        if x <> 0 then x else compare_terms ss ts

and compare_terms ss ts =
  match (ss, ts) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | s :: ss, t :: ts ->
      let x = compare_term s t in
      if x <> 0 then x else compare_terms ss ts

let compare_atom (a : atom) (b : atom) =
  match (a, b) with
  | P (p, ss), P (q, ts) ->
      let x = String.compare p q in
      if x <> 0 then x else compare_terms ss ts
  | P _, (E _ | D _) -> -1
  | (E _ | D _), P _ -> 1
  | E (s, t), E (u, v) ->
      let x = compare_term s u in
      if x <> 0 then x else compare_term t v
  | E _, D _ -> -1
  | D _, E _ -> 1
  | D ((a, b), ss), D ((c, d), ts) ->
      let x = Int.compare a c in
      if x <> 0 then x
      else
        let x = Int.compare b d in
        if x <> 0 then x else compare_terms ss ts

let compare_literal (l : literal) (m : literal) =
  let x = Bool.compare l.positive m.positive in
  if x <> 0 then x else compare_atom l.atom m.atom

(* Variables renamed to (0, i) in order of first occurrence (literals left to right, terms
   depth first, an equation's left side first). A short association list, since clauses have
   few variables. *)
let rename_variables c =
  let vars = ref [] and count = ref 0 in
  let rename v =
    let rec find = function
      | [] ->
          let i = !count in
          vars := (v, i) :: !vars;
          count := i + 1;
          V (0, i)
      | ((w : variable), i) :: rest ->
          if Int.equal (fst w) (fst v) && Int.equal (snd w) (snd v) then V (0, i) else find rest
    in
    find !vars
  in
  List.map (map_literal (map_vars rename)) c

let normalize c =
  (* Do not orient equality: ordering can depend on a subsequent substitution. *)
  let c = List.sort_uniq compare_literal c in
  List.sort_uniq compare_literal (rename_variables c)

let tautology c =
  List.exists
    (fun l ->
      (match l.atom with E (x, y) -> l.positive && x = y | _ -> false)
      || List.mem { l with positive = not l.positive } c)
    c

(* Clause.normalize sorts by polarity and then atom. Merge the negative and
   positive runs instead of comparing each literal with the entire clause. *)
let tautology_sorted c =
  let rec positives = function
    | [] -> []
    | l :: rest as literals -> if l.positive then literals else positives rest
  in
  let positive = positives c in
  let rec complementary negatives positives =
    match (negatives, positives) with
    | n :: ns, p :: ps when not n.positive ->
        let order = compare_atom n.atom p.atom in
        order = 0 || if order < 0 then complementary ns positives else complementary negatives ps
    | _ -> false
  in
  List.exists (fun l -> match l.atom with E (x, y) -> x = y | _ -> false) positive
  || complementary c positive

let remove i xs = List.filteri (fun j _ -> i <> j) xs
let replace i x xs = List.mapi (fun j y -> if i = j then x else y) xs

let rec term_weight = function
  | V _ -> 1
  | Fn (_, ts) -> 1 + List.fold_left (fun n t -> n + term_weight t) 0 ts

let atom_terms = function P (_, ts) | D (_, ts) -> ts | E (x, y) -> [ x; y ]

let weight c =
  List.fold_left
    (fun n l -> n + 1 + List.fold_left (fun n t -> n + term_weight t) 0 (atom_terms l.atom))
    0 c

(* The signed predicate/arity feature of a literal, interned (Intern.feature): an immediate int
   that compares with [Int.equal] and hashes and orders as the string key it replaces,
   [(positive, (name, arity))] with name ["p:" ^ predicate], ["d:a:i"] or ["="] ([key_view]). *)
type feature = Intern.feature

let key l =
  match l.atom with
  | P (s, ts) -> Intern.predicate l.positive s (List.length ts)
  | D (d, ts) -> Intern.definition l.positive d (List.length ts)
  | E _ -> Intern.equality l.positive

let key_view = Intern.view
let compare_feature = Intern.compare_feature
let flip_feature = Intern.flip

let rec subterms ?(variables = false) prefix t =
  let here = match t with V _ when not variables -> [] | _ -> [ (prefix, t) ] in
  match t with
  | V _ -> here
  | Fn (_, ts) ->
      here @ List.concat (List.mapi (fun i t -> subterms ~variables (prefix @ [ i ]) t) ts)

let positions ?(variables = false) l =
  List.concat (List.mapi (fun i t -> subterms ~variables [ i ] t) (atom_terms l.atom))

let rec at_term path t =
  match (path, t) with
  | [], _ -> t
  | i :: rest, Fn (_, ts) -> at_term rest (List.nth ts i)
  | _ -> invalid_arg "Clause: bad term path"

let at l = function
  | [] -> invalid_arg "Clause: empty atom path"
  | i :: path -> at_term path (List.nth (atom_terms l.atom) i)

let rec put_term path replacement t =
  match (path, t) with
  | [], _ -> replacement
  | i :: rest, Fn (s, ts) -> Fn (s, replace i (put_term rest replacement (List.nth ts i)) ts)
  | _ -> invalid_arg "Clause: bad replacement path"

let put l path replacement =
  match path with
  | [] -> invalid_arg "Clause: empty atom path"
  | i :: rest ->
      let ts = atom_terms l.atom in
      let ts = replace i (put_term rest replacement (List.nth ts i)) ts in
      {
        l with
        atom =
          (match (l.atom, ts) with
          | P (s, _), ts -> P (s, ts)
          | D (s, _), ts -> D (s, ts)
          | E _, [ x; y ] -> E (x, y)
          | _ -> assert false);
      }

let components ~guard clause =
  let literals = Array.of_list clause in
  let n = Array.length literals in
  let parents = Array.init n Fun.id and owners = Tbl.Pair.create n in
  let rec find i =
    if parents.(i) = i then i
    else
      let root = find parents.(i) in
      parents.(i) <- root;
      root
  in
  let join i j =
    let i = find i and j = find j in
    if i <> j then parents.(max i j) <- min i j
  in
  Array.iteri
    (fun i l ->
      guard ();
      List.iter
        (fun variable ->
          match Tbl.Pair.find_opt owners variable with
          | None -> Tbl.Pair.add owners variable i
          | Some j -> join i j)
        (Wire.variables [ l ]))
    literals;
  let groups = Array.make n [] in
  Array.iteri
    (fun i literal ->
      let root = find i in
      groups.(root) <- literal :: groups.(root))
    literals;
  Array.fold_right
    (fun group result -> if group = [] then result else List.rev group :: result)
    groups []
