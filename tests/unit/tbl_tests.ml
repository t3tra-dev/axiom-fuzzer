open Axiom_fuzzer
open Test_support
open Wire

(* Typed search tables: equality must agree with [compare = 0], equal keys must
   hash alike (including physically distinct copies), lookups must match a
   generic Stdlib table, and keys sharing long prefixes must not share one
   bucket (the defect of Stdlib's 10-word generic hash). *)

let rng = Random.State.make [| 7; 11; 2026 |]
let pick xs = List.nth xs (Random.State.int rng (List.length xs))
let symbols = [ Original "f"; Original "g"; Original "h"; Skolem (0, 1); Skolem (1, 0) ]

let rec term depth =
  if depth = 0 || Random.State.int rng 3 = 0 then
    if Random.State.bool rng then V (Random.State.int rng 2, Random.State.int rng 3)
    else Fn (pick [ Original "a"; Original "b"; Skolem (2, 2) ], [])
  else Fn (pick symbols, List.init (1 + Random.State.int rng 2) (fun _ -> term (depth - 1)))

let atom () =
  match Random.State.int rng 3 with
  | 0 -> P (pick [ "p"; "q" ], List.init (Random.State.int rng 3) (fun _ -> term 2))
  | 1 -> E (term 2, term 2)
  | _ -> D ((Random.State.int rng 2, 1), [ term 1 ])

let literal () = { positive = Random.State.bool rng; atom = atom () }
let clause () = List.init (Random.State.int rng 4) (fun _ -> literal ())

(* Rebuild every node, so equal keys are never physically shared. *)
let rec copy_term = function
  | V (a, b) -> V (a + 0, b + 0)
  | Fn (Original s, ts) ->
      Fn (Original (String.init (String.length s) (String.get s)), List.map copy_term ts)
  | Fn (Skolem (a, b), ts) -> Fn (Skolem (a, b), List.map copy_term ts)

let copy_atom = function
  | P (p, ts) -> P (String.init (String.length p) (String.get p), List.map copy_term ts)
  | E (s, t) -> E (copy_term s, copy_term t)
  | D ((a, b), ts) -> D ((a, b), List.map copy_term ts)

let copy_literal l = { positive = l.positive; atom = copy_atom l.atom }
let copy_clause = List.map copy_literal

let agree name ~gen ~copy ~equal ~hash =
  for _ = 1 to 2000 do
    let a = gen () and b = gen () in
    let a' = copy a in
    check (a' == a || equal a a') (name ^ ": a copy is not equal");
    check (hash a = hash a') (name ^ ": equal keys hash differently");
    check (hash a >= 0) (name ^ ": negative hash");
    check (equal a b = (compare a b = 0)) (name ^ ": equality disagrees with compare")
  done

(* The subsumption index without amortized removal, verbatim but for names: an eager list filter
   per removal. The reference for the differential test below. *)
module Eager = struct
  type node = { children : node Tbl.Feature.t; mutable terminal : step list }
  type t = { root : node; live : step Tbl.Int.t; mutable baseline : int; mutable candidates : int }

  let node () = { children = Tbl.Feature.create 4; terminal = [] }
  let create () = { root = node (); live = Tbl.Int.create 128; baseline = 0; candidates = 0 }
  let features = Subsumption_index.features
  let possible = Subsumption_index.possible
  let atom = Subsumption_index.atom

  let add t (s : step) =
    Tbl.Int.add t.live s.id s;
    let rec insert n = function
      | [] -> n.terminal <- s :: n.terminal
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
    insert t.root (features s.clause)

  let remove t id =
    match Tbl.Int.find_opt t.live id with
    | None -> ()
    | Some s ->
        Tbl.Int.remove t.live id;
        let rec erase n = function
          | [] -> n.terminal <- List.filter (fun (s : step) -> s.id <> id) n.terminal
          | key :: rest ->
              let child = Tbl.Feature.find n.children key in
              erase child rest;
              if child.terminal = [] && Tbl.Feature.length child.children = 0 then
                Tbl.Feature.remove n.children key
        in
        erase t.root (features s.clause)

  let collect t accept output =
    let result = List.filter accept !output |> List.sort (fun (a : step) b -> compare a.id b.id) in
    t.candidates <- t.candidates + List.length result;
    result

  let forward t clause =
    t.baseline <- t.baseline + Tbl.Int.length t.live;
    let output = ref [] in
    let rec visit n keys =
      output := List.rev_append n.terminal !output;
      let rec children = function
        | [] -> ()
        | k :: rest ->
            Option.iter (fun child -> visit child rest) (Tbl.Feature.find_opt n.children k);
            children rest
      in
      children keys
    in
    visit t.root (features clause);
    collect t (fun s -> possible s.clause clause) output

  let exists_forward t clause accept =
    let exception Found in
    t.baseline <- t.baseline + Tbl.Int.length t.live;
    let rec visit n keys =
      List.iter
        (fun (s : step) ->
          if possible s.clause clause then (
            t.candidates <- t.candidates + 1;
            if accept s then raise Found))
        n.terminal;
      let rec children = function
        | [] -> ()
        | k :: rest ->
            Option.iter (fun child -> visit child rest) (Tbl.Feature.find_opt n.children k);
            children rest
      in
      children keys
    in
    try
      visit t.root (features clause);
      false
    with Found -> true

  let resolution ?(budget = 256) t clause =
    let exception Exhausted in
    let left = ref budget and found = Tbl.Int.create 16 in
    let tick () =
      decr left;
      if !left < 0 then raise Exhausted
    in
    let keys = features clause in
    let feasible side =
      List.exists
        (fun p -> List.exists (fun t -> p.positive <> t.positive && atom p.atom t.atom) clause)
        side
      && List.for_all (fun p -> List.exists (fun t -> atom p.atom t.atom) clause) side
    in
    let rec visit n flipped pivot =
      if pivot then
        List.iter
          (fun s ->
            tick ();
            if feasible s.clause then Tbl.Int.replace found s.id s)
          n.terminal;
      Tbl.Feature.iter
        (fun key child ->
          tick ();
          (* Features are interned ints now: the opposite sign is [Clause.flip_feature]. *)
          let opposite = List.mem (Clause.flip_feature key) keys in
          if List.mem key keys then visit child flipped (pivot || opposite)
          else if (not flipped) && opposite then visit child true true)
        n.children
    in
    (try visit t.root false false with Exhausted -> ());
    Tbl.Int.fold (fun _ s xs -> s :: xs) found []
    |> List.sort (fun (a : step) b -> compare a.id b.id)

  let backward t clause =
    t.baseline <- t.baseline + Tbl.Int.length t.live;
    let output = ref [] in
    let rec visit n required =
      if required = [] then output := List.rev_append n.terminal !output;
      Tbl.Feature.iter
        (fun k child ->
          match required with
          | [] -> visit child []
          | first :: rest ->
              (* Stdlib.compare on the string keys the interned features replaced. *)
              let order = Clause.compare_feature k first in
              if order = 0 then visit child rest else if order < 0 then visit child required)
        n.children
    in
    visit t.root (features clause);
    collect t (fun s -> possible clause s.clause) output
end

let ids = List.map (fun (s : step) -> s.id)

(* The polymorphic implementations that the monomorphic tables replaced, verbatim but for names:
   the references of the equivalence tests below. *)
module Before = struct
  let normalize c =
    let c = List.sort_uniq compare c in
    let vars = Tbl.Pair.create 8 in
    let rename v =
      match Tbl.Pair.find_opt vars v with
      | Some i -> V (0, i)
      | None ->
          let i = Tbl.Pair.length vars in
          Tbl.Pair.add vars v i;
          V (0, i)
    in
    List.sort_uniq compare (List.map (Clause.map_literal (Clause.map_vars rename)) c)

  let key c =
    let counts = Tbl.Pair.create 8 in
    let rec visit = function
      | V v -> Tbl.Pair.replace counts v (1 + Option.value ~default:0 (Tbl.Pair.find_opt counts v))
      | Fn (_, ts) -> List.iter visit ts
    in
    let shape l =
      List.iter visit (Clause.atom_terms l.atom);
      let canonical l = List.hd (normalize [ l ]) in
      let normal = canonical l in
      match l.atom with
      | E (x, y) -> min normal (canonical { l with atom = E (y, x) })
      | _ -> normal
    in
    let shapes = List.map shape c |> List.sort compare in
    (shapes, Tbl.Pair.fold (fun _ n ns -> n :: ns) counts [] |> List.sort compare)

  let rec matches p t =
    match (p, t) with
    | V _, _ -> true
    | Fn (f, ps), Fn (g, ts) ->
        Sym.equal f g && List.length ps = List.length ts && List.for_all2 matches ps ts
    | _ -> false

  let atom p t =
    match (p, t) with
    | P (p, ps), P (q, ts) ->
        Sym.name p q && List.length ps = List.length ts && List.for_all2 matches ps ts
    | D (p, ps), D (q, ts) ->
        Sym.def p q && List.length ps = List.length ts && List.for_all2 matches ps ts
    | E (s, t), E (u, v) -> (matches s u && matches t v) || (matches s v && matches t u)
    | _ -> false

  let possible c d =
    List.for_all (fun p -> List.exists (fun t -> p.positive = t.positive && atom p.atom t.atom) d) c

  let feature_key l =
    ( l.positive,
      match l.atom with
      | P (s, ts) -> ("p:" ^ s, List.length ts)
      | D ((a, i), ts) -> (Printf.sprintf "d:%d:%d" a i, List.length ts)
      | E _ -> ("=", 2) )

  let features c = List.map feature_key c |> List.sort_uniq compare

  (* Tbl.Hash.feature on the string keys. *)
  let hash_feature ((positive, (name, arity)) : bool * (string * int)) =
    Tbl.Hash.(finish (mix (mix (mix seed (if positive then 17 else 19)) (String.hash name)) arity))
end

let sign x = if x < 0 then -1 else if x > 0 then 1 else 0

(* Shallower and more varied than [term]: arities 0-3 under one name, so equal heads with
   different arities and shared prefixes occur. *)
let rec wild depth =
  if depth = 0 || Random.State.int rng 4 = 0 then
    if Random.State.bool rng then V (Random.State.int rng 2, Random.State.int rng 3)
    else Fn (pick [ Original "a"; Original "ab"; Original ""; Skolem (2, 2); Skolem (0, 1) ], [])
  else Fn (pick symbols, List.init (Random.State.int rng 4) (fun _ -> wild (depth - 1)))

let wild_literal () =
  let atom =
    match Random.State.int rng 3 with
    | 0 -> P (pick [ "p"; "q"; "pq" ], List.init (Random.State.int rng 4) (fun _ -> wild 2))
    | 1 -> E (wild 2, wild 2)
    | _ ->
        D
          ( (Random.State.int rng 2, Random.State.int rng 2),
            List.init (Random.State.int rng 3) (fun _ -> wild 1) )
  in
  { positive = Random.State.bool rng; atom }

let wild_clause () = List.init (Random.State.int rng 5) (fun _ -> wild_literal ())

let tests =
  [
    ( "monomorphic Wire comparisons have the sign of Stdlib.compare",
      fun () ->
        for _ = 1 to 20000 do
          let a = wild_literal () and b = wild_literal () in
          let a' = copy_literal a in
          equal (sign (Clause.compare_literal a b)) (sign (compare a b)) "literal order differs";
          equal (Clause.compare_literal a a') 0 "a copy compares unequal";
          equal
            (sign (Clause.compare_atom a.atom b.atom))
            (sign (compare a.atom b.atom))
            "atom order differs";
          let s = wild 3 and t = wild 3 in
          equal (sign (Clause.compare_term s t)) (sign (compare s t)) "term order differs"
        done );
    ( "normalize, variant keys, features and the subsumption prefilter are unchanged",
      fun () ->
        for _ = 1 to 20000 do
          let c = wild_clause () and d = wild_clause () in
          equal (Clause.normalize c) (Before.normalize c) "normalize differs";
          equal (Variant_index.key c) (Before.key c) "variant key differs";
          equal
            (List.map Clause.key_view (Subsumption_index.features c))
            (Before.features c) "features differ";
          equal (Subsumption_index.possible c d) (Before.possible c d) "prefilter differs";
          let n = Clause.normalize d in
          equal (Subsumption_index.possible n d) (Before.possible n d) "prefilter differs"
        done );
    ( "term, atom, literal and clause keys agree with structural comparison",
      fun () ->
        agree "term"
          ~gen:(fun () -> term 4)
          ~copy:copy_term ~equal:Tbl.Equal.term ~hash:Tbl.Hash.term;
        agree "atom" ~gen:atom ~copy:copy_atom ~equal:Tbl.Equal.atom ~hash:Tbl.Hash.atom;
        agree "literal" ~gen:literal ~copy:copy_literal ~equal:Tbl.Equal.literal
          ~hash:Tbl.Hash.literal;
        agree "clause" ~gen:clause ~copy:copy_clause ~equal:Tbl.Equal.clause ~hash:Tbl.Hash.clause;
        agree "clause and support"
          ~gen:(fun () -> (clause (), List.init (Random.State.int rng 3) Fun.id))
          ~copy:(fun (c, xs) -> (copy_clause c, List.map (fun x -> x + 0) xs))
          ~equal:Tbl.Equal.clause_ints ~hash:Tbl.Hash.clause_ints;
        agree "head"
          ~gen:(fun () -> (pick symbols, Random.State.int rng 3))
          ~copy:(fun (f, n) -> (f, n))
          ~equal:Tbl.Equal.head ~hash:Tbl.Hash.head;
        agree "feature"
          ~gen:(fun () -> Clause.key (wild_literal ()))
          ~copy:(fun f -> f + 0)
          ~equal:Tbl.Equal.feature ~hash:Tbl.Hash.feature );
    ( "interned features hash, compare and equal as the string keys they replace",
      fun () ->
        for _ = 1 to 20000 do
          let a = wild_literal () and b = wild_literal () in
          let a' = copy_literal a in
          let fa = Clause.key a and fb = Clause.key b in
          equal (Clause.key_view fa) (Before.feature_key a) "feature view differs";
          equal (Clause.key a') fa "a copy has another feature";
          equal (Tbl.Hash.feature fa)
            (Before.hash_feature (Before.feature_key a))
            "feature hash differs";
          equal (Int.equal fa fb)
            (Before.feature_key a = Before.feature_key b)
            "feature equality differs";
          equal
            (sign (Clause.compare_feature fa fb))
            (sign (compare (Before.feature_key a) (Before.feature_key b)))
            "feature order differs";
          equal (Clause.flip_feature fa)
            (Clause.key { a with positive = not a.positive })
            "flipped feature differs"
        done );
    ( "definition features are encoded, not interned, and keep the string keys' hash and order",
      fun () ->
        let before = (Intern.state ()).count in
        let definition () =
          let a =
            match Random.State.int rng 3 with
            | 0 -> Random.State.int rng 3
            | 1 -> Random.State.int rng ((1 lsl 30) - 1)
            | _ -> (1 lsl 30) + Random.State.int rng 5 (* outside the encoding: interned *)
          in
          let i =
            if a < 1 lsl 30 && Random.State.int rng 4 = 0 then Random.State.int rng (1 lsl 20)
            else Random.State.int rng 4
          in
          {
            positive = Random.State.bool rng;
            atom = D ((a, i), List.init (Random.State.int rng 3) (fun _ -> V (0, 0)));
          }
        in
        let outside = ref 0 in
        for _ = 1 to 20000 do
          let a = definition ()
          and b = if Random.State.bool rng then definition () else wild_literal () in
          (match a.atom with D ((x, _), _) when x >= 1 lsl 30 -> incr outside | _ -> ());
          let fa = Clause.key a and fb = Clause.key b in
          equal (Clause.key_view fa) (Before.feature_key a) "definition view differs";
          equal (Clause.key (copy_literal a)) fa "a copied definition has another feature";
          equal (Tbl.Hash.feature fa)
            (Before.hash_feature (Before.feature_key a))
            "definition hash differs";
          equal (Int.equal fa fb)
            (Before.feature_key a = Before.feature_key b)
            "definition equality differs";
          equal
            (sign (Clause.compare_feature fa fb))
            (sign (compare (Before.feature_key a) (Before.feature_key b)))
            "definition order differs";
          equal (Clause.flip_feature fa)
            (Clause.key { a with positive = not a.positive })
            "flipped definition differs"
        done;
        check (!outside > 100) "too few definitions outside the encoding";
        (* Only the definitions outside the encoding (5 ids x 4 indices x 3 arities) and the
           predicates of [wild_literal] (3 names x 4 arities) can have been interned. *)
        check
          ((Intern.state ()).count - before <= (5 * 4 * 3) + 12)
          "encoded definitions were interned" );
    ( "canonical names and symbols",
      fun () ->
        let names = [ "f"; "g"; "ab"; ""; "multiply"; "inverse"; "c1"; "c2"; "c10" ] in
        for _ = 1 to 5000 do
          let s = pick names in
          let s' = String.init (String.length s) (String.get s) in
          check (Intern.name s == Intern.name s') "a name is not canonical";
          check (Intern.original s == Intern.original s') "a symbol is not canonical";
          (match Intern.original s with
          | Original n -> check (n == Intern.name s) "a symbol does not use the canonical name"
          | Skolem _ -> failwith "a canonical symbol is a Skolem");
          let r =
            String.init (Random.State.int rng 12) (fun _ -> Char.chr (97 + Random.State.int rng 3))
          in
          check (Sym.name s s') "equal names differ";
          check (Sym.equal (Original s) (Original s')) "equal symbols differ";
          equal (Sym.name s r) (String.equal s r) "name equality differs";
          equal (Sym.equal (Original s) (Original r)) (String.equal s r) "symbol equality differs"
        done;
        (* Clausification builds canonical symbols and names. *)
        let fresh s = String.init (String.length s) (String.get s) in
        let formula : Wire.source =
          All
            (Disj
               [
                 Pred ("p", [ App ("f", [ B 0 ]) ]);
                 Pred (fresh "p", [ App (fresh "f", [ App ("a", []) ]) ]);
               ])
        in
        let axiom : Wire.axiom = { axiom_id = 0; name = "ax"; origin = Fixed "ax"; formula } in
        match Clausify.run axiom with
        | [ [ { atom = P (p, [ Fn (f, _) ]); _ }; { atom = P (q, [ Fn (g, _) ]); _ } ] ] ->
            check (p == q) "clausified predicate names are not shared";
            check (f == g) "clausified symbols are not shared"
        | _ -> failwith "unexpected clausification" );
    ( "typed tables answer lookups exactly like a generic table",
      fun () ->
        let typed = Tbl.Clause.create 16 and generic = Hashtbl.create 16 in
        let keys = List.init 3000 (fun _ -> clause ()) in
        List.iteri
          (fun i c ->
            Tbl.Clause.replace typed c i;
            Hashtbl.replace generic c i)
          keys;
        equal (Tbl.Clause.length typed) (Hashtbl.length generic) "table sizes differ";
        List.iter
          (fun c ->
            let c = if Random.State.bool rng then copy_clause c else c in
            equal (Tbl.Clause.find_opt typed c) (Hashtbl.find_opt generic c) "lookup differs")
          (keys @ List.init 3000 (fun _ -> clause ()));
        List.iter
          (fun c ->
            Tbl.Clause.remove typed c;
            Hashtbl.remove generic c)
          (List.filteri (fun i _ -> i mod 3 = 0) keys);
        List.iter
          (fun c -> equal (Tbl.Clause.mem typed c) (Hashtbl.mem generic c) "membership differs")
          keys );
    ( "keys that share a long prefix do not share a bucket",
      fun () ->
        let prefix =
          List.init 3 (fun i -> positive (P ("p", [ Fn (Original "f", [ v i; v (i + 1) ]) ])))
        in
        let rec numeral n =
          if n = 0 then constant "z" else Fn (Original "s", [ numeral (n - 1) ])
        in
        let keys = List.init 2000 (fun n -> prefix @ [ negative (P ("q", [ numeral n ])) ]) in
        let typed = Tbl.Clause.create 16 and generic = Hashtbl.create 16 in
        List.iter
          (fun c ->
            Tbl.Clause.replace typed c ();
            Hashtbl.replace generic c ())
          keys;
        let longest = (Tbl.Clause.stats typed).max_bucket_length
        and generic_longest = (Hashtbl.stats generic).max_bucket_length in
        Printf.printf "    longest bucket: typed %d, Stdlib generic %d (2000 keys)\n%!" longest
          generic_longest;
        check (longest <= 16) (Printf.sprintf "typed clause table has a %d-key bucket" longest);
        let terms = Tbl.Term.create 16 in
        List.iter (fun n -> Tbl.Term.replace terms (numeral n) n) (List.init 2000 Fun.id);
        let longest = (Tbl.Term.stats terms).max_bucket_length in
        check (longest <= 16) (Printf.sprintf "typed term table has a %d-key bucket" longest) );
    ( "integer, pair and list keys",
      fun () ->
        equal (Tbl.Hash.int 12345) 12345 "integer keys are not their own hash";
        check (Tbl.Hash.int (-3) >= 0) "negative integer key has a negative hash";
        let pairs = Tbl.Pair.create 16 and lists = Tbl.Ints.create 16 in
        for i = 0 to 99 do
          for j = 0 to 9 do
            Tbl.Pair.replace pairs (i, j) (i + j);
            Tbl.Ints.replace lists [ i; j ] (i * j)
          done
        done;
        equal (Tbl.Pair.length pairs) 1000 "pair keys collided as equal";
        equal (Tbl.Pair.find pairs (Sys.opaque_identity (42, 7))) 49 "pair lookup";
        equal (Tbl.Ints.find lists (List.map (fun x -> x + 0) [ 42; 7 ])) 294 "list lookup";
        check (not (Tbl.Ints.mem lists [ 42 ])) "list prefix matched";
        check
          (Tbl.Equal.head_opt None None && not (Tbl.Equal.head_opt None (Some (Original "f", 0))))
          "optional heads" );
    ( "term arena interns structurally and keeps foreign handles apart",
      fun () ->
        let a = Term.create () and b = Term.create () in
        let t = Fn (Original "f", [ v 0; Fn (Original "g", [ constant "c" ]) ]) in
        let x = Term.of_wire a t and y = Term.of_wire a (copy_term t) in
        check (Term.equal x y) "equal terms got different handles";
        check (Term.to_wire a x == Term.to_wire a y) "wire cache did not share";
        equal (Term.to_wire a x) t "wire round trip";
        let z = Term.of_wire b t in
        check (not (Term.equal x z)) "handles of two arenas compare equal";
        check (rejects (fun () -> ignore (Term.view a z))) "foreign handle accepted";
        let before = Term.count a in
        ignore (Term.of_wire a (copy_term t));
        equal (Term.count a) before "re-interning added nodes" );
    ( "shared filter agrees with List.filter and keeps unchanged suffixes shared",
      fun () ->
        let rec suffix_shared xs ys =
          (* [ys] is physically a suffix of [xs] *)
          xs == ys || match xs with [] -> false | _ :: rest -> suffix_shared rest ys
        in
        for _ = 1 to 2000 do
          let xs = List.init (Random.State.int rng 40) (fun i -> i) in
          let drop = Random.State.int rng 5 in
          let keep x = drop = 0 || ((x * 7) + drop) mod (2 + drop) <> 0 in
          let calls = ref [] in
          let r =
            Shared.filter
              (fun x ->
                calls := x :: !calls;
                keep x)
              xs
          in
          equal r (List.filter keep xs) "shared filter changed the elements or their order";
          equal (List.rev !calls) xs "predicate not called exactly once per element in order";
          if List.for_all keep xs then check (r == xs) "nothing dropped but the list was copied";
          (* The longest all-kept suffix of the input is shared by the result. *)
          let rec tail_kept = function
            | [] -> []
            | _ :: rest as l -> if List.for_all keep l then l else tail_kept rest
          in
          check (suffix_shared r (tail_kept xs)) "all-kept suffix was copied"
        done;
        let long = List.init 1_000_000 (fun i -> i) in
        equal
          (List.length (Shared.filter (fun x -> x mod 3 <> 0) long))
          666_666 "long list (stack safety)" );
    ( "the queue filter keeps the rotating filter's elements, calls and order",
      fun () ->
        for _ = 1 to 3000 do
          let xs = List.init (Random.State.int rng 50) (fun i -> i) in
          let drop = Random.State.int rng 4 in
          let keep x = drop = 0 || ((x * 5) + drop) mod (3 + drop) <> 0 in
          let run filter =
            let q = Queue.create () and calls = ref [] in
            List.iter (fun x -> Queue.add x q) xs;
            filter
              (fun x ->
                calls := x :: !calls;
                keep x)
              q;
            Queue.add (-1) q;
            (List.of_seq (Queue.to_seq q), List.rev !calls)
          in
          equal (run Shared.filter_queue) (run Shared.filter_queue_rotate)
            "queue filter changed the elements, their order or the predicate calls"
        done );
    ( "reclaiming from pushed roots keeps the nodes the list of roots keeps",
      fun () ->
        for _ = 1 to 300 do
          (* A random proof DAG (parents have smaller ids) and a copy with the same ids. *)
          let p = Proof.create () and copy = Proof.create () in
          let n = 1 + Random.State.int rng 300 in
          for i = 0 to n - 1 do
            let seed = Random.State.int rng 1_000_000 in
            let rule =
              if i = 0 || seed mod 4 = 0 then Input (i, 0)
              else Resolve (seed mod i, 0, seed / 7 mod i, 0, [])
            in
            ignore (Proof.add p [] rule);
            ignore (Proof.add copy [] rule)
          done;
          let count = if Random.State.int rng 10 = 0 then 5000 else Random.State.int rng 20 in
          let roots = List.init count (fun _ -> Random.State.int rng n) in
          let a = Proof.reclaim_with p (fun push -> List.iter push roots)
          and b = Proof.reclaim_list copy roots in
          equal a b "reclaimed counts differ";
          equal
            (List.map (fun (s : step) -> s.id) (Proof.steps p))
            (List.map (fun (s : step) -> s.id) (Proof.steps copy))
            "reclaimed different nodes"
        done );
    ( "reclaiming refuses a node created during the sweep past its marks",
      fun () ->
        (* The marks are a bit set sized from the store's next id on entry. A node added while
           the roots are pushed lies past it: the checked accesses raise instead of marking
           outside the set. *)
        let p = Proof.create () in
        for i = 0 to 2 do
          ignore (Proof.add p [] (Input (i, 0)))
        done;
        check
          (rejects (fun () ->
               ignore
                 (Proof.reclaim_with p (fun push ->
                      for i = 0 to 15 do
                        push (Proof.add p [] (Input (i, 0))).id
                      done))))
          "a node created during the sweep was marked past the bit set";
        (* Within the bounds nothing changed: the three inputs as roots keep all three. *)
        let q = Proof.create () in
        for i = 0 to 2 do
          ignore (Proof.add q [] (Input (i, 0)))
        done;
        equal (Proof.reclaim_with q (fun push -> List.iter push [ 0; 1; 2 ])) 0 "a root was dropped"
    );
    ( "the heaps' monomorphic comparisons agree with the polymorphic ones",
      fun () ->
        let floats = [| 0.; -0.; 1.5; -2.; Float.nan; Float.infinity; Float.neg_infinity; 3. |] in
        for _ = 1 to 20000 do
          let i () = Random.State.int rng 5 - 2 in
          let f () = floats.(Random.State.int rng (Array.length floats)) in
          let x = (i (), i ()) and y = (i (), i ()) in
          equal (Passive.le x y) (x <= y) "pair order differs";
          let a = (i (), f (), i (), i ()) and b = (i (), f (), i (), i ()) in
          equal (Passive.ele a b) (compare a b <= 0) "entry order differs"
        done );
    ( "feature vectors never reject a subsumer",
      fun () ->
        (* Instances of a clause, with extra literals and in another literal order, are subsumed
           by it, so their vectors must be at least its vector; random pairs check every pair
           that subsumes. *)
        let table = Feature_vector.table () in
        let instance c =
          let sigma = Tbl.Pair.create 8 in
          let rec image = function
            | V v -> (
                match Tbl.Pair.find_opt sigma v with
                | Some t -> t
                | None ->
                    let t =
                      if Random.State.bool rng then V (3, Tbl.Pair.length sigma) else wild 2
                    in
                    Tbl.Pair.add sigma v t;
                    t)
            | Fn (f, ts) -> Fn (f, List.map image ts)
          in
          let d = List.map (Clause.map_literal image) c @ wild_clause () in
          List.sort (fun _ _ -> if Random.State.bool rng then 1 else -1) d
        in
        let subsumers = ref 0 in
        for _ = 1 to 20000 do
          let c = wild_clause () in
          let d = if Random.State.bool rng then instance c else wild_clause () in
          if Subsumption.subsumes ~budget:1000000 c d then (
            incr subsumers;
            check
              (Feature_vector.below (Feature_vector.vector table c) (Feature_vector.vector table d))
              "a subsumer's vector exceeds the subsumed clause's vector")
        done;
        check (!subsumers > 5000) "too few subsuming pairs" );
    ( "feature-vector index queries equal a linear scan over random adds and removals",
      fun () ->
        (* Small and large populations, many equal vectors (splits that cannot separate them),
           removal of whole subtrees and re-adds of removed items. *)
        List.iter
          (fun (population, rounds, generate) ->
            let table = Feature_vector.table () in
            let index = Feature_vector.create () in
            let vectors =
              Array.init population (fun _ -> Feature_vector.vector table (generate ()))
            in
            let entries = Array.make population None in
            let scan keep =
              List.filter_map
                (fun i ->
                  match entries.(i) with Some _ when keep vectors.(i) -> Some i | _ -> None)
                (List.init population Fun.id)
            in
            let answer query v =
              let found = ref [] in
              query index v (fun (e : int Feature_vector.entry) -> found := e.item :: !found);
              List.sort compare !found
            in
            for round = 1 to rounds do
              let i = Random.State.int rng population in
              (match entries.(i) with
              | Some e ->
                  Feature_vector.remove index e;
                  entries.(i) <- None
              | None -> entries.(i) <- Some (Feature_vector.add index i vectors.(i)));
              if round mod 5 = 0 then (
                let v = Feature_vector.vector table (generate ()) in
                equal (answer Feature_vector.forward v)
                  (scan (fun w -> Feature_vector.below w v))
                  "forward differs from the linear scan";
                equal
                  (answer Feature_vector.backward v)
                  (scan (fun w -> Feature_vector.below v w))
                  "backward differs from the linear scan";
                equal (Feature_vector.size index)
                  (Array.fold_left (fun n e -> if e = None then n else n + 1) 0 entries)
                  "live count")
            done;
            Array.iteri
              (fun i e ->
                match e with
                | Some e ->
                    Feature_vector.remove index e;
                    entries.(i) <- None
                | None -> ())
              entries;
            equal (Feature_vector.size index) 0 "entries left after removing all";
            equal index.nodes 1 "nodes left after removing all")
          [
            (60, 3000, wild_clause);
            (2000, 30000, wild_clause);
            (500, 8000, fun () -> [ literal () ]);
            (300, 6000, fun () -> [ { positive = true; atom = P ("p", [ V (0, 0) ]) } ]);
          ] );
    ( "an index without the resolution trie answers forward and backward queries alike",
      fun () ->
        let full = Subsumption_index.create ()
        and lean = Subsumption_index.create ~resolution:false () in
        let steps =
          Array.init 300 (fun id ->
              { id; clause = Clause.normalize (wild_clause ()); rule = Input (id, 0) })
        in
        let live = Array.make (Array.length steps) false in
        for round = 0 to 2999 do
          let i = Random.State.int rng (Array.length steps) in
          if live.(i) then (
            Subsumption_index.remove full i;
            Subsumption_index.remove lean i)
          else (
            Subsumption_index.add full steps.(i);
            Subsumption_index.add lean steps.(i));
          live.(i) <- not live.(i);
          if round mod 5 = 0 then (
            let q = Clause.normalize (wild_clause ()) in
            equal
              (ids (Subsumption_index.forward lean q))
              (ids (Subsumption_index.forward full q))
              "forward";
            equal
              (ids (Subsumption_index.backward lean q))
              (ids (Subsumption_index.backward full q))
              "backward")
        done;
        equal (Tbl.Feature.length lean.root.children) 0 "the trie-less index built a trie";
        check
          (match Subsumption_index.resolution lean [] with
          | exception Invalid_argument _ -> true
          | _ -> false)
          "resolution answered without its trie" );
    ( "existence-only forward subsumption query agrees with the candidate list",
      fun () ->
        let index = Subsumption_index.create () in
        let steps =
          List.init 120 (fun id ->
              let clause = List.init (1 + Random.State.int rng 3) (fun _ -> literal ()) in
              { id; clause; rule = Input (id, 0) })
        in
        List.iter (Subsumption_index.add index) steps;
        List.iter
          (fun (s : step) -> if s.id mod 5 = 0 then Subsumption_index.remove index s.id)
          steps;
        for round = 0 to 599 do
          let query = List.init (1 + Random.State.int rng 4) (fun _ -> literal ()) in
          let modulus = 1 + (round mod 7) in
          let accept (s : step) = s.id mod modulus = round mod modulus in
          let listed = List.exists accept (Subsumption_index.forward index query) in
          equal
            (Subsumption_index.exists_forward index query accept)
            listed "exists_forward disagrees with forward";
          equal
            (Subsumption_index.exists_forward index query (fun _ -> true))
            (Subsumption_index.forward index query <> [])
            "exists_forward misses a possible candidate"
        done );
    ( "subsumption index removal is amortized and queries match eager removal",
      fun () ->
        (* Few predicates, so many clauses share one trie node; ids are removed and the same
           steps added again, which a dead entry must not duplicate. The budgeted resolution query
           still walks the amortized trie and must equal the eager reference, including what its
           budget reaches. Forward and backward answers are the eager trie's candidates minus
           exactly those the feature vectors rule out, in the same (ascending id) order, and keep
           every clause that subsumes or is subsumed; exists_forward answers as the forward list.
           The baseline counter is unchanged; the candidate counter counts the answers. *)
        let index = Subsumption_index.create () and eager = Eager.create () in
        let steps =
          Array.init 400 (fun id ->
              let clause = List.init (1 + Random.State.int rng 2) (fun _ -> literal ()) in
              { id; clause = Clause.normalize clause; rule = Input (id, 0) })
        in
        let live = Array.make (Array.length steps) false in
        let query () =
          Clause.normalize (List.init (1 + Random.State.int rng 3) (fun _ -> literal ()))
        in
        let vector c = Feature_vector.vector index.symbols c in
        let candidates = ref 0 in
        for round = 0 to 2999 do
          let i = Random.State.int rng (Array.length steps) in
          if live.(i) then (
            Subsumption_index.remove index i;
            Eager.remove eager i;
            live.(i) <- false)
          else (
            Subsumption_index.add index steps.(i);
            Eager.add eager steps.(i);
            live.(i) <- true);
          if round mod 7 = 0 then (
            let q = query () in
            let v = vector q in
            let forward = Subsumption_index.forward index q
            and eager_forward = Eager.forward eager q in
            let expected =
              List.filter (fun (s : step) -> Feature_vector.below (vector s.clause) v) eager_forward
            in
            equal (ids forward) (ids expected) "forward";
            List.iter
              (fun (s : step) ->
                if Subsumption.subsumes ~budget:100000 s.clause q then
                  check (List.memq s forward) "forward lost a subsumer")
              eager_forward;
            let backward = Subsumption_index.backward index q
            and eager_backward = Eager.backward eager q in
            let expected =
              List.filter
                (fun (s : step) -> Feature_vector.below v (vector s.clause))
                eager_backward
            in
            equal (ids backward) (ids expected) "backward";
            List.iter
              (fun (s : step) ->
                if Subsumption.subsumes ~budget:100000 q s.clause then
                  check (List.memq s backward) "backward lost a subsumed clause")
              eager_backward;
            candidates := !candidates + List.length forward + List.length backward;
            let modulus = 2 + (round mod 5) in
            let accept (s : step) = s.id mod modulus = 0 in
            let calls = ref 0 in
            equal
              (Subsumption_index.exists_forward index q (fun s ->
                   incr calls;
                   accept s))
              (List.exists accept forward) "exists_forward";
            check (!calls <= List.length forward) "exists_forward tested a non-candidate";
            candidates := !candidates + !calls;
            let budget = 1 + Random.State.int rng 40 in
            equal
              (ids (Subsumption_index.resolution ~budget index q))
              (ids (Eager.resolution ~budget eager q))
              "budgeted resolution query";
            ignore (Eager.exists_forward eager q accept);
            equal index.baseline eager.baseline "baseline counter";
            equal index.candidates !candidates "candidate counter")
        done;
        (* A removed step added again appears once. *)
        let s = steps.(0) in
        if not live.(0) then Subsumption_index.add index s;
        Subsumption_index.remove index s.id;
        Subsumption_index.add index s;
        let q = s.clause in
        equal
          (List.length
             (List.filter (fun (x : step) -> x.id = s.id) (Subsumption_index.forward index q)))
          1 "a re-added step is listed twice";
        (* Mass removal from one shared node: the eager filter took quadratic time (about 10^9
           list cells here); the amortized index takes linear time. CPU time, generous bound. *)
        let n = 60_000 in
        let same id =
          {
            id;
            clause = [ { positive = true; atom = P ("p", [ V (0, 0) ]) } ];
            rule = Input (id, 0);
          }
        in
        let big = Subsumption_index.create () in
        let started = Sys.time () in
        for id = 0 to n - 1 do
          Subsumption_index.add big (same id)
        done;
        for id = 0 to n - 1 do
          Subsumption_index.remove big id
        done;
        let seconds = Sys.time () -. started in
        check (seconds < 2.)
          (Printf.sprintf "removing %d entries of one node took %.2f s" n seconds);
        equal (Subsumption_index.forward big (same 0).clause) [] "a removed entry was listed";
        equal (Tbl.Feature.length big.root.children) 0 "an emptied node was not pruned" );
    ( "the name-hash cache returns String.hash, also for copies and colliding slots",
      fun () ->
        (* Names of one shape (one length, the same first, middle and last byte) share a cache
           slot; copies are physically distinct. Every answer must be String.hash's, and the
           mixed hash of a term must equal the formula on String.hash. *)
        let names =
          List.init 300 (fun i -> Printf.sprintf "s%03dx" i)
          @ List.init 300 (fun i -> Printf.sprintf "%c%d" (Char.chr (97 + (i mod 26))) i)
          @ [ ""; "a"; "="; String.make 40 'q' ]
        in
        for _ = 1 to 20 do
          List.iter
            (fun s ->
              let s' = String.init (String.length s) (String.get s) in
              equal (Tbl.Hash.string_hash s) (String.hash s) "cached name hash";
              equal (Tbl.Hash.string_hash s') (String.hash s) "cached name hash of a copy";
              equal (Tbl.Hash.string 17 s) (Tbl.Hash.mix 17 (String.hash s)) "mixed name hash")
            names
        done;
        let rec plain h = function
          | V (a, b) -> Tbl.Hash.mix (Tbl.Hash.mix (Tbl.Hash.mix h 3) a) b
          | Fn (f, ts) ->
              let h =
                match f with
                | Original s -> Tbl.Hash.mix (Tbl.Hash.mix h 1) (String.hash s)
                | Skolem (a, b) -> Tbl.Hash.mix (Tbl.Hash.mix (Tbl.Hash.mix h 2) a) b
              in
              Tbl.Hash.mix (List.fold_left plain h ts) 5
        in
        for _ = 1 to 5000 do
          let t = term 4 in
          equal (Tbl.Hash.term t) (Tbl.Hash.finish (plain Tbl.Hash.seed t)) "term hash";
          equal (Tbl.Hash.term (copy_term t)) (Tbl.Hash.term t) "term hash of a copy"
        done );
    ( "head codes and integer fingerprints agree with symbol equality and the cell rules",
      fun () ->
        let heads =
          [ (Original "f", 2); (Original "f", 1); (Original "g", 1); (Original "a", 0) ]
          @ [
              (Skolem (0, 1), 2); (Skolem (1, 0), 2); (Skolem (2, 2), 0); (Skolem (1 lsl 26, 3), 1);
            ]
        in
        let copy (f, n) =
          ( (match f with
            | Original s -> Original (String.init (String.length s) (String.get s))
            | k -> k),
            n )
        in
        List.iter
          (fun (f, n) ->
            List.iter
              (fun (g, m) ->
                let same = Sym.equal f g && n = m in
                equal (Intern.head_code f n = Intern.head_code g m) same "head code equality";
                let g, m = copy (g, m) in
                equal (Intern.head_code f n = Intern.head_code g m) same "head code of a copy";
                check (Intern.head_code f n >= 0) "negative head code")
              heads)
          heads;
        (* The cell semantics of the variant fingerprint this replaces. *)
        let module Old = struct
          type cell = Variable | Below | Absent | Head of symbol * int

          let rec at term = function
            | [] -> ( match term with V _ -> Variable | Fn (s, ts) -> Head (s, List.length ts))
            | i :: path -> (
                match term with
                | V _ -> Below
                | Fn (_, ts) -> (
                    match List.nth_opt ts i with None -> Absent | Some t -> at t path))

          let term t = Array.map (at t) [| []; [ 0 ]; [ 1 ]; [ 0; 0 ] |]

          let cell a b =
            match (a, b) with
            | Below, _ | _, Below -> true
            | Absent, Absent -> true
            | Absent, _ | _, Absent -> false
            | Variable, _ | _, Variable -> true
            | Head (f, n), Head (g, m) -> Sym.equal f g && n = m

          let compatible ?(reverse = false) a b =
            let rec loop i =
              i = 4 || (cell a.(i) b.(if reverse then i lxor 1 else i) && loop (i + 1))
            in
            loop 0
        end in
        let yes = ref 0 in
        for _ = 1 to 20000 do
          let s = term 3 and t = term 3 in
          let t = if Random.State.int rng 3 = 0 then copy_term s else t in
          List.iter
            (fun reverse ->
              let expected = Old.compatible ~reverse (Old.term s) (Old.term t) in
              if expected then incr yes;
              equal
                (Index.Fingerprint.compatible ~reverse (Index.Fingerprint.term s)
                   (Index.Fingerprint.term t))
                expected "integer fingerprints disagree with the cell rules")
            [ false; true ]
        done;
        check (!yes > 2000 && !yes < 38000) "fingerprint fixture too uniform" );
    ( "literal prints never change the subsumption prefilter's answer",
      fun () ->
        (* Pairs (c, d) where d is often an instance of c, possibly with literals shuffled in and
           equations turned around, so that both answers occur. *)
        let instance c =
          let sigma =
            List.init 3 (fun i -> ((0, i), term 2)) @ List.init 3 (fun i -> ((1, i), term 2))
          in
          let rec apply = function
            | V v -> ( match List.assoc_opt v sigma with Some t -> t | None -> V v)
            | Fn (f, ts) -> Fn (f, List.map apply ts)
          in
          let flip = function E (s, t) when Random.State.bool rng -> E (t, s) | a -> a in
          let lit (l : literal) = { l with atom = flip (Clause.map_atom apply l.atom) } in
          let extra = if Random.State.bool rng then [ literal () ] else [] in
          List.map lit c @ extra
        in
        let yes = ref 0 and n = ref 0 and masked = ref 0 in
        let mask c = Subsumption_index.mask c (Subsumption_index.prints c) in
        for _ = 1 to 30000 do
          let c = clause () in
          let d = if Random.State.int rng 3 = 0 then clause () else instance c in
          List.iter
            (fun (c, d) ->
              let expected = Subsumption_index.possible c d in
              if expected then incr yes;
              incr n;
              (* The head mask is a necessary condition of the prefilter. *)
              if not (Subsumption_index.masked (mask c) (mask d)) then (
                check (not expected) "the head mask rejects a possible pair";
                incr masked);
              equal
                (Subsumption_index.possible_prints (Subsumption_index.prints c) c
                   (Subsumption_index.prints d) d)
                expected "the printed prefilter differs";
              equal
                (Subsumption_index.possible_prints (Subsumption_index.prints c) (copy_clause c)
                   (Subsumption_index.prints (copy_clause d))
                   d)
                expected "the printed prefilter differs on copies")
            [ (c, d); (d, c) ]
        done;
        check (!yes > 5000 && !yes < !n - 5000) "prefilter fixture too uniform";
        check (!masked > 1000) "the head mask rejected too few pairs" );
    ( "the Wire KBO equals the tree KBO under the standard, installed and E-style orders",
      fun () ->
        let installed weights =
          let o = Ordering.create () in
          Ordering.install o ~weights (List.init 20 (fun _ -> clause ()));
          o
        in
        let table unified =
          let tbl = Hashtbl.create 16 in
          List.iter
            (fun (key, rank, w) -> Hashtbl.replace tbl key (rank, w))
            [
              ((Ordering.Function (Original "f"), 2), 3, 2);
              ((Ordering.Function (Original "g"), 1), max_int, 0);
              ((Ordering.Function (Original "h"), 1), 1, 1);
              ((Ordering.Function (Skolem (0, 1)), 2), 5, 3);
              ((Ordering.Function (Original "a"), 0), 0, 1);
              ((Ordering.Predicate "p", 1), 2, 1);
            ];
          (* Many more symbols than the order's symbol cache has slots, so that lookups of two
             symbols of one comparison share a slot. *)
          for k = 0 to 599 do
            Hashtbl.replace tbl
              (Ordering.Function (Original (Printf.sprintf "c%d" k)), 0)
              (k mod 97, 1)
          done;
          let o = Ordering.create () in
          Ordering.install_table ~unified o tbl;
          o
        in
        let many = List.init 600 (fun k -> Fn (Original (Printf.sprintf "c%d" k), [])) in
        let rec term_many depth =
          if depth = 0 || Random.State.int rng 3 = 0 then
            if Random.State.int rng 4 = 0 then V (0, Random.State.int rng 3) else pick many
          else
            Fn
              (pick symbols, List.init (1 + Random.State.int rng 2) (fun _ -> term_many (depth - 1)))
        in
        (* The tree KBO before the monomorphic helpers: polymorphic equality, hash-table variable
           counts and table lookups per symbol. *)
        let module Old = struct
          open Ordering

          let counts t =
            let result = Tbl.Pair.create 8 in
            let rec visit = function
              | Var v ->
                  Tbl.Pair.replace result v
                    (1 + Option.value ~default:0 (Tbl.Pair.find_opt result v))
              | App (_, ts) -> List.iter visit ts
            in
            visit t;
            result

          let dominates_variables s t =
            let sc = counts s and tc = counts t in
            Tbl.Pair.fold
              (fun v n ok -> ok && Option.value ~default:0 (Tbl.Pair.find_opt sc v) >= n)
              tc true

          let rec unary_chain_over s x =
            match s with
            | App (_, [ Var y ]) -> y = x
            | App (_, [ u ]) -> unary_chain_over u x
            | _ -> false

          let rec kbo order s t =
            s <> t && dominates_variables s t
            &&
            let ws = weight order s and wt = weight order t in
            ws > wt
            || ws = wt
               &&
               match (s, t) with
               | App _, Var x -> unary_chain_over s x
               | App (f, xs), App (g, ys) ->
                   let p = compare_heads order (f, List.length xs) (g, List.length ys) in
                   p > 0 || (p = 0 && lex order xs ys)
               | _ -> false

          and lex order xs ys =
            match (xs, ys) with
            | x :: xs, y :: ys -> if x = y then lex order xs ys else kbo order x y
            | _ -> false
        end in
        let literal_trees (l : literal) =
          let ts =
            match l.atom with
            | E (s, t) -> [ Ordering.of_term s; Ordering.of_term t ]
            | P (p, ts) ->
                [
                  Ordering.App (Ordering.Predicate p, List.map Ordering.of_term ts);
                  Ordering.App (Ordering.Truth, []);
                ]
            | D (p, ts) ->
                [
                  Ordering.App (Ordering.Definition p, List.map Ordering.of_term ts);
                  Ordering.App (Ordering.Truth, []);
                ]
          in
          if l.positive then ts else ts @ ts
        in
        let rec subterms t =
          t :: (match t with V _ -> [] | Fn (_, ts) -> List.concat_map subterms ts)
        in
        let checked = ref 0 and yes = ref 0 in
        List.iter
          (fun order ->
            for n = 1 to 5000 do
              let s = if n mod 2 = 0 then term 4 else term_many 3 in
              let t =
                match Random.State.int rng 4 with
                | 0 -> copy_term s
                | 1 -> pick (subterms s)
                | _ -> if n mod 2 = 0 then term 4 else term_many 3
              in
              (let l = literal () and m = literal () in
               List.iter
                 (fun (a, b) ->
                   List.iter
                     (fun x ->
                       List.iter
                         (fun y ->
                           equal (Ordering.greater_tree order x y) (Old.kbo order x y)
                             "the tree KBO differs on literal terms")
                         (literal_trees b))
                     (literal_trees a))
                 [ (l, m); (m, l); (l, l) ]);
              List.iter
                (fun (s, t) ->
                  let expected = Old.kbo order (Ordering.of_term s) (Ordering.of_term t) in
                  equal
                    (Ordering.greater_tree order (Ordering.of_term s) (Ordering.of_term t))
                    expected "the tree KBO differs from the old tree KBO";
                  equal (Ordering.greater ~order s t) expected "the Wire KBO differs";
                  equal
                    (Ordering.greater ~order (copy_term s) (copy_term t))
                    expected "the Wire KBO differs on copies";
                  incr checked;
                  if expected then incr yes)
                [ (s, t); (t, s) ]
            done)
          [ Ordering.standard; installed true; installed false; table true; table false ];
        check (!yes > 2000 && !yes < !checked - 2000) "KBO fixture too uniform";
        (* Pairs of the table's constants: equal weights, so the precedence decides, from two
           lookups that often share a cache slot. *)
        List.iter
          (fun order ->
            for _ = 1 to 20000 do
              let s = pick many and t = pick many in
              let expected = Old.kbo order (Ordering.of_term s) (Ordering.of_term t) in
              equal (Ordering.greater ~order s t) expected "the Wire KBO's precedence differs";
              equal
                (Ordering.greater_tree order (Ordering.of_term s) (Ordering.of_term t))
                expected "the tree KBO's precedence differs"
            done)
          [ table true; table false ] );
  ]

let () = run tests
