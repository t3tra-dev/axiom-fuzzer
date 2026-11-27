open Wire

(** Congruence closure proposes explanations using only existing unit equalities. Replay expands
    each explanation into ordinary ground paramodulation and resolution. Neither union-find nor the
    explanation graph is trusted. *)
type reason = Equality of step | Congruence of term list * term list

type edge = { number : int; left : term; right : term; reason : reason }

(* How a conflict is explained (Engine.config.ground_explanation).
   - [Forest]: along the union-find forest, each congruence edge expanded into explanations of its
     arguments along the forest again, every step a rewrite of the conflicting unit itself. The
     forest path is unique, so nested congruences repeat the same sub-explanations at every
     position, and the chain can grow exponentially in the nesting (TOP050-1 on s4d: 101,418
     rewrite steps of one 62-constant goal, 241.8 MB).
   - [Short]: a final conflict (the negative unit and every ground unit of the closure have an
     empty AVATAR support, so the refutation ends the search) whose forest explanation is longer
     than [short_threshold] steps is explained by [cheapest] instead: along the cheapest paths over
     every unit equation (also those the forest skipped because their sides were already merged)
     and the forest's congruence edges, with sharing: a pair of terms whose path has a unit
     equation and more than one edge is derived once as a unit lemma, and each use of the pair is
     one rewrite with it (s4d's TOP050-1: 1,282 steps, 0.42 MB); a path search that would pass
     its work bound ([short_work_base]) keeps the forest explanation. Until such a conflict the
     closure runs the forest code with the same guard calls and an allocation-free finality test,
     and the search ends at that conflict: only the certificate changes.
   The forest explanation is one of the candidates (its edges are in the graph, and a congruence
   edge costs at most its forest expansion), and sharing never adds a step, so the cheapest
   explanation is never longer; if its unshared cost were, the forest one is used. *)
type explanation = Forest | Short

let explanation_of_string = function
  | "forest" -> Forest
  | "short" -> Short
  | _ -> invalid_arg "ground explanation must be forest or short"

(* Final conflicts whose forest explanation has at most this many rewrite steps keep it (64; tests
   lower it to exercise small explanations). *)
let short_threshold = ref 64

(* The path search of one [cheapest] call (Dijkstra's pops and edge relaxations, counted, not
   timed, so the choice is deterministic) may do at most [short_work_base + short_work_per_step x
   (forest steps)] of them before the costs are known; past that the forest explanation is kept
   (counted in [fallbacks]). A forest explanation of a few dozen steps over a large graph of unit
   equations is not worth seconds of search: TOP050-1 on [b07c] (on E's loop) has an
   82-step forest explanation over 3,783 ground units, and its cheapest costs took 30.7 million
   relaxations (7 s) to save 10 steps; s4d's 74,124-step explanation needs 0.7 million and
   h047b31's 21,357-step one 6.4 million. Tests lower the bound to exercise the fallback. *)
let short_work_base = ref 1_000_000
let short_work_per_step = ref 1_000

type statistics = {
  mutable runs : int;
  mutable merges : int;
  mutable conflicts : int;
  mutable explanations : int;
  mutable shortened : int;  (** final conflicts explained by [cheapest] *)
  mutable saved : int;  (** forest explanation steps that those did not record *)
  mutable fallbacks : int;  (** cheapest explanations abandoned for the forest one *)
}

(* Congruence signatures: a symbol and the representatives of its arguments. *)
module Signatures = Hashtbl.Make (struct
  type t = symbol * int list

  let equal (f, xs) (g, ys) = Sym.equal f g && Tbl.Equal.ints xs ys
  let hash (f, xs) = Tbl.Hash.(finish (List.fold_left mix (symbol seed f) xs))
end)

(* Predicate atoms up to congruence: head and argument representatives. *)
module Positives = Hashtbl.Make (struct
  type t = [ `P of string | `D of int * int ] * int list

  let equal ((p, xs) : t) ((q, ys) : t) =
    (match (p, q) with `P p, `P q -> Sym.name p q | `D d, `D e -> Sym.def d e | _ -> false)
    && Tbl.Equal.ints xs ys

  let hash ((p, xs) : t) =
    let open Tbl.Hash in
    let h =
      match p with `P p -> string (mix seed 7) p | `D (a, b) -> mix (mix (mix seed 13) a) b
    in
    finish (List.fold_left mix h xs)
end)

let statistics () =
  { runs = 0; merges = 0; conflicts = 0; explanations = 0; shortened = 0; saved = 0; fallbacks = 0 }

let rec ground = function V _ -> false | Fn (_, ts) -> List.for_all ground ts

let unit (s : step) =
  match s.clause with
  | [ l ] when List.for_all ground (Clause.atom_terms l.atom) -> Some l
  | _ -> None

(* Whether a unit holds without branch assumptions. Allocation-free on the conflict path. *)
let unconditional (avatar : Avatar.t) (s : step) =
  match Tbl.Int.find avatar.entries s.id with
  | entry -> entry.support = []
  | exception Not_found -> false

let rec all_unconditional avatar = function
  | [] -> true
  | (s, _) :: rest -> unconditional avatar s && all_unconditional avatar rest

(* A conflict of [s] in [units] ends the search: every premise any explanation can use and [s]
   itself are unconditional. *)
let final avatar s units = unconditional avatar s && all_unconditional avatar units

(* Explanation costs saturate here instead of overflowing. *)
let infinite = max_int / 4
let add a b = if a >= infinite - b then infinite else a + b

module Queue_set = Set.Make (struct
  type t = int * int

  let compare (a, b) (c, d) = if a <> c then Int.compare a c else Int.compare b d
end)

(* The [Short] explanation of the negative unit [s] at each [(position, source, destination)] of
   a final conflict: [forest] is the forest explanation (the fallback), [path] the forest path
   search, [ids] and [terms] the interned terms and [graph] the forest edges by term. *)
let cheapest stats ~guard ~record ~units ~ids ~terms ~graph ~path ~next ~forest s pairs =
  (* The forest explanation's length without recording it. The forest path for a bound is unique,
     so the result is memoized by its terms and bound. *)
  let forest_memo = Hashtbl.create 64 in
  let rec forest_size bound source target =
    if Tbl.Equal.term source target then 0
    else
      let key = (Tbl.Term.find ids source, Tbl.Term.find ids target, bound) in
      match Hashtbl.find_opt forest_memo key with
      | Some n -> n
      | None ->
          let n =
            List.fold_left
              (fun n (left, _, edge) ->
                guard ();
                match edge.reason with
                | Equality _ -> add n 1
                | Congruence (xs, ys) ->
                    let xs, ys = if left = edge.left then (xs, ys) else (ys, xs) in
                    List.fold_left2 (fun n x y -> add n (forest_size edge.number x y)) n xs ys)
              0 (path bound source target)
          in
          Hashtbl.add forest_memo key n;
          n
  in
  let steps = List.fold_left (fun n (_, x, y) -> add n (forest_size next x y)) 0 pairs in
  if steps <= !short_threshold then forest ()
  else
    let exception Over_budget in
    let budget =
      let per_step = max 0 !short_work_per_step in
      add (max 0 !short_work_base)
        (if per_step > 0 && steps >= infinite / per_step then infinite else per_step * steps)
    in
    (* The bound applies until the costs are known, before anything is recorded; the rewriting
       that follows repeats searches whose cost the recorded steps bound. *)
    let work = ref 0 and bounded = ref true in
    let spend () =
      incr work;
      if !bounded && !work > budget then raise_notrace Over_budget
    in
    (* The explanation graph by interned term id: every unit equation, also those the forest
       skipped, and the forest's congruence edges (each once, in the order of its number). *)
    let adjacency = Array.make (Array.length terms) [] in
    let connect edge =
      let a = Tbl.Term.find ids edge.left and b = Tbl.Term.find ids edge.right in
      adjacency.(a) <- (b, edge) :: adjacency.(a);
      adjacency.(b) <- (a, edge) :: adjacency.(b)
    in
    List.iter
      (fun (s, l) ->
        guard ();
        match (l.positive, l.atom) with
        | true, E (a, b) when not (Tbl.Equal.term a b) ->
            connect { number = -1; left = a; right = b; reason = Equality s }
        | _ -> ())
      units;
    Tbl.Term.fold
      (fun _ edges acc ->
        List.fold_left
          (fun acc edge -> match edge.reason with Congruence _ -> edge :: acc | Equality _ -> acc)
          acc edges)
      graph []
    |> List.sort_uniq (fun a b -> Int.compare a.number b.number)
    |> List.iter connect;
    let adjacency = Array.map List.rev adjacency in
    (* A unit equation costs one rewrite; a congruence edge costs the cheapest explanations of its
       argument pairs with the congruence edges older than it (their sides were merged by those,
       so the recursion ends), memoized per edge. [search bound x y] is Dijkstra's algorithm from
       x, ties broken by cost and then term id, so the path it returns is the one whose cost
       [distance] reports. *)
    let costs = Hashtbl.create 64 in
    let rec congruence_cost edge =
      match Hashtbl.find_opt costs edge.number with
      | Some c -> c
      | None ->
          let xs, ys = match edge.reason with Congruence (xs, ys) -> (xs, ys) | _ -> ([], []) in
          let c =
            List.fold_left2
              (fun c x y -> if c >= infinite then c else add c (distance edge.number x y))
              0 xs ys
          in
          Hashtbl.add costs edge.number c;
          c
    and distance bound x y = if Tbl.Equal.term x y then 0 else fst (search bound x y)
    and search bound x y =
      let source = Tbl.Term.find ids x and goal = Tbl.Term.find ids y in
      let best = Hashtbl.create 64 and previous = Hashtbl.create 64 in
      Hashtbl.replace best source 0;
      let queue = ref (Queue_set.singleton (0, source)) and reached = ref false in
      while (not !reached) && not (Queue_set.is_empty !queue) do
        guard ();
        let ((d, u) as top) = Queue_set.min_elt !queue in
        spend ();
        queue := Queue_set.remove top !queue;
        if u = goal then reached := true
        else if d <= Hashtbl.find best u then
          List.iter
            (fun (v, edge) ->
              spend ();
              let weight =
                match edge.reason with
                | Equality _ -> 1
                | Congruence _ -> if edge.number < bound then congruence_cost edge else infinite
              in
              if weight < infinite then
                let c = add d weight in
                match Hashtbl.find_opt best v with
                | Some old when old <= c -> ()
                | _ ->
                    Hashtbl.replace best v c;
                    Hashtbl.replace previous v (u, edge);
                    queue := Queue_set.add (c, v) !queue)
            adjacency.(u)
      done;
      if not !reached then (infinite, [])
      else
        let rec collect v acc =
          if v = source then acc
          else
            let u, edge = Hashtbl.find previous v in
            collect u ((terms.(u), terms.(v), edge) :: acc)
        in
        (Hashtbl.find best goal, collect goal [])
    in
    (* Rewriting with sharing. A pair whose cheapest path is one unit equation is one step with
       that premise; a path of congruence edges only rewrites the argument pairs in place; any
       other path is derived once as a unit lemma [x = y] (from the path's first unit equation,
       rewritten on both sides along the path), and every use of the pair is then one step with
       the lemma. The lemmas are small unit clauses, so a large target is rewritten once per pair
       instead of once per step of the pair's explanation, and a pair needed at many positions is
       explained once (the forest repeats it at every position). *)
    let lemmas = Hashtbl.create 64 in
    let side_of literal term =
      match literal.atom with
      | E (l, _) when Tbl.Equal.term l term -> 0
      | E (_, r) when Tbl.Equal.term r term -> 1
      | _ -> invalid_arg "ground explanation mismatch"
    in
    let rec rewrite bound target position source destination =
      if Tbl.Equal.term source destination then target
      else
        match snd (search bound source destination) with
        | [] -> invalid_arg "ground explanation has no path"
        | [ (left, right, edge) ] -> traverse target position left right edge
        | path
          when List.exists
                 (fun (_, _, e) -> match e.reason with Equality _ -> true | _ -> false)
                 path ->
            let lemma = derive source destination path in
            let literal = List.hd target.clause and own = List.hd lemma.clause in
            if Clause.at literal position <> source then invalid_arg "ground explanation mismatch";
            stats.explanations <- stats.explanations + 1;
            record
              [ Clause.put literal position destination ]
              (Paramodulate (lemma.id, 0, side_of own source = 1, target.id, 0, position, []))
        | path ->
            List.fold_left
              (fun target (left, right, edge) -> traverse target position left right edge)
              target path
    (* One edge of a path at [position] of the unit [target]: [left] becomes [right]. *)
    and traverse target position left right edge =
      guard ();
      match edge.reason with
      | Equality premise ->
          let reverse = left <> edge.left in
          let literal = List.hd target.clause in
          if Clause.at literal position <> left then invalid_arg "ground explanation mismatch";
          stats.explanations <- stats.explanations + 1;
          record
            [ Clause.put literal position right ]
            (Paramodulate (premise.id, 0, reverse, target.id, 0, position, []))
      | Congruence (xs, ys) ->
          let xs, ys = if left = edge.left then (xs, ys) else (ys, xs) in
          List.fold_left
            (fun target (i, (x, y)) -> rewrite edge.number target (position @ [ i ]) x y)
            target
            (List.mapi (fun i pair -> (i, pair)) (List.combine xs ys))
    (* The unit lemma [x = y] (either orientation) for a path with a unit equation, derived once
       per pair; the recursion into a congruence edge's arguments uses older edges only. *)
    and derive x y path =
      let key = (Tbl.Term.find ids x, Tbl.Term.find ids y) in
      match Hashtbl.find_opt lemmas key with
      | Some lemma -> lemma
      | None ->
          let edges = Array.of_list path in
          let rec first j =
            match edges.(j) with _, _, { reason = Equality _; _ } -> j | _ -> first (j + 1)
          in
          let j = first 0 in
          let uj, start =
            match edges.(j) with
            | uj, _, { reason = Equality premise; _ } -> (uj, premise)
            | _ -> assert false
          in
          let back = side_of (List.hd start.clause) uj in
          let forward = 1 - back in
          let lemma = ref start in
          for i = j - 1 downto 0 do
            let ui, ui1, edge = edges.(i) in
            lemma := traverse !lemma [ back ] ui1 ui edge
          done;
          for i = j + 1 to Array.length edges - 1 do
            let ui, ui1, edge = edges.(i) in
            lemma := traverse !lemma [ forward ] ui ui1 edge
          done;
          Hashtbl.replace lemmas key !lemma;
          Hashtbl.replace lemmas (snd key, fst key) !lemma;
          !lemma
    in
    (* The cheapest paths' cost without sharing bounds the steps recorded with sharing. *)
    match List.fold_left (fun n (_, x, y) -> add n (distance next x y)) 0 pairs with
    | exception Over_budget ->
        stats.fallbacks <- stats.fallbacks + 1;
        forest ()
    | cost when cost > steps -> forest ()
    | _ -> (
        bounded := false;
        let before = stats.explanations in
        match
          List.fold_left (fun target (position, x, y) -> rewrite next target position x y) s pairs
        with
        | target ->
            stats.shortened <- stats.shortened + 1;
            stats.saved <- stats.saved + max 0 (steps - (stats.explanations - before));
            target
        | exception Invalid_argument _ ->
            (* An internal mismatch of the cheapest path (none is known): the forest explanation
             still refutes; the nodes recorded so far stay unreferenced. *)
            stats.fallbacks <- stats.fallbacks + 1;
            forest ())

let close stats ~guard ~record ~conflict ~explanation ~avatar units =
  let ids = Tbl.Term.create 128 and terms = ref [] in
  let rec intern t =
    guard ();
    if not (Tbl.Term.mem ids t) then (
      (match t with Fn (_, ts) -> List.iter intern ts | V _ -> assert false);
      let id = Tbl.Term.length ids in
      Tbl.Term.add ids t id;
      terms := t :: !terms)
  in
  List.iter (fun (_, l) -> List.iter intern (Clause.atom_terms l.atom)) units;
  let terms = Array.of_list (List.rev !terms) in
  let parents = Array.init (Array.length terms) Fun.id in
  let rec root i =
    if parents.(i) = i then i
    else
      let r = root parents.(i) in
      parents.(i) <- r;
      r
  in
  let representative t = root (Tbl.Term.find ids t) in
  let graph = Tbl.Term.create 128 and next = ref 0 in
  let merge left right reason =
    guard ();
    let a = representative left and b = representative right in
    if a = b then false
    else (
      parents.(max a b) <- min a b;
      let edge = { number = !next; left; right; reason } in
      incr next;
      List.iter
        (fun t ->
          Tbl.Term.replace graph t (edge :: Option.value ~default:[] (Tbl.Term.find_opt graph t)))
        [ left; right ];
      stats.merges <- stats.merges + 1;
      true)
  in
  List.iter
    (fun (s, l) ->
      match (l.positive, l.atom) with true, E (a, b) -> ignore (merge a b (Equality s)) | _ -> ())
    units;
  let changed = ref true in
  while !changed do
    changed := false;
    let signatures = Signatures.create 128 in
    Array.iter
      (fun t ->
        guard ();
        match t with
        | V _ -> assert false
        | Fn (f, args) -> (
            let signature = (f, List.map representative args) in
            match Signatures.find_opt signatures signature with
            | None -> Signatures.add signatures signature t
            | Some other ->
                let other_args = match other with Fn (_, xs) -> xs | _ -> assert false in
                if merge t other (Congruence (args, other_args)) then changed := true))
      terms
  done;
  let path bound source target =
    let queue = Queue.create () and visited = Tbl.Term.create 32 in
    Queue.add source queue;
    Tbl.Term.add visited source None;
    while (not (Tbl.Term.mem visited target)) && not (Queue.is_empty queue) do
      guard ();
      let t = Queue.take queue in
      List.iter
        (fun edge ->
          let next = if edge.left = t then edge.right else edge.left in
          if edge.number < bound && not (Tbl.Term.mem visited next) then (
            Tbl.Term.add visited next (Some (t, edge));
            Queue.add next queue))
        (Option.value ~default:[] (Tbl.Term.find_opt graph t))
    done;
    let rec collect t acc =
      if t = source then acc
      else
        match Tbl.Term.find_opt visited t with
        | Some (Some (previous, edge)) -> collect previous ((previous, t, edge) :: acc)
        | _ -> invalid_arg "ground explanation has no path"
    in
    collect target []
  in
  let rec rewrite bound target position source destination =
    List.fold_left
      (fun target (left, right, edge) ->
        guard ();
        match edge.reason with
        | Equality premise ->
            let reverse = left <> edge.left in
            let literal = List.hd target.clause in
            if Clause.at literal position <> left then invalid_arg "ground explanation mismatch";
            stats.explanations <- stats.explanations + 1;
            record
              [ Clause.put literal position right ]
              (Paramodulate (premise.id, 0, reverse, target.id, 0, position, []))
        | Congruence (xs, ys) ->
            let xs, ys = if left = edge.left then (xs, ys) else (ys, xs) in
            List.fold_left
              (fun target (i, (x, y)) -> rewrite edge.number target (position @ [ i ]) x y)
              target
              (List.mapi (fun i pair -> (i, pair)) (List.combine xs ys)))
      target (path bound source destination)
  in
  let refute s rule =
    stats.conflicts <- stats.conflicts + 1;
    conflict s rule
  in
  let positives = Positives.create 64 in
  let key l =
    match l.atom with
    | P (p, args) -> Some (`P p, List.map representative args)
    | D (p, args) -> Some (`D p, List.map representative args)
    | E _ -> None
  in
  List.iter
    (fun (s, l) ->
      if l.positive then
        Option.iter
          (fun k -> if not (Positives.mem positives k) then Positives.add positives k s)
          (key l))
    units;
  List.iter
    (fun (s, l) ->
      guard ();
      if not l.positive then
        match l.atom with
        | E (a, b) when representative a = representative b ->
            let target =
              if explanation = Short && final avatar s units then
                cheapest stats ~guard ~record ~units ~ids ~terms ~graph ~path ~next:!next
                  ~forest:(fun () -> rewrite !next s [ 0 ] a b)
                  s
                  [ ([ 0 ], a, b) ]
              else rewrite !next s [ 0 ] a b
            in
            refute target (Equality_resolve (target.id, 0, []))
        | _ ->
            Option.iter
              (fun k ->
                match Positives.find_opt positives k with
                | None -> ()
                | Some positive ->
                    let args = Clause.atom_terms l.atom in
                    let wanted = Clause.atom_terms (List.hd positive.clause).atom in
                    let target =
                      if explanation = Short && final avatar s units then
                        cheapest stats ~guard ~record ~units ~ids ~terms ~graph ~path ~next:!next
                          ~forest:(fun () ->
                            List.fold_left
                              (fun target (i, (x, y)) -> rewrite !next target [ i ] x y)
                              s
                              (List.mapi (fun i pair -> (i, pair)) (List.combine args wanted)))
                          s
                          (List.mapi (fun i (x, y) -> ([ i ], x, y)) (List.combine args wanted))
                      else
                        List.fold_left
                          (fun target (i, (x, y)) -> rewrite !next target [ i ] x y)
                          s
                          (List.mapi (fun i pair -> (i, pair)) (List.combine args wanted))
                    in
                    refute target (Resolve (positive.id, 0, target.id, 0, [])))
              (key l))
    units

let run_units stats ~guard ~record ~conflict ~explanation ~avatar units =
  stats.runs <- stats.runs + 1;
  if List.exists (fun (_, l) -> match l.atom with E _ -> l.positive | _ -> false) units then
    close stats ~guard ~record ~conflict ~explanation ~avatar units
  else
    (* Without equalities every congruence class is a singleton. Do not intern
       all subterms or rebuild a graph just to compare complementary atoms. *)
    let positives = Tbl.Atom.create 64 in
    List.iter
      (fun (s, l) ->
        guard ();
        if l.positive && not (Tbl.Atom.mem positives l.atom) then Tbl.Atom.add positives l.atom s)
      units;
    List.iter
      (fun (s, l) ->
        guard ();
        if not l.positive then
          let rule =
            match l.atom with
            | E (a, b) when a = b -> Some (Equality_resolve (s.id, 0, []))
            | atom ->
                Option.map
                  (fun p -> Resolve (p.id, 0, s.id, 0, []))
                  (Tbl.Atom.find_opt positives atom)
          in
          Option.iter
            (fun rule ->
              stats.conflicts <- stats.conflicts + 1;
              conflict s rule)
            rule)
      units
