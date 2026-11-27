(** Age plus one or two weight queues, a preferred queue and three positive-literal class queues,
    with shared liveness and lazy deletion. *)
type heap = Empty | Node of int * (int * int) * heap * heap

let rank = function Empty -> 0 | Node (r, _, _, _) -> r
let node x a b = if rank a >= rank b then Node (rank b + 1, x, a, b) else Node (rank a + 1, x, b, a)

(* [x <= y] on the (weight, id) pairs, without the polymorphic comparison: the same
   lexicographic order on two ints. *)
let[@inline] le ((a, b) : int * int) ((c, d) : int * int) = a < c || (a = c && b <= d)

let rec merge a b =
  match (a, b) with
  | Empty, h | h, Empty -> h
  | Node (_, x, l, r), Node (_, y, _, _) -> if le x y then node x l (merge r b) else merge b a

let push x h = merge (Node (1, x, Empty, Empty)) h
let pop = function Empty -> None | Node (_, x, a, b) -> Some (x, merge a b)

type policy = Size | Unit | Mixed

(* E-style queue mix (Evaluation): one heap per evaluation function, ordered by
   (priority, weight, order, id); the order is the clause's evaluation order, its id unless the
   caller gives one ([add ~order]): ids grow with creation, E's evaluation order. *)
type eheap = EEmpty | ENode of int * (int * float * int * int) * eheap * eheap

let erank = function EEmpty -> 0 | ENode (r, _, _, _) -> r

let enode x a b =
  if erank a >= erank b then ENode (erank b + 1, x, a, b) else ENode (erank a + 1, x, b, a)

(* [compare x y <= 0] on the (priority, weight, order, id) entries, without the polymorphic
   comparison: the same lexicographic order, with Float.compare (the polymorphic comparison's
   order on floats, nan included) on the weight. *)
let[@inline] ele ((p, w, o, i) : int * float * int * int) ((q, v, n, j) : int * float * int * int) =
  if p <> q then p < q
  else
    let c = Float.compare w v in
    if c <> 0 then c < 0 else if o <> n then o < n else i <= j

let rec emerge a b =
  match (a, b) with
  | EEmpty, h | h, EEmpty -> h
  | ENode (_, x, l, r), ENode (_, y, _, _) -> if ele x y then enode x l (emerge r b) else emerge b a

let epush x h = emerge (ENode (1, x, EEmpty, EEmpty)) h
let epop = function EEmpty -> None | ENode (_, x, a, b) -> Some (x, emerge a b)

(* Vampire's split passive containers (Saturation/PredicateSplitPassiveClauseContainers.cpp,
   SaturationAlgorithm.cpp makeLevel0..4), for a balanced mix: a tree whose inner nodes split the
   clauses by a feature (the number of positive literals for plsq) at cutoffs, either into the
   first queue whose cutoff the value does not exceed (tammet) or into that queue and every later
   one (layered), and select a child by weighted round robin; every leaf is an age:weight container
   of its own with its own balance. Liveness stays shared: a clause selected from one leaf is gone
   from all of them. Each node counts its live clauses. *)
type vleaf = {
  mutable vage : eheap;
  mutable vweight : eheap;
  mutable vbalance : int;
  mutable vcount : int;
  mutable vlimits : (int * int * int) option;
      (** LRS limits (AWPassiveClauseContainer): the age queue's age and selection weight, the
          weight queue's weight; [None]: none. *)
}

type vtree = VLeaf of vleaf | VSplit of vsplit

and vsplit = {
  feature : int;  (** The clause feature it splits by (0: positive literals). *)
  cutoffs : float array;  (** The last one is unbounded. *)
  inverted : int array;  (** lcm / ratio of each queue. *)
  balances : int array;
  layered : bool;
  children : vtree array;
  mutable scount : int;
}

type split_level = { split_feature : int; ratios : int list; cutoffs : float list; layered : bool }
(** One split level, outermost first: the feature, the queue ratios, the cutoffs (one fewer than the
    ratios) and the arrangement. *)

type mix = {
  switch : int array;  (** Cumulative selection counts (che_hcb.c HCBAddWFCB). *)
  heaps : eheap array;
  evals : (int, (int * float) array) Hashtbl.t;
  orders : (int, int) Hashtbl.t;
      (** Tie-break keys that differ from the id: E's evaluation order ([add ~order], with
          presaturation) or Vampire's clause numbers ([add ~number]: negative for the input clauses,
          which it processes in reverse order; the derived clauses' in their order of creation,
          which can differ from the order in which they are admitted). *)
  mutable current : int;
  mutable count : int;
  picked : int array;  (** Selections served by each queue. *)
  mutable last : int * (int * float);
      (** The queue and evaluation (priority, weight) of the last selection; a trace diagnostic. *)
  balance : (int * int) option;
      (** Vampire's age:weight selection (AWPassiveClauseContainer::popSelected) for a mix of two
          queues, the age queue and the weight queue, instead of the round-robin of the counts. *)
  mutable balanced : int;  (** Vampire's [_balance]. *)
  tree : vtree option;  (** Vampire's split containers ([balance] only); [heaps] stay empty. *)
  features : (int, int array) Hashtbl.t;  (** The split features of each clause in [tree]. *)
}

(* Shared clauses, three admission classes, no separate search modes. *)
type kind = Negative | One_positive | Many_positive

let kind_index = function Negative -> 0 | One_positive -> 1 | Many_positive -> 2

let classify clause =
  match List.fold_left (fun n l -> if l.Wire.positive then n + 1 else n) 0 clause with
  | 0 -> Negative
  | 1 -> One_positive
  | _ -> Many_positive

let policy_name = function Size -> "size" | Unit -> "unit" | Mixed -> "mixed"

type t = {
  mutable weight : heap;
  mutable unit_weight : heap;
  mutable age : heap;
  mutable preferred : heap;
  preference : int Tbl.Int.t;
  mutable preferred_selected : int;
  live : (int * int) Tbl.Int.t;
  mutable selected : int;
  ratio : int;
  policy : policy;
  mutable inserted : int;
  kinds : heap array;
  classes : (kind * int) Tbl.Int.t;
  mutable kind_turn : int;
  kind_selected : int array;
  kind_wait_total : int array;
  kind_wait_max : int array;
  plain : bool;  (** Only the age and size/unit weight heaps: no class or preferred turns. *)
  mix : mix option;
}

(** The queue phase is the position in a periodic selection schedule at which the first selection
    starts. Production queues: the age, class, preferred and size/unit turns of [take_plain] are a
    function of [selected], which starts at the phase. A queue mix: the position in the round-robin
    of [HCBStandardClauseSelect], which starts at the phase modulo the cycle length (the sum of the
    counts); phase 0 is E's own start, at the first queue. Two phases give the same schedule, so the
    same search, exactly when they are congruent modulo the schedule's period ([turn_period],
    [mix_period]). *)

(* The smallest period of [f], given that [length] is one. *)
let smallest_period ~length f =
  let rec repeats p s = s >= length || (f (s + p) = f s && repeats p (s + 1)) in
  let rec find p = if p >= length || (length mod p = 0 && repeats p 0) then p else find (p + 1) in
  if length <= 1 then 1 else find 1

(* The turn [take_plain] takes at selection [s]: age, unit weight, class and preferred slots. *)
let plain_turn ~policy ~plain ~ratio s =
  let by_age = s mod (ratio + 1) = ratio in
  let weighted = s - (s / (ratio + 1)) in
  ( by_age,
    policy = Mixed && weighted mod 2 = 1,
    (not plain) && (not by_age) && weighted mod 4 = 3,
    (not plain) && (not by_age) && s mod 2 = 1 )

(** The period of the production selection turns in the phase: 22 for the default ratio 10 (the age
    slot repeats every 11 selections, the preferred slot every 2, and 22 selections advance the
    class and unit/size alternations by 20, a multiple of 4). [8 * (ratio + 1)] is a period of every
    turn, so the smallest one divides it. *)
let turn_period ?(policy = Size) ?(plain = false) ~ratio () =
  if ratio < 0 || ratio > 1000000 then
    invalid_arg "Passive: weight ratio must be between 0 and 1000000";
  smallest_period ~length:(8 * (ratio + 1)) (plain_turn ~policy ~plain ~ratio)

(* The queue that a queue mix serves at cycle position [s]. *)
let mix_queue counts s =
  let rec go i s = function [] -> i | n :: rest -> if s < n then i else go (i + 1) (s - n) rest in
  go 0 s counts

(** The period of a queue mix's schedule in the phase: its cycle length (the sum of the counts),
    unless the schedule repeats within the cycle (one queue). 11 for E's 208 mix (1, 4, 1, 1, 4), 26
    for Y1346's (20, 5, 1). *)
let mix_period counts =
  if counts = [] || List.exists (fun n -> n < 1) counts then
    invalid_arg "Passive: queue counts must be positive";
  let length = List.fold_left ( + ) 0 counts in
  smallest_period ~length (fun s -> mix_queue counts (s mod length))

let rec gcd a b = if b = 0 then a else gcd b (a mod b)

let rec build_tree = function
  | [] -> VLeaf { vage = EEmpty; vweight = EEmpty; vbalance = 0; vcount = 0; vlimits = None }
  | level :: inner ->
      let n = List.length level.ratios in
      if n < 2 || List.length level.cutoffs <> n - 1 || List.exists (fun r -> r <= 0) level.ratios
      then invalid_arg "Passive: a split level needs two or more positive ratios and n-1 cutoffs";
      let lcm = List.fold_left (fun l r -> l / gcd l r * r) 1 level.ratios in
      VSplit
        {
          feature = level.split_feature;
          cutoffs = Array.of_list (level.cutoffs @ [ infinity ]);
          inverted = Array.of_list (List.map (fun r -> lcm / r) level.ratios);
          balances = Array.make n 0;
          layered = level.layered;
          children = Array.init n (fun _ -> build_tree inner);
          scount = 0;
        }

let create ?(policy = Size) ?(phase = 0) ?(plain = false) ?(mix = []) ?balance ?(split = []) ~ratio
    () =
  if ratio < 0 || ratio > 1000000 then
    invalid_arg "Passive: weight ratio must be between 0 and 1000000";
  if List.exists (fun n -> n < 1) mix then invalid_arg "Passive: queue counts must be positive";
  {
    weight = Empty;
    unit_weight = Empty;
    age = Empty;
    preferred = Empty;
    preference = Tbl.Int.create 128;
    preferred_selected = 0;
    live = Tbl.Int.create 256;
    selected = max 0 phase;
    ratio;
    policy;
    inserted = 0;
    kinds = Array.make 3 Empty;
    classes = Tbl.Int.create 256;
    kind_turn = 0;
    kind_selected = Array.make 3 0;
    kind_wait_total = Array.make 3 0;
    kind_wait_max = Array.make 3 0;
    plain;
    mix =
      (if mix = [] then None
       else
         let n = List.length mix in
         let switch = Array.of_list mix in
         for i = 1 to n - 1 do
           switch.(i) <- switch.(i) + switch.(i - 1)
         done;
         (* The phase's position in the cycle: [current] is the queue that serves it and [count]
            the selections of the cycle before it, as [take_mixed] keeps them. *)
         let count = max 0 phase mod switch.(n - 1) in
         Some
           {
             switch;
             heaps = Array.make n EEmpty;
             evals = Hashtbl.create 256;
             orders = Hashtbl.create 16;
             current = mix_queue mix count;
             count;
             picked = Array.make n 0;
             last = (-1, (0, 0.));
             balance =
               (match balance with
               | Some (a, w) when n = 2 && a >= 0 && w >= 0 && a + w > 0 -> Some (a, w)
               | Some _ -> invalid_arg "Passive: a balanced selection needs two queues"
               | None -> None);
             balanced = 0;
             tree =
               (if split = [] then None
                else if balance = None then invalid_arg "Passive: split queues need a balance"
                else Some (build_tree split));
             features = Hashtbl.create (if split = [] then 1 else 256);
           });
  }

(* The queues of a split node that hold a clause with feature value [v]. *)
let split_queues (s : vsplit) v =
  let n = Array.length s.cutoffs in
  let rec best i = if i >= n - 1 || float_of_int v <= s.cutoffs.(i) then i else best (i + 1) in
  let b = best 0 in
  if s.layered then List.init (n - b) (fun k -> b + k) else [ b ]

(* Every leaf that holds a clause with [features], and every node on the way counts it. *)
let rec tree_iter ~node ~leaf features = function
  | VLeaf l -> leaf l
  | VSplit s ->
      node s;
      List.iter
        (fun i -> tree_iter ~node ~leaf features s.children.(i))
        (split_queues s features.(s.feature))

let tree_size = function VLeaf l -> l.vcount | VSplit s -> s.scount

let mix_push m id evals =
  let order = Option.value ~default:id (Hashtbl.find_opt m.orders id) in
  Array.iteri
    (fun i (prio, weight) -> m.heaps.(i) <- epush (prio, weight, order, id) m.heaps.(i))
    evals

let enqueue q id (size, unit_weight) =
  q.weight <- push ((if q.policy = Unit then unit_weight else size), id) q.weight;
  if q.policy = Mixed then q.unit_weight <- push (unit_weight, id) q.unit_weight;
  q.age <- push (id, id) q.age;
  Option.iter
    (fun (kind, _) ->
      let i = kind_index kind in
      q.kinds.(i) <- push (unit_weight, id) q.kinds.(i))
    (Tbl.Int.find_opt q.classes id)

let add ?kind ?unit_weight ?evals ?order ?number ?features q id weight =
  let weights = (weight, Option.value ~default:weight unit_weight) in
  (match (q.mix, evals) with
  | Some m, Some evals ->
      if Array.length evals <> Array.length m.heaps then
        invalid_arg "Passive: one evaluation per queue is required";
      let key = match number with Some n -> n | None -> Option.value ~default:id order in
      Hashtbl.replace m.evals id evals;
      if key <> id then Hashtbl.replace m.orders id key else Hashtbl.remove m.orders id;
      (match m.tree with
      | None -> mix_push m id evals
      | Some tree ->
          let features =
            match features with
            | Some f -> f
            | None -> invalid_arg "Passive: split queues need the clause's features"
          in
          Hashtbl.replace m.features id features;
          let (pa, wa), (pw, ww) = (evals.(0), evals.(1)) in
          tree_iter features tree
            ~node:(fun s -> s.scount <- s.scount + 1)
            ~leaf:(fun l ->
              l.vcount <- l.vcount + 1;
              l.vage <- epush (pa, wa, key, id) l.vage;
              l.vweight <- epush (pw, ww, key, id) l.vweight));
      (* A queue mix serves every selection: the production heaps and classes stay empty. *)
      Tbl.Int.replace q.live id weights
  | Some _, None -> invalid_arg "Passive: a queue mix needs clause evaluations"
  | None, _ ->
      (match kind with
      | None -> Tbl.Int.remove q.classes id
      | Some kind -> Tbl.Int.replace q.classes id (kind, q.selected));
      Tbl.Int.replace q.live id weights;
      enqueue q id weights);
  q.inserted <- q.inserted + 1

let length q = Tbl.Int.length q.live

let invalidate q id =
  Option.iter
    (fun m ->
      (match (m.tree, Hashtbl.find_opt m.features id) with
      | Some tree, Some features when Tbl.Int.mem q.live id ->
          tree_iter features tree
            ~node:(fun s -> s.scount <- s.scount - 1)
            ~leaf:(fun l -> l.vcount <- l.vcount - 1);
          Hashtbl.remove m.features id
      | _ -> ());
      Hashtbl.remove m.evals id;
      Hashtbl.remove m.orders id)
    q.mix;
  Tbl.Int.remove q.live id;
  Tbl.Int.remove q.classes id;
  Tbl.Int.remove q.preference id

let preferred_weight q id score =
  let size, unit_weight = Tbl.Int.find q.live id in
  let weight = if q.policy = Size then size else unit_weight in
  weight * 16 / (16 + score)

let prefer q id score =
  if
    q.mix = None && Tbl.Int.mem q.live id
    && score > Option.value ~default:0 (Tbl.Int.find_opt q.preference id)
  then (
    Tbl.Int.replace q.preference id score;
    q.preferred <- push (preferred_weight q id score, id) q.preferred)

let rebuild q =
  q.weight <- Empty;
  q.unit_weight <- Empty;
  q.age <- Empty;
  q.preferred <- Empty;
  Array.fill q.kinds 0 3 Empty;
  (match q.mix with
  | None ->
      Tbl.Int.iter (enqueue q) q.live;
      Tbl.Int.iter
        (fun id score -> q.preferred <- push (preferred_weight q id score, id) q.preferred)
        q.preference
  | Some m -> (
      Array.fill m.heaps 0 (Array.length m.heaps) EEmpty;
      match m.tree with
      | None -> Hashtbl.iter (fun id evals -> mix_push m id evals) m.evals
      | Some tree ->
          let rec clear = function
            | VLeaf l ->
                l.vage <- EEmpty;
                l.vweight <- EEmpty
            | VSplit s -> Array.iter clear s.children
          in
          clear tree;
          Hashtbl.iter
            (fun id evals ->
              let key = Option.value ~default:id (Hashtbl.find_opt m.orders id) in
              let (pa, wa), (pw, ww) = (evals.(0), evals.(1)) in
              tree_iter (Hashtbl.find m.features id) tree ~node:ignore ~leaf:(fun l ->
                  l.vage <- epush (pa, wa, key, id) l.vage;
                  l.vweight <- epush (pw, ww, key, id) l.vweight))
            m.evals));
  q.inserted <- length q

(** Collection-time compaction. A queue mix keeps every live clause in each of its heaps, so it is
    rebuilt only once stale entries dominate, as [take] does; the production heaps are rebuilt. *)
let compact q =
  match q.mix with Some _ when q.inserted <= 2 * (length q + 64) -> () | _ -> rebuild q

let take_plain q =
  let by_age = q.selected mod (q.ratio + 1) = q.ratio in
  let weighted = q.selected - (q.selected / (q.ratio + 1)) in
  let by_unit = q.policy = Mixed && weighted mod 2 = 1 in
  let rec pick h =
    match pop h with
    | None -> (None, Empty)
    | Some ((_, id), h) -> if Tbl.Int.mem q.live id then (Some id, h) else pick h
  in
  let rec preferred h =
    match pop h with
    | None -> (None, Empty)
    | Some ((weight, id), rest) ->
        if
          Tbl.Int.mem q.live id
          && Option.fold ~none:false
               ~some:(fun score -> preferred_weight q id score = weight)
               (Tbl.Int.find_opt q.preference id)
        then (Some id, rest)
        else preferred rest
  in
  let selected =
    (* Every fourth non-age selection protects a class; the global age slot always
       wins. Empty classes return their slot to the shared queues. *)
    if (not q.plain) && (not by_age) && weighted mod 4 = 3 then (
      let i = q.kind_turn mod 3 in
      q.kind_turn <- q.kind_turn + 1;
      let rec choose h =
        match pop h with
        | None -> (None, Empty)
        | Some ((_, id), rest) -> (
            match Tbl.Int.find_opt q.classes id with
            | Some (kind, _) when kind_index kind = i -> (Some id, rest)
            | _ -> choose rest)
      in
      let id, rest = choose q.kinds.(i) in
      q.kinds.(i) <- rest;
      id)
    else None
  in
  let selected =
    if (not q.plain) && selected = None && (not by_age) && q.selected mod 2 = 1 then (
      let id, rest = preferred q.preferred in
      q.preferred <- rest;
      Option.iter (fun _ -> q.preferred_selected <- q.preferred_selected + 1) id;
      id)
    else selected
  in
  let result =
    match selected with
    | Some _ -> selected
    | None ->
        let result, h =
          pick (if by_age then q.age else if by_unit then q.unit_weight else q.weight)
        in
        if by_age then q.age <- h else if by_unit then q.unit_weight <- h else q.weight <- h;
        result
  in
  Option.iter
    (fun id ->
      Option.iter
        (fun (kind, born) ->
          let i = kind_index kind and wait = q.selected - born in
          q.kind_selected.(i) <- q.kind_selected.(i) + 1;
          q.kind_wait_total.(i) <- q.kind_wait_total.(i) + wait;
          q.kind_wait_max.(i) <- max q.kind_wait_max.(i) wait)
        (Tbl.Int.find_opt q.classes id);
      invalidate q id;
      q.selected <- q.selected + 1)
    result;
  if q.inserted > 4 * (length q + 64) then rebuild q;
  result

(* HCBStandardClauseSelect (che_hcb.c:898): the current queue serves its count,
   then the next one; every live clause is in every queue. *)
let take_mixed ?(skip = fun _ -> false) q m =
  let rec pick h =
    match epop h with
    | None -> (None, EEmpty)
    | Some ((_, _, _, id), rest) ->
        if not (Tbl.Int.mem q.live id) then pick rest
        else if skip id then (
          (* Dropped within the same turn (E's orphans at selection). *)
          Tbl.Int.remove q.live id;
          pick rest)
        else (Some id, rest)
  in
  let i =
    match m.balance with
    | Some (age, weight) ->
        (* AWPassiveClauseContainer::byWeight and popSelected: a positive balance selects by
           weight (queue 1), a negative one by age (queue 0), zero by weight unless the age
           ratio is the larger one. *)
        let by_weight =
          if age = 0 then true
          else if weight = 0 then false
          else if m.balanced > 0 then true
          else if m.balanced < 0 then false
          else age <= weight
        in
        if by_weight then (
          m.balanced <- m.balanced - age;
          1)
        else (
          m.balanced <- m.balanced + weight;
          0)
    | None -> m.current
  in
  let id, rest = pick m.heaps.(i) in
  m.heaps.(i) <- rest;
  if m.balance = None then (
    m.count <- m.count + 1;
    while m.current < Array.length m.switch && m.count = m.switch.(m.current) do
      m.current <- m.current + 1
    done;
    if m.current = Array.length m.switch then (
      m.count <- 0;
      m.current <- 0));
  Option.iter
    (fun id ->
      m.picked.(i) <- m.picked.(i) + 1;
      Option.iter (fun evals -> m.last <- (i, evals.(i))) (Hashtbl.find_opt m.evals id);
      invalidate q id;
      q.selected <- q.selected + 1)
    id;
  if q.inserted > 4 * (length q + 64) then rebuild q;
  id

(* AWPassiveClauseContainer::byWeight. *)
let by_weight ~age ~weight balance =
  if age = 0 then true
  else if weight = 0 then false
  else if balance > 0 then true
  else if balance < 0 then false
  else age <= weight

(* PredicateSplitPassiveClauseContainer::popSelected: the child with the least balance (the first
   on ties) is charged its inverted ratio and every balance drops by the least one; an empty child
   passes the turn to the next non-empty one to the right, else to the left. *)
let split_child (s : vsplit) =
  let n = Array.length s.children in
  let least = ref 0 in
  for k = 1 to n - 1 do
    if s.balances.(k) < s.balances.(!least) then least := k
  done;
  let low = s.balances.(!least) in
  s.balances.(!least) <- s.balances.(!least) + s.inverted.(!least);
  Array.iteri (fun k b -> s.balances.(k) <- b - low) s.balances;
  let rec right k = if k < n && tree_size s.children.(k) = 0 then right (k + 1) else k in
  match right !least with
  | k when k < n -> s.children.(k)
  | _ ->
      let rec left k = if k > 0 && tree_size s.children.(k) = 0 then left (k - 1) else k in
      s.children.(left (!least - 1))

(* A balanced mix with Vampire's split containers: down the tree to a leaf, then the leaf's own
   age:weight selection. *)
let take_tree ?(skip = fun _ -> false) q m tree (age, weight) =
  let rec pick h =
    match epop h with
    | None -> (None, EEmpty)
    | Some ((_, _, _, id), rest) ->
        if not (Tbl.Int.mem q.live id) then pick rest
        else if skip id then (
          invalidate q id;
          pick rest)
        else (Some id, rest)
  in
  if tree_size tree = 0 then None
  else
    let rec leaf = function VLeaf l -> l | VSplit s -> leaf (split_child s) in
    let l = leaf tree in
    let i = if by_weight ~age ~weight l.vbalance then 1 else 0 in
    let id, rest = pick (if i = 1 then l.vweight else l.vage) in
    if i = 1 then (
      l.vbalance <- l.vbalance - age;
      l.vweight <- rest)
    else (
      l.vbalance <- l.vbalance + weight;
      l.vage <- rest);
    Option.iter
      (fun id ->
        m.picked.(i) <- m.picked.(i) + 1;
        Option.iter (fun evals -> m.last <- (i, evals.(i))) (Hashtbl.find_opt m.evals id);
        invalidate q id;
        q.selected <- q.selected + 1)
      id;
    if q.inserted > 4 * (length q + 64) then rebuild q;
    id

(** The next selection. [skip] (a queue mix only) drops a clause it holds for instead of selecting
    it, without using the turn; the caller retires it. *)
let take ?skip q =
  match q.mix with
  | Some ({ tree = Some tree; balance = Some balance; _ } as m) -> take_tree ?skip q m tree balance
  | Some m -> take_mixed ?skip q m
  | None -> take_plain q

(** Vampire's LRS limit simulation (PassiveClauseContainer::updateLimits, simulationPopSelected):
    [count] selections of a balanced two-queue mix from its current balance, on persistent copies of
    the heaps (the queues are unchanged). Returns the evaluations at which the age queue and the
    weight queue stand afterwards, [None] for a queue the simulation emptied; [None] overall without
    a balanced mix. *)
let simulate_balance q ~count =
  match q.mix with
  | Some ({ balance = Some (age_ratio, weight_ratio); _ } as m) when Array.length m.heaps = 2 ->
      let simulated = Tbl.Int.create 64 in
      (* The first live, not yet simulated entry, and the heap without the skipped ones. *)
      let rec peek h =
        match epop h with
        | None -> (None, EEmpty)
        | Some ((prio, weight, _, id), rest) ->
            if Tbl.Int.mem q.live id && not (Tbl.Int.mem simulated id) then
              (Some (prio, weight, id), h)
            else peek rest
      in
      let age = ref m.heaps.(0) and weight = ref m.heaps.(1) and balance = ref m.balanced in
      let remaining = ref count and exhausted = ref false in
      while !remaining > 0 && not !exhausted do
        let a, ha = peek !age in
        age := ha;
        let w, hw = peek !weight in
        weight := hw;
        match (a, w) with
        | Some (_, _, ida), Some (_, _, idw) ->
            let by_weight =
              if age_ratio = 0 then true
              else if weight_ratio = 0 then false
              else if !balance > 0 then true
              else if !balance < 0 then false
              else age_ratio <= weight_ratio
            in
            if by_weight then (
              balance := !balance - age_ratio;
              Tbl.Int.replace simulated idw ())
            else (
              balance := !balance + weight_ratio;
              Tbl.Int.replace simulated ida ());
            decr remaining
        | _ -> exhausted := true
      done;
      let a, _ = peek !age and w, _ = peek !weight in
      let eval = Option.map (fun (prio, weight, _) -> (prio, weight)) in
      Some (eval a, eval w)
  | _ -> None

(** Vampire's LRS limits for split containers (PassiveClauseContainer::updateLimits): with more
    reachable selections than clauses ([sizeEstimate]: the last queue's size when layered, else the
    sum) no leaf is limited; otherwise [count] selections are simulated on the whole tree from the
    current balances (simulationPopSelected, which picks the leaf as [take_tree] does), and every
    leaf takes its limits from where its two queues stand (setLimitsFromSimulation: none for a queue
    the simulation emptied). Returns false without split containers. *)
let update_split_limits q ~count =
  match q.mix with
  | Some { tree = Some tree; balance = Some (age_ratio, weight_ratio); _ } ->
      let rec size_estimate = function
        | VLeaf l -> l.vcount
        | VSplit s ->
            if s.layered then size_estimate s.children.(Array.length s.children - 1)
            else Array.fold_left (fun n c -> n + size_estimate c) 0 s.children
      in
      let rec leaves f = function VLeaf l -> f l | VSplit s -> Array.iter (leaves f) s.children in
      (if count > size_estimate tree then leaves (fun l -> l.vlimits <- None) tree
       else
         let simulated = Tbl.Int.create 64 in
         (* Per leaf: its queues as persistent heaps and its simulated balance; per split node its
           simulated balances. *)
         let leaf_state = ref [] in
         leaves
           (fun l -> leaf_state := (l, (ref l.vage, ref l.vweight, ref l.vbalance)) :: !leaf_state)
           tree;
         let st l = List.assq l !leaf_state in
         let rec peek h =
           match epop h with
           | None -> (None, EEmpty)
           | Some ((prio, weight, _, id), rest) ->
               if Tbl.Int.mem q.live id && not (Tbl.Int.mem simulated id) then
                 (Some (prio, weight, id), h)
               else peek rest
         in
         let has_next l =
           let a, _, _ = st l in
           let x, h = peek !a in
           a := h;
           x <> None
         in
         let rec node_has_next = function
           | VLeaf l -> has_next l
           | VSplit s -> Array.exists node_has_next s.children
         in
         let split_balances = ref [] in
         let rec collect = function
           | VLeaf _ -> ()
           | VSplit s ->
               split_balances := (s, Array.copy s.balances) :: !split_balances;
               Array.iter collect s.children
         in
         collect tree;
         let rec pop = function
           | VLeaf l ->
               let a, w, b = st l in
               if by_weight ~age:age_ratio ~weight:weight_ratio !b then (
                 b := !b - age_ratio;
                 let x, h = peek !w in
                 w := h;
                 Option.iter (fun (_, _, id) -> Tbl.Int.replace simulated id ()) x)
               else (
                 b := !b + weight_ratio;
                 let x, h = peek !a in
                 a := h;
                 Option.iter (fun (_, _, id) -> Tbl.Int.replace simulated id ()) x)
           | VSplit s ->
               let balances = List.assq s !split_balances in
               let n = Array.length s.children in
               let least = ref 0 in
               for k = 1 to n - 1 do
                 if balances.(k) < balances.(!least) then least := k
               done;
               let low = balances.(!least) in
               balances.(!least) <- balances.(!least) + s.inverted.(!least);
               Array.iteri (fun k b -> balances.(k) <- b - low) balances;
               let rec right k =
                 if k < n && not (node_has_next s.children.(k)) then right (k + 1) else k
               in
               let k =
                 match right !least with
                 | k when k < n -> k
                 | _ ->
                     let rec left k =
                       if k > 0 && not (node_has_next s.children.(k)) then left (k - 1) else k
                     in
                     left (!least - 1)
               in
               pop s.children.(max 0 k)
         in
         let remaining = ref count in
         while !remaining > 0 && node_has_next tree do
           pop tree;
           decr remaining
         done;
         leaves
           (fun l ->
             let a, w, _ = st l in
             let xa, _ = peek !a and xw, _ = peek !w in
             l.vlimits <-
               (if l.vcount = 0 then None
                else
                  let max_age, max_age_weight =
                    match xa with
                    | Some (p, f, _) -> (p, int_of_float f / 2)
                    | None -> (max_int, max_int)
                  in
                  let max_weight = match xw with Some (p, _, _) -> p | None -> max_int in
                  Some (max_age, max_age_weight, max_weight)))
           tree);
      true
  | _ -> false

(** PredicateSplitPassiveClauseContainer::exceedsAllLimits for a new clause with [features], [age]
    and selection [weight] (AWPassiveClauseContainer::exceedsAllLimits at the leaves: below the age
    limit or within the weight limit is in). Layered: beyond the limits of every queue it would
    join; tammet: of its queue. *)
let split_exceeds q ~features ~age ~weight =
  match q.mix with
  | Some { tree = Some tree; _ } ->
      let exceeds l =
        match l.vlimits with
        | None -> false
        | Some (max_age, max_age_weight, max_weight) ->
            if age < max_age then false
            else if weight <= max_weight then false
            else if age > max_age then true
            else weight > max_age_weight
      in
      let all = ref true in
      tree_iter features tree ~node:ignore ~leaf:(fun l -> if not (exceeds l) then all := false);
      !all
  | _ -> false

(** Whether some leaf of the split containers has limits (PassiveClauseContainer::limitsActive). *)
let split_limited q =
  match q.mix with
  | Some { tree = Some tree; _ } ->
      let rec any = function
        | VLeaf l -> l.vlimits <> None
        | VSplit s -> Array.exists any s.children
      in
      any tree
  | _ -> false

let split q = match q.mix with Some { tree = Some _; _ } -> true | _ -> false
let mix_selections q = match q.mix with None -> [||] | Some m -> Array.copy m.picked

(** The queue and evaluation of a queue mix's last selection ((-1, (0, 0.)) without a mix). *)
let last_pick q = match q.mix with None -> (-1, (0, 0.)) | Some m -> m.last
