type t = { nodes : Wire.step Tbl.Int.t; mutable next : int }

let create () = { nodes = Tbl.Int.create 256; next = 0 }

let add p clause rule =
  let node : Wire.step = { id = p.next; clause; rule } in
  p.next <- p.next + 1;
  Tbl.Int.add p.nodes node.id node;
  node

let get p i = Tbl.Int.find p.nodes i
let length p = p.next
let stored p = Tbl.Int.length p.nodes

let statistics (c : Wire.certificate) =
  match c.natural with
  | Some code -> Natural.statistics code
  | None ->
      let boolean = match c.avatar with None -> 0 | Some a -> List.length a.boolean_steps in
      (List.length c.steps + boolean, List.length c.axioms)

let steps p =
  Tbl.Int.fold (fun _ s xs -> s :: xs) p.nodes []
  |> List.sort (fun (a : Wire.step) b -> compare a.id b.id)

(* The nodes reachable from [roots] stay, every other one is dropped. Node ids are below [p.next],
   so the reached ones are marked in a bit set, and the store drops the others in place: [nodes] is
   read only by id ([get], [stored]) and [steps] sorts what it lists, so its internal order is
   never observed. *)
let reclaim_list p roots =
  let keep = Bytes.make ((p.next + 7) lsr 3) '\000' in
  let marked id =
    id >= 0 && id < p.next && Char.code (Bytes.get keep (id lsr 3)) land (1 lsl (id land 7)) <> 0
  in
  let mark id =
    Bytes.set keep (id lsr 3)
      (Char.chr (Char.code (Bytes.get keep (id lsr 3)) lor (1 lsl (id land 7))))
  in
  let pending = Stack.create () in
  List.iter (fun id -> Stack.push id pending) roots;
  while not (Stack.is_empty pending) do
    let id = Stack.pop pending in
    if not (marked id) then (
      let step = get p id in
      mark id;
      List.iter (fun id -> Stack.push id pending) (Wire.parents step.rule))
  done;
  let before = stored p in
  Tbl.Int.filter_map_inplace (fun id step -> if marked id then Some step else None) p.nodes;
  before - stored p

(* [reclaim_list] with the roots given by [roots push] (every root passed to [push]) instead of a
   list, and an int array as the stack: the marked set is the set of nodes reachable from the
   roots whatever order they are pushed and visited in, so the store keeps the same nodes. The
   sweep pushes every live id of its tables without building lists of them. A root that is not
   stored raises [Not_found], as [get] does in [reclaim_list]. The bit set is sized from [p.next]
   on entry, so no node may be created while [roots] and the drain run (the engine's iterators
   create none); its accesses are checked, so a node created past the set raises
   [Invalid_argument] instead of being marked outside it. *)
let reclaim_with ?(dropped = fun _ -> ()) p roots =
  let keep = Bytes.make ((p.next + 7) lsr 3) '\000' in
  let marked id =
    id >= 0 && id < p.next && Char.code (Bytes.get keep (id lsr 3)) land (1 lsl (id land 7)) <> 0
  in
  let mark id =
    Bytes.set keep (id lsr 3)
      (Char.chr (Char.code (Bytes.get keep (id lsr 3)) lor (1 lsl (id land 7))))
  in
  let stack = ref (Array.make 1024 0) and top = ref 0 in
  let push id =
    if !top = Array.length !stack then (
      let grown = Array.make (2 * !top) 0 in
      Array.blit !stack 0 grown 0 !top;
      stack := grown);
    Array.unsafe_set !stack !top id;
    incr top
  in
  let drain () =
    while !top > 0 do
      decr top;
      let id = Array.unsafe_get !stack !top in
      if not (marked id) then (
        let step = get p id in
        mark id;
        List.iter push (Wire.parents step.rule))
    done
  in
  roots (fun id ->
      push id;
      if !top >= 4096 then drain ());
  drain ();
  let before = stored p in
  Tbl.Int.filter_map_inplace
    (fun id step ->
      if marked id then Some step
      else (
        dropped id;
        None))
    p.nodes;
  before - stored p

let reclaim p roots = reclaim_with p (fun push -> List.iter push roots)

let used_axioms (c : Wire.certificate) =
  let ids = Tbl.Int.create 32 in
  let use id = Tbl.Int.replace ids id () in
  List.iter (fun (s : Wire.step) -> match s.rule with Input (id, _) -> use id | _ -> ()) c.steps;
  let rec term = function
    | Wire.V _ -> ()
    | Fn (symbol, ts) ->
        (match symbol with Skolem (id, _) -> use id | Original _ -> ());
        List.iter term ts
  in
  Option.iter
    (fun (a : Wire.avatar_certificate) ->
      List.iter
        (List.iter (fun (l : Wire.literal) ->
             match l.atom with
             | D ((id, _), ts) ->
                 use id;
                 List.iter term ts
             | P (_, ts) -> List.iter term ts
             | E (x, y) ->
                 term x;
                 term y))
        a.components)
    c.avatar;
  List.filter (fun (a : Wire.axiom) -> Tbl.Int.mem ids a.axiom_id) c.axioms

let collect get root =
  let seen = Tbl.Int.create 64 and pending = Stack.create () in
  Stack.push root pending;
  while not (Stack.is_empty pending) do
    let id = Stack.pop pending in
    if not (Tbl.Int.mem seen id) then (
      let (node : Wire.step) = get id in
      Tbl.Int.add seen id node;
      List.iter (fun id -> Stack.push id pending) (Wire.parents node.rule))
  done;
  Tbl.Int.fold (fun _ node nodes -> node :: nodes) seen []
  |> List.sort (fun (x : Wire.step) y -> compare x.id y.id)

let prune (c : Wire.certificate) =
  match c.natural with
  | Some code -> { c with natural = Some (Natural.prune code) }
  | None when Option.is_some c.avatar ->
      let c = Avatar_proof.prune c (Option.get c.avatar) in
      { c with axioms = used_axioms c }
  | None ->
      let nodes = Tbl.Int.create (List.length c.steps) in
      List.iter (fun (s : Wire.step) -> Tbl.Int.add nodes s.id s) c.steps;
      let c = { c with steps = collect (Tbl.Int.find nodes) c.root } in
      { c with axioms = used_axioms c }

let extract ?(cnf_mode = Wire.Hybrid) ?avatar p ~theory ~axioms ~root =
  let c : Wire.certificate =
    {
      natural = None;
      avatar;
      cnf_mode;
      theory;
      axioms;
      steps = (if Option.is_some avatar then steps p else collect (get p) root);
      root;
    }
  in
  (* The plain root's transitive ancestors were already collected and sorted.
     Only AVATAR needs a second kind of slice through its Boolean dependencies. *)
  match avatar with
  | None -> { c with axioms = used_axioms c }
  | Some _ -> prune c
