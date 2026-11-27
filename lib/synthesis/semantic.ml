(* Small finite structures, used only on the search side of the schema probe
   lane. Nothing here is trusted: a "killer" is merely an instance that is
   false in every structure of the pool, i.e. a promising candidate for an
   isolated refutation attempt. Every resulting proof is still checked by the
   ordinary kernel. This module has no condition grammar of its own: the lane
   probes the schemas' own enumeration, the main search's instances and the
   conditions of the observational source (Observational: the theory's own
   formulas, one per truth table over this pool); an experimental condition
   prior lives only in the schema benchmark. With the lane's evaluation
   option [mace] the pool and counter-models are built by SAT (Mace)
   instead of this module's sampling [builder] and [find_model]; [eval]
   serves both.

   All budgets are counted in evaluation steps (one step per formula node
   visited in one structure), never in wall-clock time, so the same inputs
   give the same pool and killers on a loaded or an idle machine. *)

type model = {
  size : int;
  preds : (string * int, bool array) Hashtbl.t;
  funs : (string * int, int array) Hashtbl.t;
}

(* Evaluation steps spent; the probe lane converts them into its work units. *)
type meter = { mutable steps : int }

let meter () = { steps = 0 }

exception Budget

let index n args = List.fold_left (fun acc a -> (acc * n) + a) 0 args
let rec pow n k = if k = 0 then 1 else n * pow n (k - 1)

(* [None]: evaluation budget exhausted or an unknown symbol. *)
let eval ?(budget = 200_000) ?meter m f =
  let steps = ref budget in
  let rec term env = function
    | Wire.B i -> List.nth env i
    | Wire.F _ -> 0
    | Wire.App (s, ts) ->
        let args = List.map (term env) ts in
        (Hashtbl.find m.funs (s, List.length ts)).(index m.size args)
  and formula env f =
    decr steps;
    if !steps < 0 then raise Budget;
    match f with
    | Wire.Top -> true
    | Wire.Bot -> false
    | Wire.Pred (p, ts) ->
        let args = List.map (term env) ts in
        (Hashtbl.find m.preds (p, List.length ts)).(index m.size args)
    | Wire.Eq (x, y) -> term env x = term env y
    | Wire.Neg g -> not (formula env g)
    | Wire.Conj gs -> List.for_all (formula env) gs
    | Wire.Disj gs -> List.exists (formula env) gs
    | Wire.All g ->
        let rec loop i = i >= m.size || (formula (i :: env) g && loop (i + 1)) in
        loop 0
    | Wire.Ex g ->
        let rec loop i = i < m.size && (formula (i :: env) g || loop (i + 1)) in
        loop 0
  in
  let result =
    try Some (formula [] f) with Budget | Not_found | Failure _ | Invalid_argument _ -> None
  in
  Option.iter (fun c -> c.steps <- c.steps + (budget - max 0 !steps)) meter;
  result

(* Tables of a structure as one mixed-radix vector of cells. *)
type shape = { cells : (bool * (string * int) * int) list (* is_pred, symbol, cell count *) }

let shape signature n =
  {
    cells =
      List.map (fun (s, k) -> (false, (s, k), pow n k)) (Signature.functions signature)
      @ List.map (fun (p, k) -> (true, (p, k), pow n k)) (Signature.predicates signature);
  }

let build n shape values =
  let m = { size = n; preds = Hashtbl.create 4; funs = Hashtbl.create 4 } in
  let pos = ref 0 in
  List.iter
    (fun (is_pred, key, count) ->
      if is_pred then
        Hashtbl.replace m.preds key (Array.init count (fun i -> values.(!pos + i) = 1))
      else Hashtbl.replace m.funs key (Array.init count (fun i -> values.(!pos + i)));
      pos := !pos + count)
    shape.cells;
  m

let radices n shape =
  List.concat_map
    (fun (is_pred, _, count) -> List.init count (fun _ -> if is_pred then 2 else n))
    shape.cells
  |> Array.of_list

(* All structures of size [n] when there are at most [limit], else [limit]
   deterministic random samples. Lazy, so a budget can stop it early. *)
let structures ~rng ~limit signature n : model Seq.t =
  let shape = shape signature n in
  let radix = radices n shape in
  let total = Array.fold_left (fun acc r -> if acc > limit then acc else acc * r) 1 radix in
  if total <= limit then
    let rec from values () =
      let m = build n shape values in
      let next = Array.copy values in
      let rec bump i =
        if i < 0 then false
        else if next.(i) + 1 < radix.(i) then (
          next.(i) <- next.(i) + 1;
          true)
        else (
          next.(i) <- 0;
          bump (i - 1))
      in
      Seq.Cons (m, if bump (Array.length radix - 1) then from next else Seq.empty)
    in
    from (Array.make (Array.length radix) 0)
  else
    Seq.init limit (fun _ -> ())
    |> Seq.map (fun () -> build n shape (Array.map (fun r -> Random.State.int rng r) radix))
    |> Seq.memoize

type pool = {
  models : model list;
  axioms_used : int;
  axioms_total : int;
  active : Wire.source list;
}

let empty = { models = []; axioms_used = 0; axioms_total = 0; active = [] }

(* Models of the largest greedily chosen subset of [axioms] that has small
   models; axioms without any small model (e.g. infinity) are dropped. *)
let settle ~sizes ~capacity axioms candidates =
  let k = Array.length axioms in
  let active = Array.make k true in
  let satisfies (_, sat) = Array.for_all2 (fun a s -> (not a) || s) active sat in
  let rec settle () =
    let models = List.filter satisfies candidates in
    if models <> [] || not (Array.exists Fun.id active) then models
    else
      (* Drop the active axiom satisfied by the fewest structures. *)
      let worst = ref (-1) and fewest = ref max_int in
      Array.iteri
        (fun i a ->
          if a then
            let c = List.length (List.filter (fun (_, sat) -> sat.(i)) candidates) in
            if c < !fewest then (
              fewest := c;
              worst := i))
        active;
      active.(!worst) <- false;
      settle ()
  in
  let models = settle () |> List.map fst in
  (* Keep a size-diverse selection: an equal share per domain size. *)
  let share = max 1 (capacity / max 1 (List.length sizes)) in
  let selected =
    List.concat_map
      (fun n ->
        let rec take c = function
          | [] -> []
          | _ when c = 0 -> []
          | m :: r -> if m.size = n then m :: take (c - 1) r else take c r
        in
        take share models)
      sizes
  in
  {
    models = selected;
    axioms_used = Array.fold_left (fun n a -> if a then n + 1 else n) 0 active;
    axioms_total = k;
    active = List.filteri (fun i _ -> active.(i)) (Array.to_list axioms);
  }

(* Incremental pool construction: [advance] evaluates structures until a
   step quota is spent, so the probe lane can build the pool in slices of its
   own share instead of a blocking startup phase. The total is capped by
   [budget] evaluation steps (the former 0.3 s deadline). *)
type builder = {
  b_signature : Signature.t;
  b_axioms : Wire.source array;
  b_sizes : int list;
  b_capacity : int;
  b_per_size : int;
  b_rng : Random.State.t;
  mutable b_pending : int list;
  mutable b_current : model Seq.t;
  mutable b_candidates : (model * bool array) list;
  b_meter : meter;
  b_budget : int;
}

let builder ?(sizes = [ 1; 2; 3; 4 ]) ?(per_size = 2000) ?(capacity = 128) ~budget signature axioms
    =
  {
    b_signature = signature;
    b_axioms = Array.of_list axioms;
    b_sizes = sizes;
    b_capacity = capacity;
    b_per_size = per_size;
    b_rng = Random.State.make [| 20261114 |];
    b_pending = sizes;
    b_current = Seq.empty;
    b_candidates = [];
    b_meter = meter ();
    b_budget = budget;
  }

let builder_steps b = b.b_meter.steps

(* Evaluate up to [quota] more steps; [Some pool] when construction is done. *)
let advance b ~quota =
  if Signature.is_unrestricted b.b_signature then Some empty
  else
    let stop = b.b_meter.steps + quota in
    let rec go () =
      if b.b_meter.steps >= b.b_budget then `Done
      else if b.b_meter.steps >= stop then `More
      else
        match b.b_current () with
        | Seq.Cons (m, rest) ->
            b.b_current <- rest;
            let sat =
              Array.map (fun f -> eval ~budget:20_000 ~meter:b.b_meter m f = Some true) b.b_axioms
            in
            b.b_candidates <- (m, sat) :: b.b_candidates;
            go ()
        | Seq.Nil -> (
            match b.b_pending with
            | [] -> `Done
            | n :: rest ->
                b.b_pending <- rest;
                b.b_current <- structures ~rng:b.b_rng ~limit:b.b_per_size b.b_signature n;
                (* Building the size-n tables is charged as one step per cell. *)
                b.b_meter.steps <- b.b_meter.steps + 1;
                go ())
    in
    match go () with
    | `More -> None
    | `Done ->
        Some (settle ~sizes:b.b_sizes ~capacity:b.b_capacity b.b_axioms (List.rev b.b_candidates))

(* Whole pool at once (tests and offline tools). *)
let pool ?sizes ?per_size ?capacity ?(budget = 20_000_000) signature axioms =
  let b = builder ?sizes ?per_size ?capacity ~budget signature axioms in
  let rec go () = match advance b ~quota:max_int with Some p -> p | None -> go () in
  go ()

(* False in every pool model (and the pool is nonempty). *)
let killer ?(budget = 200_000) ?meter pool f =
  pool.models <> [] && List.for_all (fun m -> eval ~budget ?meter m f = Some false) pool.models

(* Counterexample refinement: a structure satisfying [axioms] and [f], if a
   bounded search finds one within [budget] evaluation steps. *)
let find_model ?(sizes = [ 1; 2; 3; 4 ]) ?(per_size = 1500) ~budget ?meter signature axioms f =
  if Signature.is_unrestricted signature then None
  else
    let local = { steps = 0 } in
    let rng = Random.State.make [| 4242 |] in
    let fits m =
      local.steps < budget
      && eval ~budget:50_000 ~meter:local m f = Some true
      && List.for_all (fun a -> eval ~budget:50_000 ~meter:local m a = Some true) axioms
    in
    let rec go = function
      | [] -> None
      | n :: rest -> (
          match Seq.find fits (structures ~rng ~limit:per_size signature n) with
          | Some m -> Some m
          | None -> if local.steps >= budget then None else go rest)
    in
    let found = go sizes in
    Option.iter (fun c -> c.steps <- c.steps + local.steps) meter;
    found
