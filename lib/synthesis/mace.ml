(* MACE-style finite model building (SEM-MACE), used only on the search side of
   the schema probe lane: the finite-model pool that ranks instances and the
   counter-model search that refines it. Nothing here is trusted: a model only
   reorders or drops candidate instances, and every proof is still checked by
   the ordinary kernel.

   Method (Claessen & Sorensson's Paradox, 2003, without its clausifier): the
   formulas are grounded over a domain {0 .. n-1} for n = 1, 2, ... into the
   existing CDCL (lib/saturation/boolean.ml).
   - Every predicate cell P(e1..ek) is a variable; every function cell
     f(e1..ek) has one variable per value, with totality (some value) and
     functionality (at most one value) clauses.
   - Quantifiers expand into conjunctions and disjunctions over the domain;
     terms are flattened: a term denotes, for each value v, the condition
     under which it equals v. Subformulas become Tseitin gates (definitional
     clauses, shared by identical literal sets), with constant folding.
   - Symmetry breaking by the least-number rule on the constants: the i-th
     constant takes a value of at most i, and a value v > 0 only when some
     earlier constant takes v - 1 (every model has such an isomorphic copy).
   - A selector per axiom: a model of a maximal satisfiable subset of the
     axioms at size n is found by deciding the selectors true first and then
     growing (the found set is kept, one more selector is required).
   - Diverse models: blocking clauses, deterministic random phases before
     every solve, and an isomorphism check (canonical form over all
     permutations, n <= 6) so that the pool holds no two isomorphic models.

   Budgets are deterministic: every guard call of the CDCL and every clause
   or gate built is one step on the caller's meter (Semantic.meter); a solve
   that runs past its cap is abandoned. No wall-clock time is read. *)

exception Exhausted

(* Literals of the CDCL are signed (variable + 1); [ltrue] and [lfalse] are
   constants of the grounding (never given to the solver), and [- l] negates
   both kinds. *)
let ltrue = max_int
let lfalse = -max_int

type ground = {
  n : int;
  sat : Boolean.t;
  meter : Semantic.meter;
  limit : int;  (** The meter reading at which grounding and solving stop. *)
  preds : (string * int, int array) Hashtbl.t;  (** Cell -> literal. *)
  funs : (string * int, int array) Hashtbl.t;  (** Cell * n + value -> literal. *)
  gates : (int list, int) Hashtbl.t;  (** Sorted conjunct literals -> gate literal. *)
  signature : Signature.t;
}

let tick g k =
  g.meter.steps <- g.meter.steps + k;
  if g.meter.steps > g.limit then raise Exhausted

let fresh g = Boolean.new_variable g.sat + 1
let structural = Boolean.Split (-1)
let add g lits = ignore (Boolean.add_clause g.sat ~origin:structural lits)
let rec pow n k = if k = 0 then 1 else n * pow n (k - 1)

(* A conjunction of literals as one literal (a Tseitin gate when it has two or
   more non-constant conjuncts). *)
let conj g lits =
  if List.mem lfalse lits then lfalse
  else
    let lits = List.sort_uniq compare (List.filter (fun l -> l <> ltrue) lits) in
    if List.exists (fun l -> List.mem (-l) lits) lits then lfalse
    else
      match lits with
      | [] -> ltrue
      | [ l ] -> l
      | lits -> (
          match Hashtbl.find_opt g.gates lits with
          | Some x -> x
          | None ->
              tick g (List.length lits + 1);
              let x = fresh g in
              List.iter (fun l -> add g [ -x; l ]) lits;
              add g (x :: List.map (fun l -> -l) lits);
              Hashtbl.add g.gates lits x;
              x)

let disj g lits = -conj g (List.map (fun l -> -l) lits)

(* Symbol tables of size n: predicate cells, function cells with totality,
   functionality, and least-number symmetry breaking on the constants. *)
let create ~meter ~limit signature n =
  let g =
    {
      n;
      sat = Boolean.create ();
      meter;
      limit;
      preds = Hashtbl.create 8;
      funs = Hashtbl.create 8;
      gates = Hashtbl.create 1024;
      signature;
    }
  in
  List.iter
    (fun (p, k) ->
      let cells = pow n k in
      tick g cells;
      Hashtbl.replace g.preds (p, k) (Array.init cells (fun _ -> fresh g)))
    (Signature.predicates signature);
  let constants = ref [] in
  List.iter
    (fun (f, k) ->
      let cells = pow n k in
      tick g (cells * n * n);
      let vars = Array.init (cells * n) (fun _ -> fresh g) in
      for c = 0 to cells - 1 do
        add g (List.init n (fun v -> vars.((c * n) + v)));
        for v = 0 to n - 1 do
          for w = v + 1 to n - 1 do
            add g [ -vars.((c * n) + v); -vars.((c * n) + w) ]
          done
        done
      done;
      if k = 0 then constants := vars :: !constants;
      Hashtbl.replace g.funs (f, k) vars)
    (Signature.functions signature);
  (* Least-number rule: constant i (in signature order) takes a value <= i, and
     a value v > 0 only if an earlier constant takes v - 1. *)
  List.iteri
    (fun i vars ->
      for v = 0 to n - 1 do
        if v > i then add g [ -vars.(v) ]
        else if v > 0 then
          add g
            (-vars.(v)
            :: List.map
                 (fun prev -> prev.(v - 1))
                 (List.filteri (fun j _ -> j < i) (List.rev !constants)))
      done)
    (List.rev !constants);
  g

(* All combinations of the arguments' values with their conditions. *)
let rec product = function
  | [] -> [ ([], []) ]
  | d :: rest ->
      let tails = product rest in
      List.concat_map (fun (v, l) -> List.map (fun (vs, ls) -> (v :: vs, l :: ls)) tails) d

(* A term under [env] (domain elements of the bound variables, innermost
   first): for each value it can take, the condition under which it does. *)
let rec term g env = function
  | Wire.B i -> [ (List.nth env i, ltrue) ]
  | Wire.F _ -> [ (0, ltrue) ]
  | Wire.App (f, args) ->
      let k = List.length args in
      let vars = Hashtbl.find g.funs (f, k) in
      let by_value = Array.make g.n [] in
      List.iter
        (fun (values, conds) ->
          let cell = Semantic.index g.n values in
          for v = 0 to g.n - 1 do
            let l = conj g (vars.((cell * g.n) + v) :: conds) in
            if l <> lfalse then by_value.(v) <- l :: by_value.(v)
          done)
        (product (List.map (term g env) args));
      List.concat
        (List.init g.n (fun v ->
             match by_value.(v) with
             | [] -> []
             | ls ->
                 let l = disj g ls in
                 if l = lfalse then [] else [ (v, l) ]))

(* A formula under [env] as one literal. Conjunctions and quantifiers stop at
   the first false part, disjunctions at the first true one. *)
let rec formula g env f =
  tick g 1;
  match f with
  | Wire.Top -> ltrue
  | Wire.Bot -> lfalse
  | Wire.Pred (p, args) ->
      let k = List.length args in
      let cells = Hashtbl.find g.preds (p, k) in
      disj g
        (List.map
           (fun (values, conds) -> conj g (cells.(Semantic.index g.n values) :: conds))
           (product (List.map (term g env) args)))
  | Wire.Eq (a, b) ->
      let da = term g env a and db = term g env b in
      disj g
        (List.concat_map
           (fun (va, ca) ->
             List.filter_map (fun (vb, cb) -> if va = vb then Some (conj g [ ca; cb ]) else None) db)
           da)
  | Wire.Neg h -> -formula g env h
  | Wire.Conj hs -> all_of g (List.to_seq hs |> Seq.map (formula g env))
  | Wire.Disj hs -> -all_of g (List.to_seq hs |> Seq.map (fun h -> -formula g env h))
  | Wire.All h -> all_of g (Seq.init g.n (fun e -> formula g (e :: env) h))
  | Wire.Ex h -> -all_of g (Seq.init g.n (fun e -> -formula g (e :: env) h))

and all_of g parts =
  let rec go acc s =
    match s () with
    | Seq.Nil -> conj g acc
    | Seq.Cons (l, rest) -> if l = lfalse then lfalse else go (l :: acc) rest
  in
  go [] parts

(* The model of the solver's assignment. *)
let decode g (values : bool array) : Semantic.model =
  let lit_true l = values.(l - 1) in
  let m = { Semantic.size = g.n; preds = Hashtbl.create 4; funs = Hashtbl.create 4 } in
  Hashtbl.iter (fun key cells -> Hashtbl.replace m.preds key (Array.map lit_true cells)) g.preds;
  Hashtbl.iter
    (fun key vars ->
      let cells = Array.length vars / g.n in
      Hashtbl.replace m.funs key
        (Array.init cells (fun c ->
             let rec find v =
               if v >= g.n - 1 || lit_true vars.((c * g.n) + v) then v else find (v + 1)
             in
             find 0)))
    g.funs;
  m

(* The literals that fix the interpretation of [values] (for a blocking clause). *)
let assignment g (values : bool array) =
  let lits = ref [] in
  Hashtbl.iter
    (fun _ cells -> Array.iter (fun l -> lits := (if values.(l - 1) then l else -l) :: !lits) cells)
    g.preds;
  Hashtbl.iter
    (fun _ vars -> Array.iter (fun l -> if values.(l - 1) then lits := l :: !lits) vars)
    g.funs;
  !lits

(* Deterministic pseudo-random phases (diverse models), set before a solve. *)
let shuffle_phases g rng =
  let s = g.sat in
  for v = 0 to s.Boolean.variables - 1 do
    s.phases.(v) <- Random.State.bool rng
  done

let solve g =
  let guard () = tick g 1 in
  match Boolean.solve g.sat ~guard with Boolean.Sat values -> Some values | Boolean.Unsat -> None

(* ---------- canonical forms (isomorphism check) ---------- *)

let rec permutations = function
  | [] -> [ [] ]
  | l ->
      List.concat_map
        (fun x -> List.map (fun p -> x :: p) (permutations (List.filter (( <> ) x) l)))
        l

(* The least encoding of [m] over all renamings of its elements: two models
   are isomorphic exactly when their canonical forms are equal. *)
let canonical (m : Semantic.model) ~meter =
  let n = m.size in
  let keys t = Hashtbl.fold (fun k _ acc -> k :: acc) t [] |> List.sort compare in
  let pkeys = keys m.preds and fkeys = keys m.funs in
  let encode perm =
    (* perm.(old) = new; read the cells of the renamed model in index order *)
    let inv = Array.make n 0 in
    Array.iteri (fun o p -> inv.(p) <- o) perm;
    let buf = Buffer.create 64 in
    let decode k idx =
      (* new index -> old argument tuple *)
      let args = Array.make k 0 and r = ref idx in
      for j = k - 1 downto 0 do
        args.(j) <- inv.(!r mod n);
        r := !r / n
      done;
      Semantic.index n (Array.to_list args)
    in
    List.iter
      (fun ((_, k) as key) ->
        let cells = Hashtbl.find m.preds key in
        for idx = 0 to pow n k - 1 do
          Buffer.add_char buf (if cells.(decode k idx) then '1' else '0')
        done)
      pkeys;
    List.iter
      (fun ((_, k) as key) ->
        let cells = Hashtbl.find m.funs key in
        for idx = 0 to pow n k - 1 do
          Buffer.add_char buf (Char.chr (48 + perm.(cells.(decode k idx))))
        done)
      fkeys;
    meter.Semantic.steps <- meter.Semantic.steps + Buffer.length buf;
    Buffer.contents buf
  in
  List.fold_left
    (fun best p ->
      let e = encode (Array.of_list p) in
      match best with Some b when b <= e -> best | _ -> Some e)
    None
    (permutations (List.init n Fun.id))
  |> Option.get

(* ---------- one size: maximal satisfiable subsets and model enumeration ---------- *)

type selector = Never | Always | Sel of int

(* Ground every axiom behind a selector (axiom i holds when its selector is
   true): [Never] for an axiom that is false at this size whatever the
   interpretation, [Always] for one that is true in every structure. *)
let selectors g axioms =
  Array.map
    (fun f ->
      match formula g [] f with
      | exception (Not_found | Invalid_argument _ | Failure _) -> Never
      | l when l = lfalse -> Never
      | l when l = ltrue -> Always
      | l ->
          let s = fresh g in
          add g [ -s; l ];
          Sel s)
    axioms

(* A model of a maximal satisfiable subset of [axioms] at size [n], and the
   subset: selectors are decided true first (phase and activity), then the
   found subset is kept and one more axiom is required until that fails. *)
let mss ~meter ~limit signature axioms n =
  let g = create ~meter ~limit signature n in
  let sel = selectors g axioms in
  let s = g.sat in
  Array.iter
    (function
      | Sel l ->
          s.phases.(l - 1) <- true;
          s.activity.(l - 1) <- 1e50
      | Never | Always -> ())
    sel;
  match solve g with
  | None -> None
  | Some values ->
      let chosen values =
        Array.map (function Sel l -> values.(l - 1) | Always -> true | Never -> false) sel
      in
      let rec grow values =
        let set = chosen values in
        let missing =
          List.filter_map
            (fun i -> match sel.(i) with Sel l when not set.(i) -> Some l | _ -> None)
            (List.init (Array.length sel) Fun.id)
        in
        if missing = [] then (set, decode g values)
        else (
          Array.iteri (fun i l -> match l with Sel l when set.(i) -> add g [ l ] | _ -> ()) sel;
          add g missing;
          match solve g with Some values' -> grow values' | None -> (set, decode g values))
      in
      Some (grow values)

(* Up to [count] pairwise non-isomorphic models of all of [axioms] at size [n]
   (none of them isomorphic to a model in [known], canonical forms). *)
let models ?(iso = true) ~meter ~limit ~rng ~count ~known signature axioms n =
  let g = create ~meter ~limit signature n in
  let ok = ref true in
  Array.iter
    (fun f ->
      match formula g [] f with
      | exception (Not_found | Invalid_argument _ | Failure _) -> ok := false
      | l when l = lfalse -> ok := false
      | l -> if l <> ltrue then add g [ l ])
    axioms;
  let found = ref [] and tries = ref 0 in
  (try
     while !ok && List.length !found < count && !tries < 4 * count do
       incr tries;
       shuffle_phases g rng;
       match solve g with
       | None -> ok := false
       | Some values ->
           let m = decode g values in
           if not iso then found := m :: !found
           else
             let c = canonical m ~meter in
             if not (Hashtbl.mem known c) then (
               Hashtbl.add known c ();
               found := m :: !found);
             add g (List.map (fun l -> -l) (assignment g values))
     done
   with Exhausted -> ());
  List.rev !found

(* ---------- the pool builder ---------- *)

type builder = {
  signature : Signature.t;
  axioms : Wire.source array;
  sizes : int list;
  per_size : int;
  meter : Semantic.meter;
  budget : int;
  rng : Random.State.t;
  known : (string, unit) Hashtbl.t;
  mutable pending_mss : int list;
  mutable subsets : bool array list;  (** The maximal satisfiable subset found at each size. *)
  mutable best : (bool array * int) option;  (** The chosen subset and the first size found. *)
  mutable pending_models : int list;
  mutable found : Semantic.model list;
}

let builder ?(sizes = [ 1; 2; 3; 4 ]) ?(per_size = 32) ~budget signature axioms =
  {
    signature;
    axioms = Array.of_list axioms;
    sizes;
    per_size;
    meter = Semantic.meter ();
    budget;
    rng = Random.State.make [| 20261116 |];
    known = Hashtbl.create 64;
    pending_mss = sizes;
    subsets = [];
    best = None;
    pending_models = [];
    found = [];
  }

let steps b = b.meter.steps
let count set = Array.fold_left (fun n x -> if x then n + 1 else n) 0 set

let pool_of b =
  let set =
    match b.best with Some (set, _) -> set | None -> Array.make (Array.length b.axioms) false
  in
  {
    Semantic.models = List.rev b.found;
    axioms_used = count set;
    axioms_total = Array.length b.axioms;
    active = List.filteri (fun i _ -> set.(i)) (Array.to_list b.axioms);
  }

(* Spend up to [quota] more steps; [Some pool] when the pool is built. One
   task (the subset search at one size, or the models of one size) runs to its
   own cap, so a call can overrun its quota by one task. *)
let advance b ~quota =
  if Signature.is_unrestricted b.signature then Some Semantic.empty
  else
    let stop = b.meter.steps + quota in
    let task_cap () =
      min b.budget (b.meter.steps + (b.budget / (2 * max 1 (List.length b.sizes))))
    in
    let rec go () =
      if b.meter.steps >= b.budget then `Done
      else if b.meter.steps >= stop then `More
      else
        match (b.pending_mss, b.pending_models) with
        | n :: rest, _ ->
            b.pending_mss <- rest;
            (match mss ~meter:b.meter ~limit:(task_cap ()) b.signature b.axioms n with
            | exception Exhausted -> ()
            | None -> ()
            | Some (set, _) -> b.subsets <- b.subsets @ [ set ]);
            if b.pending_mss = [] then (
              (* The largest subset; among equal ones, the one contained in the
                 subsets of the most sizes (it has models at more sizes); then
                 the first found. *)
              let within set =
                List.length
                  (List.filter
                     (fun other -> Array.for_all2 (fun a o -> (not a) || o) set other)
                     b.subsets)
              in
              List.iteri
                (fun i set ->
                  match b.best with
                  | Some (best, _) when (count best, within best) >= (count set, within set) -> ()
                  | _ -> b.best <- Some (set, i))
                b.subsets;
              b.pending_models <- (match b.best with Some _ -> b.sizes | None -> []));
            go ()
        | [], n :: rest -> (
            b.pending_models <- rest;
            match b.best with
            | None -> `Done
            | Some (set, _) ->
                let active =
                  Array.of_list (List.filteri (fun i _ -> set.(i)) (Array.to_list b.axioms))
                in
                (match
                   models ~meter:b.meter ~limit:(task_cap ()) ~rng:b.rng ~count:b.per_size
                     ~known:b.known b.signature active n
                 with
                | exception Exhausted -> ()
                | ms -> b.found <- List.rev_append ms b.found);
                go ())
        | [], [] -> `Done
    in
    match go () with `More -> None | `Done -> Some (pool_of b)

(* Whole pool at once (tests and offline tools). *)
let pool ?sizes ?per_size ?(budget = 20_000_000) signature axioms =
  let b = builder ?sizes ?per_size ~budget signature axioms in
  let rec go () = match advance b ~quota:max_int with Some p -> p | None -> go () in
  go ()

(* Counter-model search: a structure of size [sizes] satisfying [axioms] and
   [f], if the SAT search finds one within [budget] steps (charged to
   [meter]). Sizes are tried in order. *)
let find_model ?(sizes = [ 1; 2; 3; 4; 5; 6 ]) ~budget ?meter signature axioms f =
  if Signature.is_unrestricted signature then None
  else
    let local = Semantic.meter () in
    let all = Array.of_list (axioms @ [ f ]) in
    let rec go = function
      | [] -> None
      | n :: rest -> (
          if local.steps >= budget then None
          else
            let known = Hashtbl.create 1 and rng = Random.State.make [| n |] in
            match
              models ~iso:false ~meter:local ~limit:budget ~rng ~count:1 ~known signature all n
            with
            | exception Exhausted -> None
            | m :: _ -> Some m
            | [] -> go rest)
    in
    let found = go sizes in
    Option.iter (fun (c : Semantic.meter) -> c.steps <- c.steps + local.steps) meter;
    found
