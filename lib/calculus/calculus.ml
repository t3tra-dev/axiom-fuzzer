open Wire

(* [flags]: maximality before substitution, kept for unselected clauses of
   strategies with maximal candidates. *)
type memo = { choice : int list option; flags : bool array option }

type t = {
  unifier : Unify.t;
  mutable attempts : int;
  mutable successes : int;
  variable_positions : bool;
  ordered : bool;
  selection : bool;
  selected : int list option Tbl.Int.t;
      (** Selections fixed by the lookahead (or by tests); they override the default. *)
  strategy : Strategy.t;
  order : Ordering.order;
  memo : (int, memo) Hashtbl.t;
      (** Default selections of strategies whose selection compares literals. A pure function of the
          clause, so pruning it never changes a choice. *)
  mutable ordering_rejected : int;
  mutable guard : unit -> unit;
  mutable observe : (string -> rule -> unit) option;
  mutable e_code : (Ordering.head * int -> int) option;
      (** E's symbol codes, set for a heuristic with E's literal order ([Heuristic.loop.lit_order]):
          its selection functions then take the first of equally good literals in E's order
          ({!Eselection.e_rank}). *)
}

let create ?(variable_positions = false) ?(ordered = false) ?(selection = true)
    ?(strategy = Strategy.production) ?(order = Ordering.standard) ?(memo = Hashtbl.create 32) arena
    =
  {
    unifier = Unify.create arena;
    attempts = 0;
    successes = 0;
    variable_positions;
    ordered;
    selection;
    selected = Tbl.Int.create 32;
    strategy;
    order;
    memo;
    ordering_rejected = 0;
    guard = (fun () -> ());
    observe = None;
    e_code = None;
  }

let entry c (p : step) =
  match Hashtbl.find_opt c.memo p.id with
  | Some e -> e
  | None ->
      let flags = lazy (Ordering.maximal_flags ~order:c.order p.clause) in
      let choice =
        match c.strategy.heuristic with
        | Some { vampire = Some v; _ } ->
            (* A Vampire selection function: always a nonempty set of literals. *)
            let xs = Array.of_list p.clause in
            let id key =
              match c.order.vampire with
              | Some o -> Option.value ~default:max_int (Hashtbl.find_opt o.ids key)
              | None -> 0
            in
            Some
              (Vampire.select v ~id
                 ~greater:(fun i j -> Ordering.literal_greater ~order:c.order xs.(i) xs.(j))
                 p.clause)
        | Some h ->
            (* A ported E selection function; the "P" variants select several literals. *)
            Eselection.select ~order:c.order
              ?rank:
                (match c.e_code with
                | None -> None
                | Some code -> Some (Eselection.e_rank ~code p.clause))
              h.selection p.clause
        | None ->
            Option.map
              (fun i -> [ i ])
              (match c.strategy.selection with
              | Strategy.First_negative -> Ordering.first_negative p.clause
              | Max_complex_avoid_pos_pred | Max_complex_avoid_pos_pred_lookahead ->
                  if List.for_all (fun l -> l.positive) p.clause then None
                  else Ordering.e_selection_with (Lazy.force flags) p.clause
              | Max_complex -> Ordering.best_negative p.clause
              | Vampire_best_10 -> Ordering.vampire_best_10 p.clause)
      in
      let flags =
        if c.strategy.maximal_candidates && choice = None then Some (Lazy.force flags) else None
      in
      let e = { choice; flags } in
      Hashtbl.replace c.memo p.id e;
      e

(* The strategy's selection before any lookahead revision. Production selects
   the first negative literal without a memo. *)
let default_selection c (p : step) =
  match c.strategy with
  | { selection = First_negative; maximal_candidates = false; heuristic = None; _ } ->
      Option.map (fun i -> [ i ]) (Ordering.first_negative p.clause)
  | _ -> (entry c p).choice

let selected c (p : step) =
  if not c.selection then None
  else
    match Tbl.Int.find_opt c.selected p.id with
    | Some choice -> choice
    | None -> default_selection c p

(* Keep memoized selections only for live premises. *)
let prune c ~keep = Hashtbl.filter_map_inplace (fun id x -> if keep id then Some x else None) c.memo
let forget c id = Hashtbl.remove c.memo id

let potential c chosen i =
  (not c.ordered) || match chosen with None -> true | Some js -> List.mem i js

(* Literal positions of [p] that may take part in an inference under the
   selection [chosen]. Without a selection, a maximal-candidate strategy drops
   the literals that another literal already exceeds before substitution: the
   order is stable under substitution, so they fail every eligibility check. *)
let candidate c (p : step) chosen =
  match chosen with
  | None when c.ordered && c.strategy.maximal_candidates ->
      let flags =
        match (entry c p).flags with
        | Some flags -> flags
        | None -> Ordering.maximal_flags ~order:c.order p.clause
      in
      fun i -> flags.(i)
  | _ -> potential c chosen

let candidates c p = candidate c p (selected c p)

(* A positive literal of a clause with a selection, under a ported E heuristic: one of
   E's "P" selection functions selected it (Eselection). E paramodulates into such a
   literal but never from it (ccl_overlap_index.c:518 and :554, ccl_paramod.c:1170), so it
   is no superposition source and, since E resolves by paramodulating P(s) = $true into
   ~P(t), no positive resolution premise. Production's lookahead may also select a
   positive literal; that one keeps the full calculus. *)
let vampire c = match c.strategy.heuristic with Some { vampire = Some v; _ } -> Some v | _ -> None

let into_only c chosen (l : literal) =
  c.ordered && l.positive && chosen <> None
  && match c.strategy.heuristic with Some { vampire = None; _ } -> true | _ -> false

(* [source]: the literal is the positive premise of a resolution or the equation of a
   superposition. *)
let eligible c ?(strict = false) ?(source = false) chosen xs i app =
  (not c.ordered)
  ||
  match (vampire c, chosen) with
  | Some v, Some js ->
      (* Vampire's literal maximality after-check (literal_maximality_aftercheck, on by default):
         with several selected literals, no other selected literal may exceed this one after the
         substitution; one selected literal and an incomplete selection are not checked. *)
      List.mem i js
      && (List.compare_length_with js 1 = 0
         || Vampire.incomplete v
         || Ordering.eligible ~order:c.order ~selection:false ~strict
              ~among:(fun j -> List.mem j js)
              xs i app)
  | _, Some js ->
      List.mem i js
      &&
      let l = List.nth xs i in
      (not l.positive)
      ||
      if c.strategy.heuristic = None then
        Ordering.eligible ~order:c.order ~selection:false ~strict xs i app
      else
        (* E's LiteralCompare (ccl_eqn.c:2558) ranks selected literals above unselected ones
           and makes selected literals of opposite sign incomparable: only another selected
           positive literal can exceed a P-selected one. *)
        (not source)
        && Ordering.eligible ~order:c.order ~selection:false ~strict
             ~among:(fun j -> List.mem j js && (List.nth xs j).positive)
             xs i app
  | _, None -> Ordering.eligible ~order:c.order ~selection:false ~strict xs i app

let equations a b =
  match (a, b) with
  | P (p, xs), P (q, ys) when Sym.name p q && List.length xs = List.length ys ->
      [ List.combine xs ys ]
  | D (p, xs), D (q, ys) when Sym.def p q && List.length xs = List.length ys ->
      [ List.combine xs ys ]
  | E (s, t), E (u, v) -> [ [ (s, u); (t, v) ]; [ (s, v); (t, u) ] ]
  | _ -> []

let report c stage rule sigma = Option.iter (fun f -> f stage (rule sigma)) c.observe

let solve c ~rule ~allowed eqs k =
  c.guard ();
  c.attempts <- c.attempts + 1;
  report c "attempt" rule [];
  let previous = c.successes in
  Unify.solve c.unifier eqs
    ~accept:(fun app ->
      c.successes <- c.successes + 1;
      if allowed app then true
      else (
        c.ordering_rejected <- c.ordering_rejected + 1;
        report c "ordering_rejected" rule [];
        false))
    (fun sigma app ->
      report c "conclusion" rule sigma;
      k sigma app);
  if c.successes = previous then report c "unification_rejected" rule []

(* [Heuristic.loop.e_calculus]: E's generating inferences only. *)
let e_calculus c = match c.strategy.heuristic with Some h -> h.loop.e_calculus | None -> false

let unary c (p : step) emit =
  let e = e_calculus c in
  let xs = Clause.scope 1 p.clause and chosen = selected c p in
  let pp = candidate c p chosen in
  List.iteri
    (fun i l ->
      c.guard ();
      if pp i then (
        (match (l.positive, l.atom) with
        | false, E (s, t) ->
            solve c
              ~rule:(fun s -> Equality_resolve (p.id, i, s))
              ~allowed:(eligible c chosen xs i)
              [ (s, t) ]
              (fun sigma app ->
                emit
                  (List.map (Clause.map_literal app) (Clause.remove i xs))
                  (Equality_resolve (p.id, i, sigma)))
        | _ -> ());
        List.iteri
          (fun j r ->
            if
              match (vampire c, chosen) with
              | Some v, Some js ->
                  (* Vampire's factoring (Inferences/Factoring.cpp): one selected literal and any
                     other one, both positive for selection, never equations; a pair of selected
                     literals once. *)
                  i <> j
                  && ((not (List.mem j js)) || i < j)
                  && l.positive = r.positive
                  && (match l.atom with E _ -> false | _ -> true)
                  && not (Vampire.negative_for_selection v l)
              | _ ->
                  (* E factors positive literals only (equality factoring). *)
                  i < j && l.positive = r.positive && ((not e) || l.positive)
            then
              List.iter
                (fun eqs ->
                  solve c
                    ~rule:(fun s -> Factor (p.id, i, j, s))
                    ~allowed:(eligible c chosen xs i) eqs
                    (fun sigma app ->
                      emit
                        (List.map (Clause.map_literal app) (Clause.remove j xs))
                        (Factor (p.id, i, j, sigma))))
                (equations l.atom r.atom))
          xs))
    xs

(* A cursor yields complete inference attempts. No unifier trail or arena handle
   survives a yield; the scoped Wire premises can be reused after collection. *)
type inference = (clause -> rule -> unit) -> unit

let indices n = Seq.unfold (fun i -> if i = n then None else Some (i, i + 1)) 0
let pairs xs ys = Seq.flat_map (fun x -> Seq.map (fun y -> (x, y)) ys) xs
let run cursor emit = Seq.iter (fun attempt -> attempt emit) cursor

(* Alternate complete attempts, never suspend a live unifier trail. *)
let rec interleave a b () =
  match a () with Seq.Nil -> b () | Seq.Cons (x, rest) -> Seq.Cons (x, interleave b rest)

(* Equality factoring can introduce a disequality, so it is scheduled rather
   than recursively eager. One cursor element is one oriented pair of equalities. *)
let equality_factor_cursor c (p : step) =
  if not c.ordered then Seq.empty
  else
    let xs = Clause.scope 1 p.clause and chosen = selected c p in
    let pp = candidate c p chosen in
    let xa = Array.of_list xs in
    Seq.flat_map
      (fun i ->
        c.guard ();
        let l = xa.(i) in
        match (pp i, l.positive, l.atom) with
        | true, true, E (s, t) ->
            Seq.flat_map
              (fun j ->
                let r = xa.(j) in
                match (i <> j, r.positive, r.atom) with
                | true, true, E (u, v) ->
                    pairs
                      (List.to_seq [ (false, s, t); (true, t, s) ])
                      (List.to_seq [ (false, u, v); (true, v, u) ])
                    |> Seq.map (fun ((reverse_i, lhs, rhs), (reverse_j, lhs', rhs')) emit ->
                        solve c
                          ~rule:(fun s -> Equality_factor (p.id, i, reverse_i, j, reverse_j, s))
                          ~allowed:(fun app ->
                            eligible c chosen xs i app
                            && Ordering.not_less_or_equal ~order:c.order (app lhs) (app rhs))
                          [ (lhs, lhs') ]
                          (fun sigma app ->
                            let result =
                              { positive = false; atom = E (rhs, rhs') } :: r :: Clause.remove i xs
                            in
                            emit
                              (List.map (Clause.map_literal app) result)
                              (Equality_factor (p.id, i, reverse_i, j, reverse_j, sigma))))
                | _ -> Seq.empty)
              (indices (Array.length xa))
        | _ -> Seq.empty)
      (indices (Array.length xa))

let equality_factor c p emit = run (equality_factor_cursor c p) emit

(* A position list is only a candidate filter. The same unification, ordering,
   proof construction and rollback paths serve indexed and exhaustive inference. *)
let resolve_cursor ?positions c (p : step) (q : step) =
  let xs = Clause.scope 1 p.clause and ys = Clause.scope 2 q.clause in
  let xa = Array.of_list xs and ya = Array.of_list ys in
  let pc = selected c p and qc = selected c q in
  let pp = candidate c p pc and qp = candidate c q qc in
  let e = e_calculus c in
  let pair i j emit =
    c.guard ();
    let l = xa.(i) and r = ya.(j) in
    if
      pp i && l.positive <> r.positive && qp j
      && (not (into_only c pc l))
      && (not (into_only c qc r))
      && not (e && match l.atom with E _ -> true | P _ | D _ -> false)
    then
      List.iter
        (fun eqs ->
          solve c
            ~rule:(fun s -> Resolve (p.id, i, q.id, j, s))
            ~allowed:(fun app ->
              eligible c ~strict:l.positive ~source:l.positive pc xs i app
              && eligible c ~strict:r.positive ~source:r.positive qc ys j app)
            eqs
            (fun sigma app ->
              emit
                (List.map (Clause.map_literal app) (Clause.remove i xs @ Clause.remove j ys))
                (Resolve (p.id, i, q.id, j, sigma))))
        (equations l.atom r.atom)
  in
  let positions =
    match positions with
    | Some ps -> List.to_seq ps
    | None -> pairs (indices (Array.length xa)) (indices (Array.length ya))
  in
  match vampire c with
  | Some { binary_resolution = false; _ } -> Seq.empty
  | _ -> Seq.map (fun (i, j) -> pair i j) positions

let resolve ?positions c p q emit = run (resolve_cursor ?positions c p q) emit

let paramodulate_cursor ?positions c (p : step) (q : step) =
  let pc = selected c p and qc = selected c q in
  let pp = candidate c p pc and qp = candidate c q qc in
  let rec source i = function
    | [] -> false
    | l :: rest ->
        (pp i && l.positive
        && (not (into_only c pc l))
        && match l.atom with E (s, t) -> s <> t | _ -> false)
        || source (i + 1) rest
  in
  if positions = Some [] || not (source 0 p.clause) then Seq.empty
  else
    let xs = Clause.scope 1 p.clause and ys = Clause.scope 2 q.clause in
    let xa = Array.of_list xs and ya = Array.of_list ys in
    let pair i reverse j path emit =
      c.guard ();
      let l = xa.(i) and target = ya.(j) in
      if pp i && qp j && not (into_only c pc l) then
        match (l.positive, l.atom) with
        | true, E (s, t) ->
            let lhs, rhs = if reverse then (t, s) else (s, t) in
            if lhs <> rhs then
              let subterm = Clause.at target path in
              if c.variable_positions || match subterm with V _ -> false | Fn _ -> true then
                solve c
                  ~rule:(fun s -> Paramodulate (p.id, i, reverse, q.id, j, path, s))
                  ~allowed:(fun app ->
                    let target_side =
                      if not c.ordered then true
                      else
                        match (target.atom, path) with
                        | E (x, y), 0 :: _ ->
                            Ordering.not_less_or_equal ~order:c.order (app x) (app y)
                        | E (x, y), 1 :: _ ->
                            Ordering.not_less_or_equal ~order:c.order (app y) (app x)
                        | _ -> true
                    in
                    (not c.ordered)
                    || Ordering.not_less_or_equal ~order:c.order (app lhs) (app rhs)
                       && target_side
                       && eligible c ~strict:true ~source:true pc xs i app
                       && eligible c ~strict:target.positive qc ys j app)
                  [ (lhs, subterm) ]
                  (fun sigma app ->
                    let target = Clause.put target path rhs in
                    let result = Clause.remove i xs @ Clause.replace j target ys in
                    emit
                      (List.map (Clause.map_literal app) result)
                      (Paramodulate (p.id, i, reverse, q.id, j, path, sigma)))
        | _ -> ()
    in
    let positions =
      match positions with
      | Some ps -> List.to_seq ps
      | None ->
          Seq.flat_map
            (fun i ->
              let l = xa.(i) in
              match (pp i, l.positive, l.atom) with
              | true, true, E (s, t) when s <> t && not (into_only c pc l) ->
                  Seq.flat_map
                    (fun reverse ->
                      Seq.flat_map
                        (fun j ->
                          if qp j then
                            Clause.positions ~variables:c.variable_positions ya.(j)
                            |> List.to_seq
                            |> Seq.map (fun (path, _) -> (i, reverse, j, path))
                          else Seq.empty)
                        (indices (Array.length ya)))
                    (List.to_seq [ false; true ])
              | _ -> Seq.empty)
            (indices (Array.length xa))
    in
    Seq.map (fun (i, reverse, j, path) -> pair i reverse j path) positions

let paramodulate ?positions c p q emit = run (paramodulate_cursor ?positions c p q) emit
