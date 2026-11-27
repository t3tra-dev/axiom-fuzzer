open Wire

exception No_match

let term ?(guard = fun () -> ()) env p t =
  let rec same s t =
    guard ();
    s == t
    ||
    match (s, t) with
    | V x, V y -> Sym.var x y
    | Fn (f, xs), Fn (g, ys) ->
        Sym.equal f g && List.compare_lengths xs ys = 0 && List.for_all2 same xs ys
    | _ -> false
  in
  let rec go env p t =
    guard ();
    match (p, t) with
    | V v, t -> (
        match Sym.assoc_opt v env with
        | None -> (v, t) :: env
        | Some u -> if same u t then env else raise No_match)
    | Fn (f, ps), Fn (g, ts) when Sym.equal f g && List.compare_lengths ps ts = 0 ->
        List.fold_left2 go env ps ts
    | _ -> raise No_match
  in
  go env p t

(* A necessary condition for [term env p t] to succeed: [t] has [p]'s function symbols, with the
   same numbers of arguments, at all of [p]'s non-variable positions. Repeated variables of [p] are
   not compared, so it may hold where [term] fails, never the other way round. It allocates nothing
   and calls no guard, so a caller can reject a pattern before it pays for a matching attempt. *)
let rec matchable p t =
  match p with
  | V _ -> true
  | Fn (f, ps) -> (
      match t with Fn (g, ts) -> Sym.equal f g && matchable_list ps ts | V _ -> false)

and matchable_list ps ts =
  match (ps, ts) with
  | [], [] -> true
  | p :: ps, t :: ts -> matchable p t && matchable_list ps ts
  | _ -> false

let atom ?(guard = fun () -> ()) env p t =
  match (p, t) with
  | P (f, ps), P (g, ts) when Sym.name f g && List.compare_lengths ps ts = 0 ->
      List.fold_left2 (term ~guard) env ps ts
  | D (f, ps), D (g, ts) when Sym.def f g && List.compare_lengths ps ts = 0 ->
      List.fold_left2 (term ~guard) env ps ts
  | E (p, q), E (s, t) -> term ~guard (term ~guard env p s) q t
  | _ -> raise No_match

let subsumes ?(budget = 2000) ?(guard = fun () -> ()) ?(on_exhausted = fun () -> ()) c d =
  (* Target terms are rigid values, never substituted or matched as patterns.
     The environment has only pattern keys, so no scoped copies are needed.
     This is multiset subsumption: distinct pattern literals need distinct
     target literals. Set subsumption would let p(X) | p(Y) delete its own
     factor p(X) (and every clause containing an instance of p(X)), although
     the factor is not redundant; saturation then stops without a refutation. *)
  let exception Exhausted in
  let left = ref budget and work = ref 0 in
  let tick () =
    incr work;
    if !work mod 64 = 0 then guard ()
  in
  guard ();
  List.compare_lengths c d <= 0
  &&
  let targets = Tbl.Feature.create 8 in
  List.iter
    (fun ((_, l) as target) ->
      tick ();
      let key = Clause.key l in
      Tbl.Feature.replace targets key
        (target :: Option.value ~default:[] (Tbl.Feature.find_opt targets key)))
    (List.rev (List.mapi (fun i l -> (i, l)) d));
  let patterns =
    List.map
      (fun p ->
        let candidates = Option.value ~default:[] (Tbl.Feature.find_opt targets (Clause.key p)) in
        (p, candidates, List.length candidates))
      c
    |> List.stable_sort (fun (_, _, n) (_, _, m) -> compare n m)
  in
  let used = Array.make (List.length d) false in
  let rec search env = function
    | [] -> true
    | (p, candidates, _) :: ps ->
        List.exists
          (fun (i, t) ->
            (not used.(i))
            &&
            (if !left <= 0 then raise Exhausted;
             decr left;
             tick ();
             used.(i) <- true;
             let try_atom target =
               try search (atom ~guard:tick env p.atom target) ps with No_match -> false
             in
             let found =
               try_atom t.atom || match t.atom with E (s, t) -> try_atom (E (t, s)) | _ -> false
             in
             used.(i) <- false;
             found))
          candidates
  in
  try search [] patterns
  with Exhausted ->
    on_exhausted ();
    false

(* Subsumption resolution matches only the side premise. Target variables stay
   rigid: instantiating the target would not justify deleting its old clause.
   Non-pivot equalities use their written orientation, so ordinary Resolve and
   normalization suffice to certify the shortened clause without a new rule. *)
let resolve ?(budget = 2048) ?(guard = fun () -> ()) ?(on_exhausted = fun () -> ()) (side : step)
    (target : step) =
  let exception Exhausted in
  let left = ref budget in
  let tick () =
    guard ();
    decr left;
    if !left < 0 then raise Exhausted
  in
  let xs = Clause.scope 1 side.clause and ys = Clause.scope 2 target.clause in
  let rec match_rest env = function
    | [] -> Some env
    | (p, candidates) :: rest ->
        List.find_map
          (fun l ->
            tick ();
            try match_rest (atom ~guard:tick env p.atom l.atom) rest with No_match -> None)
          candidates
  in
  try
    List.mapi (fun j l -> (j, l)) ys
    |> List.find_map (fun (j, l) ->
        let remaining = Clause.remove j ys in
        List.mapi (fun i p -> (i, p)) xs
        |> List.find_map (fun (i, p) ->
            tick ();
            if p.positive = l.positive then None
            else
              let patterns =
                Clause.remove i xs
                |> List.map (fun r ->
                    ( r,
                      List.filter
                        (fun q ->
                          tick ();
                          Int.equal (Clause.key q) (Clause.key r))
                        remaining ))
                |> List.stable_sort (fun (_, a) (_, b) -> compare (List.length a) (List.length b))
              in
              let attempt pivot =
                try
                  let env = atom ~guard:tick [] p.atom pivot in
                  Option.map
                    (fun sigma -> (remaining, Resolve (side.id, i, target.id, j, sigma)))
                    (match_rest env patterns)
                with No_match -> None
              in
              match attempt l.atom with
              | Some _ as result -> result
              | None -> ( match l.atom with E (s, t) -> attempt (E (t, s)) | _ -> None)))
  with Exhausted ->
    on_exhausted ();
    None
