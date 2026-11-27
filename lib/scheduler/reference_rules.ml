(* A deliberately simple, persistent unifier and inference catalogue. No use of
   the search Unify, Calculus, Clause, indices, ordering or redundancy filters. *)
open Wire

let rec apply sigma = function
  | V v as t -> ( match List.assoc_opt v sigma with None -> t | Some t -> apply sigma t)
  | Fn (f, ts) -> Fn (f, List.map (apply sigma) ts)

let rec occurs v = function V w -> v = w | Fn (_, ts) -> List.exists (occurs v) ts

let unify ~guard equations =
  let rec solve sigma = function
    | [] -> Some (List.map (fun (v, t) -> (v, apply sigma t)) sigma)
    | (s, t) :: rest -> (
        guard ();
        let s = apply sigma s and t = apply sigma t in
        if s = t then solve sigma rest
        else
          match (s, t) with
          | V v, t | t, V v -> if occurs v t then None else solve ((v, t) :: sigma) rest
          | Fn (f, ss), Fn (g, ts) when f = g && List.length ss = List.length ts ->
              solve sigma (List.combine ss ts @ rest)
          | _ -> None)
  in
  solve [] equations

let equations a b =
  match (a, b) with
  | P (p, xs), P (q, ys) when p = q && List.length xs = List.length ys -> [ List.combine xs ys ]
  | D (p, xs), D (q, ys) when p = q && List.length xs = List.length ys -> [ List.combine xs ys ]
  | E (s, t), E (u, v) -> [ [ (s, u); (t, v) ]; [ (s, v); (t, u) ] ]
  | _ -> []

let rec scope_term s = function
  | V (_, v) -> V (s, v)
  | Fn (f, ts) -> Fn (f, List.map (scope_term s) ts)

let scope s l =
  {
    l with
    atom =
      (match l.atom with
      | P (p, ts) -> P (p, List.map (scope_term s) ts)
      | D (p, ts) -> D (p, List.map (scope_term s) ts)
      | E (x, y) -> E (scope_term s x, scope_term s y));
  }

let positions ~guard literal visit =
  let rec term revpath t =
    guard ();
    visit (List.rev revpath) t;
    match t with V _ -> () | Fn (_, ts) -> List.iteri (fun i -> term (i :: revpath)) ts
  in
  let ts = match literal.atom with P (_, ts) | D (_, ts) -> ts | E (x, y) -> [ x; y ] in
  List.iteri (fun i -> term [ i ]) ts

exception Chosen of step

let choose ~guard ~inputs ~steps index =
  let remaining = ref index and id = List.length steps in
  let emit rule =
    guard ();
    match Kernel.derive ~inputs ~steps rule with
    | Error _ -> ()
    | Ok clause ->
        if !remaining = 0 then raise (Chosen { id; clause; rule });
        decr remaining
  in
  let matched eqs make =
    match unify ~guard eqs with None -> () | Some sigma -> emit (make sigma)
  in
  try
    (* Ordering is part of the checkpoint format. Inferences precede inputs;
       appending axioms therefore never changes an old script's choices. *)
    List.iter
      (fun (p : step) ->
        guard ();
        let xs = List.map (scope 1) p.clause in
        List.iteri
          (fun i l ->
            (match (l.positive, l.atom) with
            | false, E (s, t) -> matched [ (s, t) ] (fun sigma -> Equality_resolve (p.id, i, sigma))
            | _ -> ());
            List.iteri
              (fun j r ->
                if i < j && l.positive = r.positive then
                  List.iter
                    (fun eqs -> matched eqs (fun sigma -> Factor (p.id, i, j, sigma)))
                    (equations l.atom r.atom))
              xs)
          xs)
      steps;
    List.iter
      (fun (p : step) ->
        List.iter
          (fun (q : step) ->
            guard ();
            let xs = List.map (scope 1) p.clause and ys = List.map (scope 2) q.clause in
            List.iteri
              (fun i l ->
                List.iteri
                  (fun j r ->
                    if l.positive <> r.positive then
                      List.iter
                        (fun eqs -> matched eqs (fun sigma -> Resolve (p.id, i, q.id, j, sigma)))
                        (equations l.atom r.atom))
                  ys)
              xs;
            List.iteri
              (fun i l ->
                match (l.positive, l.atom) with
                | true, E (s, t) ->
                    List.iter
                      (fun (reverse, lhs) ->
                        List.iteri
                          (fun j r ->
                            positions ~guard r (fun path subterm ->
                                matched
                                  [ (lhs, subterm) ]
                                  (fun sigma ->
                                    Paramodulate (p.id, i, reverse, q.id, j, path, sigma))))
                          ys)
                      [ (false, s); (true, t) ]
                | _ -> ())
              xs)
          steps)
      steps;
    List.iter (fun (a, cs) -> List.iteri (fun i _ -> emit (Input (a, i))) cs) inputs;
    None
  with Chosen step -> Some step
