(** All workers use the same operations. Rewards change their scheduling, never the inference rules
    or the meaning of a clause. The oldest ready operation gets a reserved turn; unsuccessful probes
    remain provisional. *)
type operation = Infer | Split | Ground | Synthesize | Enumerate

type arm = { mutable runs : int; mutable reward : float; mutable last : int }
type t = { arms : arm array; mutable turns : int }

let index = function Infer -> 0 | Split -> 1 | Ground -> 2 | Synthesize -> 3 | Enumerate -> 4
let create () = { arms = Array.init 5 (fun _ -> { runs = 0; reward = 0.; last = -1 }); turns = 0 }

let choose t ready =
  let score operation =
    let a = t.arms.(index operation) in
    if a.runs = 0 then infinity
    else a.reward +. sqrt (2. *. log (float (t.turns + 2)) /. float a.runs)
  in
  let better a b =
    if t.turns mod 8 = 7 then t.arms.(index a).last < t.arms.(index b).last else score a > score b
  in
  match ready with
  | [] -> None
  | first :: rest ->
      Some
        (List.fold_left
           (fun best candidate -> if better candidate best then candidate else best)
           first rest)

let observe t operation ~gain ~cost =
  let a = t.arms.(index operation) in
  let reward = float (max 0 gain) /. sqrt (float (1 + max 0 cost)) in
  a.reward <- (if a.runs = 0 then reward else (0.8 *. a.reward) +. (0.2 *. reward));
  a.runs <- a.runs + 1;
  a.last <- t.turns;
  t.turns <- t.turns + 1
