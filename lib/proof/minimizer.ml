type result = { certificate : Wire.certificate; attempts : int; inconclusive : int }

let clauses ~shrink_limit ~(config : Engine.config) theory certificate =
  let current = ref (Proof.prune certificate) and attempts = ref 0 and inconclusive = ref 0 in
  let candidates = !current.Wire.axioms in
  List.iter
    (fun (candidate : Wire.axiom) ->
      if List.exists (fun (a : Wire.axiom) -> a.axiom_id = candidate.axiom_id) !current.axioms then (
        incr attempts;
        let engine = Engine.create config in
        List.iter (Engine.add_axiom engine)
          (List.filter (fun (a : Wire.axiom) -> a.axiom_id <> candidate.axiom_id) !current.axioms);
        Engine.finish engine;
        match Engine.certificate engine ~theory:(Theory.name theory) with
        | None -> incr inconclusive
        | Some c -> (
            match Kernel.check theory c with
            | Ok _ -> current := c
            | Error e -> failwith ("Minimizer replay: " ^ e))))
    candidates;
  let deadline = Telemetry.now () +. config.limits.seconds in
  let remaining = ref shrink_limit in
  let rec shrink () =
    let progress = ref false in
    List.iter
      (fun (axiom : Wire.axiom) ->
        match axiom.origin with
        | Instance (schema, phi) ->
            let rec try_candidates stream =
              let seconds = deadline -. Telemetry.now () in
              if !remaining > 0 && seconds > 0. && not !progress then
                match stream () with
                | Seq.Nil -> ()
                | Seq.Cons (change, rest) ->
                    decr remaining;
                    incr attempts;
                    let replacement =
                      Theory.instantiate theory ~id:axiom.axiom_id schema
                        (Wire.import (Theory.arena theory) change.Mutation.formula)
                    in
                    let engine =
                      Engine.create { config with limits = { config.limits with seconds } }
                    in
                    List.iter
                      (fun (a : Wire.axiom) ->
                        Engine.add_axiom engine
                          (if a.axiom_id = axiom.axiom_id then replacement else a))
                      !current.axioms;
                    Engine.finish engine;
                    (match Engine.certificate engine ~theory:(Theory.name theory) with
                    | Some c when Result.is_ok (Kernel.check theory c) ->
                        current := c;
                        progress := true
                    | _ -> incr inconclusive);
                    try_candidates rest
            in
            try_candidates (Mutation.shrinks phi)
        | _ -> ())
      !current.axioms;
    if !progress then shrink ()
  in
  shrink ();
  { certificate = !current; attempts = !attempts; inconclusive = !inconclusive }

let run ?(shrink_limit = 32) ~(config : Engine.config) theory certificate =
  if shrink_limit < 0 then invalid_arg "negative condition shrink limit";
  if (not (Float.is_finite config.limits.seconds)) || config.limits.seconds < 0. then
    invalid_arg "minimizer time budget must be finite and nonnegative";
  (match Kernel.check theory certificate with
  | Ok _ -> ()
  | Error e -> invalid_arg ("Minimizer: invalid certificate: " ^ e));
  match certificate.Wire.natural with
  | None -> clauses ~shrink_limit ~config theory certificate
  | Some code ->
      let started = Telemetry.now () in
      let guard () =
        if Telemetry.now () -. started >= config.limits.seconds then raise Natural.Stop
      in
      let accept code =
        Result.is_ok (Kernel.check ~guard theory { certificate with natural = Some code })
      in
      let code, attempts, inconclusive = Natural.shrink ~guard ~accept theory code in
      { certificate = { certificate with natural = Some code }; attempts; inconclusive }
