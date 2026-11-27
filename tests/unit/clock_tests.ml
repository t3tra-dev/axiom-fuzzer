open Axiom_fuzzer
open Test_support

(* Clock and deadline tests. The fork tests run first: OCaml 5 forbids
   Unix.fork once another Domain has been spawned, and this executable never
   spawns one. Wall-time bounds are loose (machines are shared); the exact
   lateness bound is checked in guard calls, which does not depend on load. *)

(* An unsatisfiable-looking but non-terminating input: the successor chain
   p(a), p(s(a)), ... never closes, so only a limit stops the search. *)
let endless () = Tptp.parse "fof(a,axiom,p(a)). fof(s,axiom,![X]:(p(X)=>p(s(X))))."

let timed_config seconds =
  {
    config with
    max_instances = 0;
    engine =
      {
        config.engine with
        limits =
          { Engine.seconds; max_given = max_int; max_generated = max_int; max_retained = max_int };
      };
  }

(* Run [child] in a fork(2) child and require exit status 0 within [timeout]
   seconds of wall time; a child that hangs is killed and fails the test. *)
let in_child ~timeout child =
  match Unix.fork () with
  | 0 ->
      let code = try if child () then 0 else 1 with _ -> 2 in
      Unix._exit code
  | pid ->
      let give_up = Telemetry.now () +. timeout in
      let rec wait () =
        match Unix.waitpid [ Unix.WNOHANG ] pid with
        | 0, _ ->
            if Telemetry.now () > give_up then (
              Unix.kill pid Sys.sigkill;
              ignore (Unix.waitpid [] pid);
              failwith "forked child did not stop (frozen deadline?)")
            else (
              Unix.sleepf 0.005;
              wait ())
        | _, Unix.WEXITED 0 -> ()
        | _, Unix.WEXITED n -> failwith (Printf.sprintf "forked child failed with status %d" n)
        | _, _ -> failwith "forked child was signalled"
      in
      wait ()

let wall f =
  let before = Telemetry.now () in
  let x = f () in
  (x, Telemetry.now () -. before)

(* Count the checks that returned false although a precise read just before
   the call was already past the limit. *)
let late_checks ?(pause = 0.) seconds =
  let now = Telemetry.now_ns () in
  let d = Deadline.create ~now seconds and limit = now + Float.to_int (seconds *. 1e9) in
  let late = ref 0 and checks = ref 0 in
  let rec loop () =
    let before = Telemetry.now_ns () in
    incr checks;
    if not (Deadline.expired d) then (
      if before >= limit then incr late;
      if pause > 0. then Unix.sleepf pause;
      loop ())
  in
  loop ();
  (!late, !checks)

let tests =
  [
    ( "a deadline created before fork(2) still expires in the child",
      fun () ->
        let d = Deadline.create 0.05 in
        in_child ~timeout:10. (fun () ->
            let started = Telemetry.now () in
            while not (Deadline.expired d) do
              ()
            done;
            Telemetry.now () -. started < 2.) );
    ( "an engine time limit stops the search in a forked child before any Domain",
      fun () ->
        in_child ~timeout:20. (fun () ->
            let r, seconds = wall (fun () -> Scheduler.run (timed_config 0.1) (endless ())) in
            r.certificate = None
            && String.equal r.reason "time limit"
            && seconds >= 0.1 && seconds < 5.) );
    ( "the clock is monotonic and both readers agree",
      fun () ->
        let previous = ref (Telemetry.now_ns ()) in
        for _ = 1 to 100_000 do
          let now = Telemetry.now_ns () in
          check (now >= !previous) "monotonic clock went backwards";
          previous := now
        done;
        let ns = Telemetry.now_ns () and s = Telemetry.now () in
        check
          (Float.abs (s -. (Float.of_int ns *. 1e-9)) < 0.01)
          "second and nanosecond clocks disagree";
        let before = Telemetry.now () in
        Unix.sleepf 0.02;
        check (Telemetry.now () -. before >= 0.019) "clock did not advance across a 20 ms sleep" );
    ( "clock reads and deadline checks do not allocate",
      fun () ->
        let d = Deadline.create 1e6 in
        let before = Gc.minor_words () in
        let sum = ref 0 in
        for _ = 1 to 100_000 do
          if Deadline.expired d then incr sum;
          sum := !sum + (Telemetry.now_ns () land 1);
          if Telemetry.now () < 0. then incr sum
        done;
        let words = Gc.minor_words () -. before in
        check (words < 64.) (Printf.sprintf "clock path allocated %.0f words" words);
        ignore (Sys.opaque_identity !sum) );
    ( "zero, negative and NaN budgets are expired at the first check",
      fun () ->
        List.iter
          (fun s ->
            let d = Deadline.create s in
            check (Deadline.expired d) "non-positive budget did not stop immediately";
            check (Deadline.expired_now d) "expiry is not sticky";
            equal (Deadline.remaining d) 0. "expired deadline has time left")
          [ 0.; -1.; Float.nan ] );
    ( "huge budgets never expire",
      fun () ->
        let d = Deadline.create 1e12 in
        for _ = 1 to 10_000 do
          check (not (Deadline.expired d)) "a 1e12 s budget expired"
        done;
        check (Deadline.remaining d > 1e9) "remaining time of a huge budget" );
    ( "dense checks fire at most 15 calls after the limit",
      fun () ->
        let late, checks = late_checks 0.02 in
        check (checks > 16) "fixture made too few checks";
        check (late <= 15) (Printf.sprintf "deadline fired %d checks late" late) );
    ( "sparse checks read the clock on every call",
      fun () ->
        let late, _ = late_checks ~pause:0.001 0.01 in
        check (late <= 1) (Printf.sprintf "sparse deadline fired %d checks late" late) );
    ( "a check after a long pause sees the expired deadline",
      fun () ->
        let d = Deadline.create 0.01 in
        for _ = 1 to 1000 do
          ignore (Deadline.expired d)
        done;
        Unix.sleepf 0.03;
        (* The stride is at most 16, so 16 further checks must read the clock. *)
        let fired = ref false in
        for _ = 1 to 16 do
          if Deadline.expired d then fired := true
        done;
        check !fired "deadline missed after a pause" );
    ( "after a dense phase, sparse checks fire within 15 calls and a precise check at once",
      fun () ->
        (* Dense phase: the stride grows to 16. Then calls are 2 ms apart. The
           amortized check may pass up to 15 sparse calls before it reads the
           clock again (the bound is in calls, not in time); expired_now never
           passes a call after the limit. *)
        let gap = 0.002 in
        let run precise =
          let now = Telemetry.now_ns () in
          let budget = 0.012 in
          let d = Deadline.create ~now budget and limit = now + Float.to_int (budget *. 1e9) in
          (* The dense phase ends 1 ms before the limit. *)
          while Telemetry.now_ns () < limit - 1_000_000 do
            ignore (Deadline.expired d)
          done;
          let late = ref 0 and widest = ref 0 and previous = ref (Telemetry.now_ns ()) in
          let rec loop () =
            Unix.sleepf gap;
            let before = Telemetry.now_ns () in
            widest := max !widest (before - !previous);
            previous := before;
            let fired = if precise then Deadline.expired_now d else Deadline.expired d in
            if not fired then (
              if before >= limit then incr late;
              loop ())
            else (!late, Float.of_int (before - limit) *. 1e-9, Float.of_int !widest *. 1e-9)
          in
          loop ()
        in
        let late, lateness, widest = run false in
        check (late <= 15) (Printf.sprintf "amortized check fired %d sparse calls late" late);
        check
          (lateness <= (15. *. widest) +. 0.005)
          (Printf.sprintf "amortized lateness %.1f ms exceeds 15 gaps of %.1f ms" (lateness *. 1e3)
             (widest *. 1e3));
        let late_now, _, _ = run true in
        equal late_now 0 "precise check passed a call after the limit";
        Printf.printf "    dense-to-sparse: %d late calls, %.1f ms late (widest gap %.1f ms)\n%!"
          late (lateness *. 1e3) (widest *. 1e3) );
    ( "an engine step that starts after the limit stops before doing any work",
      fun () ->
        let theory = endless () in
        let limits = { (timed_config 0.05).engine.limits with Engine.seconds = 0.05 } in
        let e = Engine.create { (timed_config 0.05).engine with limits } in
        List.iter (Engine.add_axiom e) (Theory.fixed theory);
        (* Dense guard calls first, so the amortized stride is long. *)
        let started = Telemetry.now () in
        while Telemetry.now () -. started < 0.03 && e.stopped = None && Engine.has_work e do
          Engine.step e
        done;
        check (e.stopped = None) "fixture stopped before the pause";
        Unix.sleepf 0.04;
        let generated = e.metrics.generated and given = e.metrics.given in
        Engine.step e;
        equal e.stopped (Some "time limit") "step after the limit did not stop";
        equal
          (e.metrics.generated, e.metrics.given)
          (generated, given) "step after the limit generated or selected clauses" );
    ( "an in-process engine time limit stops close to the budget",
      fun () ->
        let r, seconds = wall (fun () -> Scheduler.run (timed_config 0.2) (endless ())) in
        check (r.certificate = None) "endless input was refuted";
        equal r.reason "time limit" "search stopped for another reason";
        check (seconds >= 0.2) "search stopped before its budget";
        check (seconds < 2.) (Printf.sprintf "search overshot its budget: %.3f s" seconds);
        Printf.printf "    engine stop after %.2f ms over a 200 ms budget\n%!"
          ((seconds -. 0.2) *. 1e3) );
  ]

let () = run tests
