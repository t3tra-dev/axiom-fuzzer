open Axiom_fuzzer
open Test_support

let policy ?(lanes = 3) ?(e = 0) ?(members = []) ?(unit_work = 4) ?(measure = Slices.Steps)
    ?(sequence = Slices.Luby) ?(main_ratio = 1) ?(restart = true) ?(rounds = 0) ?(carry = false) ()
    =
  Slices.build
    {
      phases = lanes;
      restart;
      e;
      members;
      unit = unit_work;
      measure_spec = measure;
      sequence_spec = sequence;
      ratio = main_ratio;
      round_limit = rounds;
      carry_spec = carry;
    }

let policies =
  List.concat_map
    (fun lanes ->
      List.concat_map
        (fun main_ratio ->
          List.concat_map
            (fun sequence ->
              List.concat_map
                (fun restart ->
                  List.concat_map
                    (fun e ->
                      List.map
                        (fun rounds ->
                          policy ~lanes ~e ~unit_work:3 ~sequence ~main_ratio ~restart ~rounds ())
                        [ 0; 1; 4 ])
                    [ 0; 1; 3 ])
                [ true; false ])
            [ Slices.Luby; Slices.Geometric 2; Slices.Geometric 1 ])
        [ 1; 2; 5 ])
    [ 1; 2; 3; 7 ]

(* Small problems that need tens to hundreds of engine steps, so that queue
   phases reach the empty clause along different paths. *)
let problems =
  [
    ( "group-square",
      "cnf(left_identity,axiom,mult(e,X)=X). cnf(left_inverse,axiom,mult(inv(X),X)=e). \
       cnf(associativity,axiom,mult(mult(X,Y),Z)=mult(X,mult(Y,Z))). \
       cnf(square,axiom,mult(X,X)=e). cnf(goal,negated_conjecture,mult(a,b)!=mult(b,a))." );
    ( "chain",
      "cnf(c1,axiom,(~p(X)|q(f(X)))). cnf(c2,axiom,(~q(X)|r(g(X)))). cnf(c3,axiom,(~r(X)|s(X))). \
       cnf(c4,axiom,(~s(g(f(X)))|t(X))). cnf(c5,axiom,(~t(X)|~u(X))). cnf(c6,axiom,p(a)). \
       cnf(c7,axiom,(u(a)|v(a))). cnf(c8,axiom,(~v(X)|w(X))). cnf(c9,axiom,~w(a))." );
    ( "group-cube",
      "cnf(left_identity,axiom,mult(e,X)=X). cnf(left_inverse,axiom,mult(inv(X),X)=e). \
       cnf(associativity,axiom,mult(mult(X,Y),Z)=mult(X,mult(Y,Z))). \
       cnf(cube,axiom,mult(X,mult(X,X))=e). \
       cnf(goal,negated_conjecture,mult(a,mult(b,mult(a,mult(b,mult(a,b)))))!=e)." );
    ( "pigeons",
      "cnf(p1,axiom,(in(a,h1)|in(a,h2))). cnf(p2,axiom,(in(b,h1)|in(b,h2))). \
       cnf(p3,axiom,(in(c,h1)|in(c,h2))). cnf(x1,axiom,(~in(a,H)|~in(b,H))). \
       cnf(x2,axiom,(~in(a,H)|~in(c,H))). cnf(x3,axiom,(~in(b,H)|~in(c,H)))." );
    ( "lattice",
      "cnf(c,axiom,join(X,Y)=join(Y,X)). cnf(a,axiom,join(join(X,Y),Z)=join(X,join(Y,Z))). \
       cnf(i,axiom,join(X,X)=X). cnf(m,axiom,meet(X,Y)=meet(Y,X)). \
       cnf(ab1,axiom,join(X,meet(X,Y))=X). cnf(ab2,axiom,meet(X,join(X,Y))=X). \
       cnf(goal,negated_conjecture,meet(a,a)!=a)." );
  ]

let sliced ?(seconds = 5.) slices =
  {
    Scheduler.default_config with
    reference = false;
    guided = false;
    max_instances = 0;
    max_guided_instances = 0;
    slices = Some slices;
    engine =
      {
        Engine.default_config with
        limits =
          { Engine.seconds; max_given = max_int; max_generated = max_int; max_retained = max_int };
      };
  }

let solve slices text =
  let theory = Tptp.parse text in
  let r = Scheduler.portfolio (sliced slices) (fun () -> Theory.copy theory) in
  (theory, r, List.hd r.workers)

let is_prefix xs ys =
  let rec go = function
    | [], _ -> true
    | x :: xs, y :: ys -> x = y && go (xs, ys)
    | _ :: _, [] -> false
  in
  go (xs, ys)

(* Satisfiable and never saturated: every slice runs to its end. *)
let endless = "cnf(s,axiom,p(s(X))|~p(X)). cnf(z,axiom,p(z)). cnf(q,axiom,(q(X,Y)|~p(X)|~p(Y)))."

(* Satisfiable, with equality, non-unit clauses and a negated goal (non-abelian groups with p true
   and q false everywhere are models): neither engine of the share refutes it or saturates soon,
   so a run with a given-clause cap ends at a point fixed by the two searches alone. *)
let groups =
  "cnf(left_identity, axiom, mult(e, X) = X). cnf(left_inverse, axiom, mult(inv(X), X) = e). \
   cnf(associativity, axiom, mult(mult(X, Y), Z) = mult(X, mult(Y, Z))). cnf(not_commutative, \
   negated_conjecture, mult(a, b) != mult(b, a)). cnf(p_or_q, axiom, p(X) | q(X)). cnf(p_closed, \
   axiom, p(mult(X, Y)) | ~p(X)). cnf(not_both, axiom, ~q(e) | ~p(e))."

(* Everything the share's schedule decides or depends on, apart from wall-clock telemetry. *)
let share_fingerprint (r : Scheduler.result) =
  let w = List.hd r.workers in
  let s = w.slices in
  let engine (e : Engine.t) =
    ( e.config.strategy.name,
      e.metrics.given,
      e.metrics.generated,
      e.metrics.retained,
      e.metrics.checks,
      e.metrics.budget_checks,
      e.metrics.budget_digest,
      e.stopped )
  in
  ( (s.policy, s.main_slices, s.probe_slices, s.main_steps, s.probe_steps, s.main_work, s.probe_work),
    (s.probes_created, s.peak_live_probes, s.probe_given, s.probe_generated, s.probe_admitted),
    (s.winner, s.winner_slice),
    engine w.continuing,
    engine w.engine,
    r.certificate,
    r.reason )

(* A continuing engine for direct [Scheduler.sliced_search] calls whose slices
   are driven by [turn] instead of engine steps. *)
let direct ?(seconds = 5.) ?(limits = fun l -> l) ~text slices ~alive ~turn =
  let theory = Tptp.parse text in
  let config = sliced ~seconds slices in
  let config =
    { config with engine = { config.engine with limits = limits config.engine.limits } }
  in
  let main = Engine.create config.engine in
  Engine.prepare_ordering main (Theory.fixed theory);
  List.iter (Engine.add_axiom main) (Theory.fixed theory);
  let stats = Slices.stats slices and selected = ref main in
  Scheduler.sliced_search ~config ~worker_id:0
    ~cancelled:(fun () -> false)
    ~prepare:ignore ~fixed:(Theory.fixed theory) ~stats ~main
    ~main_alive:(fun () -> alive main)
    ~main_turn:(fun () -> turn main)
    ~proved:(fun () -> main.root <> None)
    ~selected;
  (main, stats, !selected)

(* Executed probe turns among the first [turns] of a restart policy whose
   axioms never change: a turn runs iff its budget exceeds every earlier
   budget of its lane. *)
let fresh_maxima (p : Slices.policy) turns =
  let best = Hashtbl.create 8 and runs = ref [] in
  for t = 0 to turns - 1 do
    match Slices.slice p ((2 * t) + 1) with
    | Slices.Probe { lane; steps; _ } ->
        if steps > Option.value ~default:0 (Hashtbl.find_opt best lane) then (
          Hashtbl.replace best lane steps;
          runs := steps :: !runs)
    | Main _ | Rest -> ()
  done;
  List.rev !runs

let tests =
  [
    ( "luby sequence",
      fun () ->
        equal (List.init 15 Slices.luby)
          [ 1; 1; 2; 1; 1; 2; 4; 1; 1; 2; 1; 1; 2; 4; 8 ]
          "Luby prefix changed" );
    ( "continuing share bound holds at every slice boundary",
      fun () ->
        List.iter
          (fun (p : Slices.policy) ->
            let main = ref 0 and probe = ref 0 and rest = ref false in
            for n = 0 to 1999 do
              (match Slices.slice p n with
              | Slices.Main steps ->
                  check (not !rest) "a bounded slice after the rest";
                  main := !main + steps
              | Probe { steps; _ } ->
                  check (not !rest) "a probe slice after the rest";
                  probe := !probe + steps
              | Rest -> rest := true);
              check (!main >= p.main_ratio * !probe) ("continuing share violated: " ^ Slices.name p)
            done;
            (* A round limit ends the probes after [rounds] visits of every lane. *)
            let lanes = List.length p.lanes in
            if p.rounds > 0 then (
              check (Slices.slice p (2 * p.rounds * lanes) = Rest) "probes outlived their rounds";
              check (Slices.slice p ((2 * p.rounds * lanes) - 1) <> Rest) "probes ended early";
              equal !probe
                (List.fold_left ( + ) 0
                   (List.init (p.rounds * lanes) (fun i -> Slices.probe_steps p i)))
                "probe budget of the rounds")
            else check (not !rest) "unbounded rounds ended")
          policies );
    ( "probe lanes are served round robin with equal budgets",
      fun () ->
        List.iter
          (fun (p : Slices.policy) ->
            let count = List.length p.lanes in
            let served = Array.make count 0 and budget = Array.make count 0 in
            for n = 0 to 1999 do
              match Slices.slice p n with
              | Slices.Main _ -> check (n mod 2 = 0) "continuing slice out of turn"
              | Rest -> check (p.rounds > 0 && n >= 2 * p.rounds * count) "rest out of turn"
              | Probe { lane; index; steps; fresh } ->
                  check (n mod 2 = 1) "probe slice out of turn";
                  equal lane (index mod count) "lane order";
                  let l = List.nth p.lanes lane in
                  (* A restart lane is always fresh; a resumed engine only once. *)
                  if l.restart then check fresh "restart lane resumed"
                  else if index >= count then check (not fresh) "resumed lane restarted";
                  served.(lane) <- served.(lane) + 1;
                  budget.(lane) <- budget.(lane) + steps;
                  let low = Array.fold_left min max_int served
                  and high = Array.fold_left max 0 served in
                  check (high - low <= 1) "a lane was starved";
                  (* After each full round every lane has had the same steps. *)
                  if lane = count - 1 then
                    check
                      (Array.for_all (fun b -> b = budget.(0)) budget)
                      ("lane budgets diverged: " ^ Slices.name p)
            done)
          policies );
    ( "luby lanes eventually receive any budget",
      fun () ->
        let p = policy ~lanes:3 ~unit_work:1 () in
        let best = Array.make 3 0 in
        for n = 0 to 2 * 3 * 64 do
          match Slices.slice p n with
          | Slices.Probe { lane; steps; _ } -> best.(lane) <- max best.(lane) steps
          | Main _ | Rest -> ()
        done;
        check (Array.for_all (fun b -> b >= 32) best) "a lane never got a long slice" );
    ( "slice options parse and validate",
      fun () ->
        check (not (Slices.enabled (Slices.parse "off"))) "off kept slicing";
        equal (Slices.parse "on") Slices.candidate "on is not the candidate";
        equal Scheduler.default_config.slices None "the default does not follow the portfolio";
        equal (Slices.parse "rounds=0").rounds 0 "rounds override lost";
        equal Slices.candidate.rounds 1 "the candidate repeats probe visits";
        let p = Slices.parse "phases=5,e=2,unit=64,geometric=2,ratio=3,resume" in
        equal
          (List.length p.lanes, p.unit_work, p.sequence, p.main_ratio)
          (7, 64, Slices.Geometric 2, 3) "overrides lost";
        let e_lanes = List.filter (fun (l : Slices.lane) -> l = Slices.e_lane) p.lanes in
        equal (List.length e_lanes) 2 "e lane occurrences";
        check (List.hd p.lanes = Slices.e_lane) "the cycle does not start with the e lane";
        check
          (List.for_all (fun (l : Slices.lane) -> l = Slices.e_lane || not l.restart) p.lanes)
          "resume flag lost";
        equal
          (List.filter_map
             (fun (l : Slices.lane) -> if l.strategy = None then Some l.offset else None)
             p.lanes)
          [ 1; 2; 3; 4; 5 ] "phase lane offsets";
        List.iter
          (fun bad -> check (rejects (fun () -> ignore (Slices.parse bad))) ("accepted " ^ bad))
          [
            "phases=-1";
            "unit=0";
            "ratio=0";
            "geometric=0";
            "phases=x";
            "speed=3";
            "phases";
            "a=b=c";
            "phases=65";
            "rounds=-1";
          ];
        check
          (rejects (fun () ->
               ignore (Eval.of_env (function "AXIOM_SLICES" -> Some "unit=-4" | _ -> None))))
          "environment hook accepted a bad unit";
        let set = function
          | "AXIOM_SLICES" -> Some "off"
          | "AXIOM_PHASE_BASE" -> Some "3"
          | _ -> None
        in
        let c = (Eval.of_env set).config Scheduler.default_config in
        check (c.slices = Some Slices.off && c.phase_base = 3) "environment hook ignored";
        equal (Eval.of_env set).active
          [ ("AXIOM_PHASE_BASE", "3"); ("AXIOM_SLICES", "off") ]
          "active switches";
        check
          (Eval.note (Eval.of_env set)
          = Some "Note: evaluation overrides active: AXIOM_PHASE_BASE=3, AXIOM_SLICES=off")
          "note" );
    ( "an unset environment keeps the default configuration and installs no hook",
      fun () ->
        let unset = Eval.of_env (fun _ -> None) in
        equal
          (unset.config Scheduler.default_config)
          Scheduler.default_config "unset environment changed the policy";
        equal unset.active [] "an unset switch is active";
        check (Eval.note unset = None) "a default run is noted";
        check (unset.isolation = Portfolio.Processes) "the default isolation is not processes";
        let clock = !Engine.cost_clock
        and unfold = !Engine.unfold_report
        and eq = !Engine.eq_report
        and equivalence = !Engine.equivalence_report
        and vampire = !Vampire.report
        and given = !Engine.given_trace
        and passive = !Engine.eval_trace
        and fresh = !Engine.new_trace in
        unset.install ();
        check
          (!Engine.cost_clock == clock && !Engine.unfold_report == unfold && !Engine.eq_report == eq
          && !Engine.equivalence_report == equivalence
          && !Vampire.report == vampire && !Engine.given_trace == given
          && !Engine.eval_trace == passive && !Engine.new_trace = fresh)
          "an unset environment installed a hook";
        (* The values that mean "unset" for the measurement and report switches. *)
        let quiet =
          Eval.of_env (function
            | "AXIOM_MEASURE_COST_CLOCK" -> Some "wall"
            | "AXIOM_MEASURE_PORTFOLIO" -> Some "processes"
            | "AXIOM_EQ_UNFOLD_REPORT" -> Some "0"
            | "AXIOM_MEASURE_GIVEN_TRACE" -> Some ""
            | _ -> None)
        in
        equal quiet.active [] "a value meaning unset is active";
        List.iter
          (fun (s : Eval.switch) ->
            check (String.starts_with ~prefix:"AXIOM_" s.name) (s.name ^ " is not an AXIOM_ name"))
          Eval.switches );
    ( "continuing engine is suspended and resumed, never restarted",
      fun () ->
        List.iter
          (fun restart ->
            (* Unprovable within the budget: every slice runs to its end. *)
            let p = policy ~lanes:2 ~unit_work:5 ~restart () in
            let theory = Tptp.parse endless in
            let config = sliced ~seconds:1.0 p in
            let r = Scheduler.portfolio config (fun () -> Theory.copy theory) in
            let w = List.hd r.workers and s = (List.hd r.workers).slices in
            check (r.certificate = None) "satisfiable fixture was refuted";
            check (w.engine == w.continuing) "a probe was reported without a proof";
            check (s.probe_slices >= 4 && s.main_slices >= 4) "too few slices for the fixture";
            (* Exact accounting: the continuing engine dispatched every step its
               slices handed out, so its state carried across all of them. Only
               the last step can stop at the deadline before dispatching. *)
            let turns = Producer_schedule.turns w.continuing.producers in
            check
              (turns <= s.main_steps && turns >= s.main_steps - 1)
              (Printf.sprintf "continuing steps were lost or restarted: %d turns for %d steps" turns
                 s.main_steps);
            check (s.main_steps >= p.main_ratio * s.probe_steps) "continuing share below its bound";
            check (Slices.main_share s >= 0.5) "share below one half";
            if restart then (
              equal s.probes_created s.probe_slices "restart reused a probe";
              equal s.peak_live_probes 1 "restart kept old probes alive")
            else (
              check (s.probes_created <= List.length p.lanes) "resume created extra probes";
              check (s.peak_live_probes <= List.length p.lanes) "resume exceeded the lane count");
            equal s.live_probes 0 "probe engines were not released";
            equal s.winner "" "phantom probe proof")
          [ true; false ] );
    ( "every slice's certificate passes the kernel",
      fun () ->
        let proofs = ref 0 in
        List.iter
          (fun (name, text) ->
            List.iter
              (fun (p : Slices.policy) ->
                let theory, r, w = solve p text in
                match r.certificate with
                | None -> ()
                | Some cert ->
                    incr proofs;
                    check (Result.is_ok (Kernel.check theory cert)) (name ^ ": kernel rejected");
                    let ids = List.map (fun (a : Wire.axiom) -> a.axiom_id) in
                    check
                      (is_prefix (ids w.engine.axioms) (ids w.continuing.axioms))
                      (name ^ ": probe searched foreign axioms");
                    check
                      (List.for_all (fun a -> List.mem a w.continuing.axioms) cert.axioms)
                      (name ^ ": certificate premise unknown to the worker");
                    equal r.proof_source "heuristic:0" "proof source format";
                    equal (w.slices.winner <> "") (w.engine != w.continuing)
                      (name ^ ": winner lane and reported engine disagree"))
              (List.concat_map
                 (fun lanes ->
                   List.concat_map
                     (fun unit_work ->
                       List.map
                         (fun restart -> policy ~lanes ~unit_work ~restart ())
                         [ true; false ])
                     [ 1; 3; 20 ])
                 [ 1; 3; 7 ]))
          problems;
        check (!proofs > 0) "no fixture was refuted" );
    ( "a probe slice reproduces the standalone engine of its phase",
      fun () ->
        (* Pick a probe phase that needs fewer steps than the continuing phase,
           size the schedule so that this lane runs first, and require that its
           proof is the standalone proof of that phase: interleaving with the
           continuing engine must not perturb the probe's search. *)
        let wins = ref 0 in
        List.iter
          (fun (name, text) ->
            let theory = Tptp.parse text in
            let standalone k =
              let r =
                Scheduler.portfolio
                  { (sliced Slices.off) with phase_base = k }
                  (fun () -> Theory.copy theory)
              in
              (r, Producer_schedule.turns r.engine.producers)
            in
            let runs = List.init 8 standalone in
            let r0, turns0 = List.hd runs in
            let faster k =
              let r, turns = List.nth runs k in
              (r : Scheduler.result).certificate <> None && k * turns < turns0
            in
            if r0.certificate <> None then
              match List.find_opt faster [ 1; 2; 3; 4; 5; 6; 7 ] with
              | None -> ()
              | Some k ->
                  let p = policy ~lanes:k ~unit_work:(snd (List.nth runs k)) () in
                  let _, r, w = solve p text in
                  check (r.certificate <> None) (name ^ ": sliced run lost the proof");
                  check (w.engine != w.continuing) (name ^ ": continuing engine won unexpectedly");
                  let phase =
                    (List.find (fun l -> Slices.lane_name l = w.slices.winner) p.lanes).offset
                  in
                  let alone, _ = List.nth runs phase in
                  incr wins;
                  equal
                    (w.engine.metrics.given, w.engine.metrics.generated)
                    (alone.engine.metrics.given, alone.engine.metrics.generated)
                    (name ^ ": probe search diverged from its standalone phase");
                  check (r.certificate = alone.certificate) (name ^ ": probe proof differs");
                  check
                    (Result.is_ok (Kernel.check theory (Option.get r.certificate)))
                    (name ^ ": kernel rejected the probe proof");
                  let e = w.engine and c = w.continuing in
                  check
                    (e.terms != c.terms && e.proof != c.proof && e.passive != c.passive
                   && e.index != c.index && e.avatar != c.avatar && e.goals != c.goals)
                    (name ^ ": probe shares state with the continuing engine"))
          problems;
        check (!wins > 0) "no fixture has a faster probe phase" );
    ( "strategy lanes keep their own calculus and pass the kernel",
      fun () ->
        let e_wins = ref 0 in
        List.iter
          (fun (name, text) ->
            List.iter
              (fun (p : Slices.policy) ->
                let theory, r, w = solve p text in
                equal w.continuing.config.strategy.name "production"
                  (name ^ ": continuing strategy changed");
                check
                  (w.continuing.order != w.engine.order || w.engine == w.continuing)
                  (name ^ ": probe shares the continuing term order");
                match r.certificate with
                | None -> ()
                | Some cert ->
                    check (Result.is_ok (Kernel.check theory cert)) (name ^ ": kernel rejected");
                    if w.slices.winner = Slices.lane_name Slices.e_lane then (
                      incr e_wins;
                      equal w.engine.config.strategy.name "proto:e" (name ^ ": e lane strategy")))
              [
                policy ~lanes:0 ~e:1 ~unit_work:1 ();
                policy ~lanes:2 ~e:2 ~unit_work:2 ();
                policy ~lanes:3 ~e:1 ~unit_work:20 ~restart:false ();
              ])
          problems;
        check (!e_wins > 0) "no e lane ever produced the proof" );
    ( "generated-clause slices account work and keep the continuing share",
      fun () ->
        let p = policy ~lanes:2 ~e:1 ~unit_work:40 ~measure:Slices.Generated () in
        let theory =
          Tptp.parse
            "cnf(s,axiom,p(s(X))|~p(X)). cnf(z,axiom,p(z)). cnf(q,axiom,(q(X,Y)|~p(X)|~p(Y)))."
        in
        let r = Scheduler.portfolio (sliced ~seconds:1.0 p) (fun () -> Theory.copy theory) in
        let w = List.hd r.workers and s = (List.hd r.workers).slices in
        check (s.probe_slices >= 3) "too few generated-clause slices";
        check
          (s.main_work > 0 && s.main_work <= w.continuing.metrics.generated)
          "continuing work exceeds its generated clauses";
        (* Every completed continuing slice reaches its budget before a probe
           slice runs; a step can overshoot, never undershoot. *)
        check
          (s.main_work >= p.main_ratio * (s.probe_work - (64 * s.probe_slices)))
          "continuing share below its bound";
        check (Slices.main_share s >= 0.45) "continuing share collapsed";
        List.iter
          (fun (name, text) ->
            let theory, r, _ = solve p text in
            Option.iter
              (fun cert ->
                check (Result.is_ok (Kernel.check theory cert)) (name ^ ": kernel rejected"))
              r.certificate)
          problems );
    ( "a single worker slices and parallel workers do not",
      fun () ->
        let theory = Tptp.parse (List.assoc "group-square" problems) in
        let one = Scheduler.portfolio (sliced Slices.candidate) (fun () -> Theory.copy theory) in
        equal (List.hd one.workers).slices.policy (Slices.name Slices.candidate) "single worker";
        let many =
          Scheduler.portfolio ~workers:3 (sliced Slices.candidate) (fun () -> Theory.copy theory)
        in
        List.iter
          (fun (w : Scheduler.worker_metrics) ->
            equal w.slices.policy "off" "parallel worker sliced";
            check (w.engine == w.continuing) "parallel worker reported a probe")
          many.workers;
        let off = Scheduler.portfolio (sliced Slices.off) (fun () -> Theory.copy theory) in
        let s = (List.hd off.workers).slices in
        equal (s.main_slices, s.probe_slices, s.probes_created) (0, 0, 0) "off still sliced";
        (* The default follows the portfolio: one balanced worker on an input without schemas
           runs the share, every other single worker runs alone. *)
        let default portfolio =
          let r =
            Scheduler.portfolio
              { (sliced Slices.off) with slices = Scheduler.default_config.slices; portfolio }
              (fun () -> Theory.copy theory)
          in
          (List.hd r.workers).slices.policy
        in
        equal (default Strategy.Balanced) (Slices.name Slices.share) "the balanced worker";
        List.iter
          (fun portfolio -> equal (default portfolio) "off" "a non-balanced single worker sliced")
          [ Strategy.Uniform; Strategy.Standard; Strategy.Workers [ Strategy.production ] ];
        (* Both portfolios resolve per-worker slices in [Scheduler.worker_configs] only. *)
        let resolved ?(config = sliced Slices.candidate) workers =
          List.map
            (fun (c : Scheduler.config) -> Option.map Slices.name c.slices)
            (Scheduler.worker_configs ~workers config)
        in
        equal (resolved 1) [ Some (Slices.name Slices.candidate) ] "worker_configs dropped slices";
        equal (resolved 4)
          (List.init 4 (fun _ -> Some "off"))
          "worker_configs sliced parallel workers";
        equal
          (resolved ~config:Scheduler.default_config 1)
          [ None ] "the default was resolved early";
        equal
          (resolved ~config:Scheduler.default_config 2)
          [ Some "off"; Some "off" ] "the default sliced parallel workers";
        let single ?(workers = 1) ~schemas (config : Scheduler.config) =
          Slices.name (Scheduler.single_slices ~workers ~schemas config)
        in
        let balanced = Scheduler.default_config in
        equal (single ~schemas:false balanced) (Slices.name Slices.share) "share for plain inputs";
        equal (single ~schemas:true balanced) "off" "a theory with schemas was sliced";
        equal (single ~workers:2 ~schemas:false balanced) "off" "two workers sliced";
        equal
          (single ~schemas:true { balanced with slices = Some Slices.candidate })
          (Slices.name Slices.candidate) "an explicit policy was dropped for schemas" );
    ( "the candidate visits each phase once, then the continuing engine runs alone",
      fun () ->
        let theory = Tptp.parse endless in
        List.iter
          (fun (p : Slices.policy) ->
            let r = Scheduler.portfolio (sliced ~seconds:1.0 p) (fun () -> Theory.copy theory) in
            let w = List.hd r.workers and s = (List.hd r.workers).slices in
            let lanes = List.length p.lanes in
            check (r.certificate = None) "satisfiable fixture was refuted";
            equal
              (s.probe_slices, s.probes_created, s.probe_skipped)
              (lanes, lanes, 0)
              ("not one visit per phase: " ^ s.policy);
            equal s.probe_steps (lanes * p.unit_work) "probe budget of one round";
            equal s.main_slices (lanes + 1) "the continuing engine did not get the rest";
            check
              (s.main_steps > lanes * p.unit_work)
              "the continuing engine stopped after the probe round";
            equal s.peak_live_probes 1 "single-round probes overlapped";
            equal s.live_probes 0 "probe engines were not released";
            let turns = Producer_schedule.turns w.continuing.producers in
            check
              (turns <= s.main_steps && turns >= s.main_steps - 1)
              "continuing steps were lost in the rest")
          [ policy ~lanes:7 ~unit_work:16 ~rounds:1 (); { Slices.candidate with unit_work = 64 } ];
        equal Slices.candidate.unit_work 512 "candidate unit";
        equal (List.length Slices.candidate.lanes) 7 "candidate lanes";
        check
          (List.for_all (fun (l : Slices.lane) -> l.strategy = None) Slices.candidate.lanes)
          "candidate lanes change the strategy" );
    ( "restart lanes never replay a completed search",
      fun () ->
        let theory = Tptp.parse endless in
        List.iter
          (fun ((p : Slices.policy), repeats) ->
            let r = Scheduler.portfolio (sliced ~seconds:1.0 p) (fun () -> Theory.copy theory) in
            let s = (List.hd r.workers).slices in
            let turns = s.probe_slices + s.probe_skipped in
            let runs = fresh_maxima p turns in
            check (turns >= 4 * List.length p.lanes) "too few probe turns for the fixture";
            equal s.probe_slices (List.length runs) ("a replay ran: " ^ s.policy);
            equal s.probes_created s.probe_slices "a restart slice reused an engine";
            (* Luby and constant budgets repeat; a doubling sequence never does. *)
            check (repeats = (s.probe_skipped > 0)) ("replay skipping not exercised: " ^ s.policy);
            (* Only the last slice can stop at the deadline before its budget. *)
            let total = List.fold_left ( + ) 0 runs in
            check
              (s.probe_steps <= total
              && s.probe_steps >= total - List.nth runs (List.length runs - 1))
              "probe steps differ from the fresh maxima";
            check (s.main_steps >= s.probe_steps) "skipped turns were not returned")
          [
            (policy ~lanes:2 ~unit_work:2 (), true);
            (policy ~lanes:3 ~unit_work:1 ~sequence:(Slices.Geometric 1) (), true);
            (policy ~lanes:1 ~unit_work:3 ~sequence:(Slices.Geometric 2) (), false);
          ];
        (* A resumed lane extends its engine and never replays. *)
        let r =
          Scheduler.portfolio
            (sliced ~seconds:1.0 (policy ~lanes:2 ~unit_work:2 ~restart:false ()))
            (fun () -> Theory.copy theory)
        in
        let s = (List.hd r.workers).slices in
        equal s.probe_skipped 0 "a resumed lane skipped a slice";
        equal s.probes_created 2 "a resumed lane restarted" );
    ( "a saturated lane revives when the axioms grow and a capped lane does not",
      fun () ->
        let extra =
          List.mapi
            (fun i (a : Wire.axiom) -> { a with axiom_id = 100 + i })
            (Theory.fixed (Tptp.parse "cnf(b,axiom,q(b)). cnf(c,axiom,r(c))."))
        in
        (* The continuing engine injects one more axiom per continuing turn,
           as schema enumeration does, and stops after the last one. *)
        let run ?limits restart =
          let pending = ref extra and turns = ref 0 in
          direct ?limits ~text:"cnf(a,axiom,p(a))."
            (policy ~lanes:1 ~unit_work:64 ~restart ())
            ~alive:(fun _ -> !turns <= List.length extra)
            ~turn:(fun main ->
              incr turns;
              (match !pending with
              | a :: rest ->
                  Engine.add_axiom main a;
                  pending := rest
              | [] -> ());
              64)
        in
        List.iter
          (fun restart ->
            let main, s, selected = run restart in
            check (selected == main) "a saturated probe reported a proof";
            equal (List.length main.axioms) 3 "fixture axioms";
            equal (s.probe_slices, s.probe_revived) (2, 1) "the saturated lane did not revive";
            equal s.probes_created 2 "a revived lane kept its saturated engine";
            equal s.live_probes 0 "dead lanes kept engines")
          [ true; false ];
        let _, s, _ = run ~limits:(fun l -> { l with Engine.max_generated = 1 }) true in
        equal (s.probe_slices, s.probe_revived) (1, 0) "a capped lane revived" );
    ( "probe engines carry the worker's memory budget",
      fun () ->
        (* The memory budget with probe slices: every probe engine gets config.engine.budget and answers
           heap pressure itself; it never withdraws instances (no ~releasable). Each probe's own
           reading is pinned at the budget and the continuing engine's at 0, so every probe is
           the larger engine and reads the worker's state (the budget): each probe responds, and
           the 2x ceiling never stops one. *)
        let b = 1 lsl 40 in
        let theory = Tptp.parse endless in
        let config = sliced ~seconds:1.5 Slices.candidate in
        let config =
          {
            config with
            engine = { config.engine with budget = { Engine.heap_words = b; proof_nodes = 0 } };
          }
        in
        let engines = ref [] and first = ref true in
        let prepare (e : Engine.t) =
          let pin = if !first then 0 else b in
          first := false;
          engines := e :: !engines;
          e.heap_reading <- (fun () -> pin)
        in
        let r = Scheduler.run_search ~prepare config theory in
        let w = List.hd r.workers in
        check (r.certificate = None) "satisfiable fixture was refuted";
        check (w.slices.probes_created >= 1) "no probe ran";
        equal (List.length !engines) (1 + w.slices.probes_created) "prepare missed an engine";
        List.iter
          (fun (e : Engine.t) ->
            equal e.config.budget.heap_words b "an engine lost the worker's budget";
            if e != w.continuing then
              check (e.metrics.budget_heap_responses >= 1) "a probe ignored heap pressure";
            equal e.metrics.budget_released 0 "a probe withdrew an instance";
            check
              (e.stopped <> Some "memory budget exhausted")
              "the ceiling stopped an engine below 2x")
          !engines );
    ( "the share is e208 at queue phase 0, resumed on the work clock with carry-over",
      fun () ->
        let p = Slices.share in
        equal p.lanes
          [ { Slices.offset = 0; strategy = Some (Strategy.of_name "e208"); restart = false } ]
          "share lanes";
        check (Some (Strategy.of_name "e208") = (List.hd p.lanes).strategy) "share member";
        equal
          (p.measure, p.sequence, p.main_ratio, p.rounds, p.carry, p.unit_work)
          (Slices.Work, Slices.Geometric 1, 1, 0, true, 15_000_000)
          "share schedule";
        (* About 50 ms of the work clock's nominal rate per slice. *)
        equal (float p.unit_work /. Engine.work_units_per_second) 0.05 "share slice length";
        (* Every slice of the share is the same 1:1 pair, forever. *)
        for n = 0 to 199 do
          match Slices.slice p n with
          | Slices.Main units -> equal units p.unit_work "continuing slice length"
          | Probe { lane; steps; fresh; index } ->
              equal (lane, steps) (0, p.unit_work) "probe slice";
              equal fresh (index = 0) "the e208 lane restarted"
          | Rest -> failwith "the share ended its probes"
        done;
        equal (Slices.parse "share") p "the hook's share differs";
        equal (Slices.parse "share,unit=30000000").unit_work 30_000_000 "share override lost";
        equal (Slices.parse "share,nocarry").carry false "carry override lost";
        equal (Slices.parse "share,members=y1346+e208").lanes
          (List.map
             (fun name ->
               { Slices.offset = 0; strategy = Some (Strategy.of_name name); restart = false })
             [ "y1346"; "e208" ])
          "member list";
        equal (Slices.parse "phases=2,members=e208,resume,work,unit=20000,carry").lanes
          ((Slices.parse "phases=2,resume").lanes
          @ [ { Slices.offset = 0; strategy = Some (Strategy.of_name "e208"); restart = false } ])
          "members follow the phase lanes";
        List.iter
          (fun bad -> check (rejects (fun () -> ignore (Slices.parse bad))) ("accepted " ^ bad))
          [
            "share,restart";
            "share,members=nonesuch";
            "phases=2,carry";
            "share,unit=0";
            "share,unit=" ^ string_of_int (Slices.min_work_unit - 1);
          ] );
    ( "the share with the members' E loop (presaturation) repeats its search exactly",
      fun () ->
        let saved = !Engine.cost_clock in
        (Engine.cost_clock := fun () -> 0.);
        Fun.protect ~finally:(fun () -> Engine.cost_clock := saved) @@ fun () ->
        let p = { Slices.share with unit_work = 1_000_000 } in
        let config =
          let c = sliced ~seconds:60. p in
          {
            c with
            (* The share's e208 lane on the members' E loop (e208 itself keeps the ported loop). *)
            loop = Some Heuristic.loop_member;
            engine = { c.engine with limits = { c.engine.limits with max_given = 150 } };
          }
        in
        check Heuristic.loop_member.presat "the member loop runs presaturation";
        let theory = Tptp.parse groups in
        let run () = Scheduler.portfolio config (fun () -> Theory.copy theory) in
        let first = run () in
        let second = run () in
        equal (share_fingerprint second) (share_fingerprint first)
          "the same input gave a different share search";
        check (first.certificate = None) "satisfiable fixture was refuted" );
    ( "the share repeats its search exactly on the stopped cost clock",
      fun () ->
        (* The scheduling costs on a stopped clock (the CLI's AXIOM_MEASURE_COST_CLOCK=stopped):
           production's search, e208's search and the work-clock slices between them then depend
           on the input alone. A different collector setting changes when the collector runs,
           never what the worker allocates or checks. Small slices give many of both kinds. *)
        let saved = !Engine.cost_clock in
        (Engine.cost_clock := fun () -> 0.);
        Fun.protect ~finally:(fun () -> Engine.cost_clock := saved) @@ fun () ->
        let p = { Slices.share with unit_work = 1_000_000 } in
        (* 200 given: production reaches its cap well before e208 under the work clock of either
           allocation profile measured (245 vs 630 slices, and 189 vs 245 after same-search
           speed-ups that allocate and check less per given, more so for e208). At 150 the
           latter reached e208's cap first. *)
        let config =
          let c = sliced ~seconds:60. p in
          {
            c with
            (* The ported lean loop: with the member's E loop (DISCOUNT selections, which count
               the clauses subsumed at selection) e208 reaches the cap before production. *)
            loop = Some Heuristic.loop_ported;
            engine = { c.engine with limits = { c.engine.limits with max_given = 200 } };
          }
        in
        let theory = Tptp.parse groups in
        let run () = Scheduler.portfolio config (fun () -> Theory.copy theory) in
        let first = run () in
        let gc = Gc.get () in
        let second =
          Fun.protect
            ~finally:(fun () -> Gc.set gc)
            (fun () ->
              Gc.set { gc with minor_heap_size = 32768; space_overhead = 400 };
              run ())
        in
        equal (share_fingerprint second) (share_fingerprint first)
          "the same input gave a different share search";
        let w = List.hd first.workers in
        let s = w.slices in
        check (first.certificate = None) "satisfiable fixture was refuted";
        equal w.continuing.stopped (Some "given clause limit") "the run did not end at its cap";
        check (s.main_slices >= 4 && s.probe_slices >= 4) "too few slices for the fixture";
        (* One e208 engine, admitted once and resumed. *)
        equal (s.probes_created, s.peak_live_probes, s.live_probes) (1, 1, 0) "e208 lane restarted";
        equal s.winner "" "phantom probe proof";
        (* Production reaches its cap first; the e208 lane runs on alone to its own cap. *)
        check (s.alone_slices > 0 && s.alone_work > 0) "the lane did not run on after the cap";
        check
          (String.ends_with ~suffix:"; e208+0~ ran on alone" first.reason)
          ("the reason hides the lane's run: " ^ first.reason);
        (* Carry-over: while both run, each engine's work tracks its handed-out budget, so the
           totals differ by about one slice (the side that ran last) plus the last step's
           overshoot. *)
        let shared = s.probe_work - s.alone_work in
        check
          (abs (s.main_work - shared) <= 3 * p.unit_work)
          (Printf.sprintf "work share drifted: %d against %d" s.main_work shared);
        (* The production search inside the share is the standalone production search: the e208
           slices suspend it and never perturb it. *)
        let alone =
          Scheduler.portfolio { config with slices = Some Slices.off } (fun () ->
              Theory.copy theory)
        in
        let a = (List.hd alone.workers).continuing and c = w.continuing in
        let search (e : Engine.t) =
          ( e.metrics.given,
            e.metrics.generated,
            e.metrics.retained,
            e.metrics.budget_checks,
            e.metrics.budget_responses )
        in
        equal (search c) (search a) "the share perturbed production's search";
        (* Production reads the worker's whole state whenever it holds the larger part. *)
        check
          (c.metrics.peak_footprint_words >= a.metrics.peak_footprint_words)
          "production read less than its own state" );
    ( "the larger engine of the share reads the worker's whole state, the smaller its own",
      fun () ->
        (* Production's own reading is pinned and the budget is off (the readings are still taken
           after every step). Pinned above anything the lane holds, production is the larger
           engine and reads its own plus the lane's state, while the lane reads its own. Pinned
           at 0, production reads 0 and the lane is the larger engine. *)
        let saved = !Engine.cost_clock in
        (Engine.cost_clock := fun () -> 0.);
        Fun.protect ~finally:(fun () -> Engine.cost_clock := saved) @@ fun () ->
        let config =
          let c = sliced ~seconds:60. { Slices.share with unit_work = 1_000_000 } in
          {
            c with
            engine =
              {
                c.engine with
                budget = Engine.no_budget;
                limits = { c.engine.limits with max_given = 150 };
              };
          }
        in
        let run ?(slices = config.slices) pin =
          let lanes = ref [] in
          let prepare (e : Engine.t) =
            if e.config.strategy.name = "production" then e.heap_reading <- (fun () -> pin)
            else lanes := e :: !lanes
          in
          let r = Scheduler.run_search ~prepare { config with slices } (Tptp.parse groups) in
          check (r.certificate = None) "satisfiable fixture was refuted";
          ((List.hd r.workers).continuing.metrics.peak_footprint_words, !lanes)
        in
        let big = 1 lsl 40 in
        let read, lanes = run big in
        let lane = match lanes with [ e ] -> e | _ -> failwith "not one e208 engine" in
        check (read > big) "the larger engine left out the lane's state";
        check (lane.metrics.peak_footprint_words < big) "the smaller engine read the larger one's";
        check (lane.metrics.peak_footprint_words > 0) "the lane read nothing";
        let read, lanes = run 0 in
        let lane = match lanes with [ e ] -> e | _ -> failwith "not one e208 engine" in
        equal read 0 "the smaller engine read the lane's state";
        check (lane.metrics.peak_footprint_words > 0) "the larger engine read nothing";
        (* Without slices nothing else is counted. *)
        equal (fst (run ~slices:(Some Slices.off) 0)) 0 "production alone read beyond itself" );
    ( "share proofs pass the kernel, from either engine",
      fun () ->
        let wins = Hashtbl.create 4 in
        List.iter
          (fun (name, text) ->
            List.iter
              (fun unit_work ->
                let theory, r, w = solve { Slices.share with unit_work } text in
                match r.certificate with
                | None -> ()
                | Some cert ->
                    check (Result.is_ok (Kernel.check theory cert)) (name ^ ": kernel rejected");
                    let winner = w.engine.config.strategy.name in
                    Hashtbl.replace wins winner ();
                    equal (w.slices.winner <> "") (w.engine != w.continuing)
                      (name ^ ": winner lane and reported engine disagree");
                    if w.engine != w.continuing then equal winner "e208" (name ^ ": lane strategy");
                    check
                      (List.for_all (fun a -> List.mem a w.continuing.axioms) cert.axioms)
                      (name ^ ": certificate premise unknown to the worker"))
              [ Slices.min_work_unit; 200_000; Slices.share.unit_work ])
          problems;
        check (Hashtbl.mem wins "production") "production never won in the share";
        check (Hashtbl.mem wins "e208") "e208 never won in the share" );
    ( "the lanes keep the worker's time when the continuing engine ends on its own",
      fun () ->
        (* The continuing engine takes one turn and then has nothing left, as a saturated or
           stopped engine: the e208 lane runs on alone, its slices back to back, and refutes. *)
        List.iter
          (fun (name, text) ->
            let theory = Tptp.parse text and turns = ref 0 in
            let main, s, selected =
              direct ~text
                { Slices.share with unit_work = Slices.min_work_unit }
                ~alive:(fun _ -> !turns < 1)
                ~turn:(fun _ ->
                  incr turns;
                  1)
            in
            check (selected != main) (name ^ ": the lane did not run on to the proof");
            equal s.winner "e208+0~" (name ^ ": winner");
            check (s.alone_slices > 0 && s.alone_slices <= s.probe_slices) (name ^ ": slices alone");
            equal s.main_slices 1 (name ^ ": a continuing slice after the end");
            let cert = Option.get (Engine.certificate selected ~theory:(Theory.name theory)) in
            check (Result.is_ok (Kernel.check theory cert)) (name ^ ": kernel rejected");
            (* The ended engine's search state was released; its axioms stay for the lanes. *)
            equal
              (Engine.footprint main, Proof.stored main.proof, Passive.length main.passive)
              (0, 0, 0)
              (name ^ ": the ended engine kept its state");
            equal (List.length main.axioms)
              (List.length (Theory.fixed theory))
              (name ^ ": the ended engine lost its axioms"))
          problems;
        (* A lane that cannot run any more ends the worker: a capped restart lane with constant
           slices has nothing left once it completed its budget (every slice would replay it). *)
        let turns = ref 0 in
        let _, s, _ =
          direct ~text:endless
            (policy ~lanes:1 ~unit_work:3 ~sequence:(Slices.Geometric 1) ())
            ~alive:(fun _ -> !turns < 1)
            ~turn:(fun _ ->
              incr turns;
              1)
        in
        equal (s.probe_slices, s.alone_slices) (1, 1) "a completed constant restart lane ran again";
        check (s.probe_skipped = 0) "the worker kept skipping a finished lane" );
    ( "an engine of the share that stops early leaves the worker's time to the other (stopped clock)",
      fun () ->
        (* Either engine is made to stop at its first budget check (its reading pinned at twice
           the ceiling under escalation): "memory budget exhausted" after one step. The other
           engine must keep the worker's time and refute the fixture alone. Small slices, so that
           neither engine finishes in its first slice. *)
        let saved = !Engine.cost_clock in
        (Engine.cost_clock := fun () -> 0.);
        Fun.protect ~finally:(fun () -> Engine.cost_clock := saved) @@ fun () ->
        let budget = 1 lsl 20 in
        let config =
          let c = sliced ~seconds:60. { Slices.share with unit_work = Slices.min_work_unit } in
          {
            c with
            engine = { c.engine with budget = { Engine.heap_words = budget; proof_nodes = 0 } };
          }
        in
        let run name text =
          let stopped = ref [] in
          let prepare (e : Engine.t) =
            if e.config.strategy.name = name then (
              stopped := e :: !stopped;
              e.heap_reading <- (fun () -> 4 * budget);
              e.budget_escalate <- true)
          in
          let theory = Tptp.parse text in
          let r = Scheduler.run_search ~prepare config theory in
          (match !stopped with
          | [ e ] ->
              equal e.stopped (Some "memory budget exhausted") (name ^ " did not stop early");
              equal e.metrics.budget_checks 1 (name ^ " passed its first budget check")
          | _ -> failwith (name ^ " ran in more or fewer than one engine"));
          check (r.certificate <> None) (name ^ ": the other engine lost the proof");
          check
            (Result.is_ok (Kernel.check theory (Option.get r.certificate)))
            (name ^ ": kernel rejected");
          List.hd r.workers
        in
        List.iter
          (fun (fixture, text) ->
            (* Production stops; the e208 lane runs on alone. *)
            let w = run "production" text in
            equal w.slices.winner "e208+0~" (fixture ^ ": winner after production stopped");
            check (w.slices.alone_slices > 0) (fixture ^ ": the lane did not run on alone");
            equal
              (Engine.footprint w.continuing, Proof.stored w.continuing.proof)
              (0, 0)
              (fixture ^ ": production's state was kept");
            (* e208 stops; production keeps the worker's time. *)
            let w = run "e208" text in
            check (w.engine == w.continuing) (fixture ^ ": production did not keep the time");
            (* Its first slices may pass in its admission; it took one step in all. *)
            equal
              (w.slices.probes_created, w.slices.probe_steps)
              (1, 1)
              (fixture ^ ": the stopped lane ran again");
            equal (w.slices.live_probes, w.slices.alone_slices) (0, 0) (fixture ^ ": lane state"))
          problems );
    ( "a released engine keeps its metrics and lets the collector reclaim its state",
      fun () ->
        let saved = !Engine.cost_clock in
        (Engine.cost_clock := fun () -> 0.);
        Fun.protect ~finally:(fun () -> Engine.cost_clock := saved) @@ fun () ->
        let theory = Tptp.parse groups in
        let e =
          Engine.create
            {
              Engine.default_config with
              budget = Engine.no_budget;
              limits = { Engine.default_limits with max_given = 300; seconds = 60. };
            }
        in
        Engine.add_initial_axioms e (Theory.fixed theory);
        Engine.finish e;
        equal e.stopped (Some "given clause limit")
          ("the fixture did not reach its cap: "
          ^ Option.value ~default:"-" e.stopped
          ^ Printf.sprintf " given=%d root=%b" e.metrics.given (e.root <> None));
        let reason = Engine.reason e
        and counters = Scheduler.counters e
        and metrics = { e.metrics with generated = e.metrics.generated } in
        check (Engine.footprint e > 0 && Proof.stored e.proof > 0) "nothing to release";
        Gc.full_major ();
        let before = Obj.reachable_words (Obj.repr e) in
        Engine.release e;
        Gc.full_major ();
        let after = Obj.reachable_words (Obj.repr e) in
        check
          (10 * after < before)
          (Printf.sprintf "the released engine still holds %d of %d words" after before);
        equal
          (Engine.footprint e, Proof.stored e.proof, Passive.length e.passive)
          (0, 0, 0) "live state left";
        check (not (Engine.has_work e)) "a released engine has work";
        equal (Engine.reason e) reason "the stop reason changed";
        equal
          { (Scheduler.counters e) with seconds = 0. }
          { counters with seconds = 0. } "counters changed";
        check (e.metrics = metrics) "metrics changed";
        (* A refutation needs its proof store. *)
        let refuted = Engine.create Engine.default_config in
        Engine.add_initial_axioms refuted
          (Theory.fixed (Tptp.parse "cnf(a,axiom,p(c)). cnf(b,axiom,~p(c))."));
        Engine.finish refuted;
        check (refuted.root <> None) "the contradiction was not refuted";
        check (rejects (fun () -> Engine.release refuted)) "a refuted engine was released" );
    ( "theory cases: resumed probes receive injected instances and pass the kernel",
      fun () ->
        let late = ref 0 and probe_proofs = ref 0 in
        List.iter
          (fun name ->
            List.iter
              (fun (p : Slices.policy) ->
                let theory = Theory.create name in
                let config = { Test_support.config with slices = Some p } in
                let r = Scheduler.portfolio config (fun () -> Theory.create name) in
                let w = List.hd r.workers in
                late := !late + w.slices.probe_late_axioms;
                let ids = List.map (fun (a : Wire.axiom) -> a.axiom_id) in
                check
                  (is_prefix (ids w.engine.axioms) (ids w.continuing.axioms))
                  (name ^ ": probe searched foreign axioms");
                match r.certificate with
                | None -> ()
                | Some cert ->
                    if w.engine != w.continuing then incr probe_proofs;
                    check (Result.is_ok (Kernel.check theory cert)) (name ^ ": kernel rejected");
                    (* A schema probe-lane certificate cites the fixed axioms and one
                       instance numbered in the lane's own ID space (the kernel check
                       above covers it); the premise check is for engine certificates. *)
                    if not (String.starts_with ~prefix:"probe:" r.proof_source) then
                      check
                        (List.for_all (fun a -> List.mem a w.continuing.axioms) cert.axioms)
                        (name ^ ": certificate premise unknown to the worker"))
              [
                policy ~lanes:3 ~unit_work:1 ~restart:false ();
                policy ~lanes:2 ~e:1 ~unit_work:2 ~restart:false ();
                policy ~lanes:3 ~unit_work:1 ();
                policy ~lanes:2 ~unit_work:2 ~measure:Slices.Generated ~restart:false ();
              ])
          [ "naive"; "separation-universal"; "foundation-self"; "mutated-separation" ];
        check (!late > 0) "no resumed probe received an injected instance";
        ignore !probe_proofs );
  ]

(* The timing tier (slice_tests.exe --timing, the runtest-timing alias): wall-clock deadlines. *)
let timing_tests =
  [
    ( "probes stop at the worker deadline",
      fun () ->
        (* The continuing engine is idle, so the deadline falls inside a probe
           slice whose budget is far larger than the remaining time. *)
        List.iter
          (fun (p : Slices.policy) ->
            let seconds = 0.3 in
            let before = Telemetry.now () in
            let main, s, selected =
              direct ~seconds ~text:endless p
                ~alive:(fun main -> Telemetry.now () -. main.started < seconds)
                ~turn:(fun _ -> max_int / 4)
            in
            let wall = Telemetry.now () -. before in
            check (selected == main) "a probe refuted the satisfiable fixture";
            check (s.probe_slices >= 1 && s.probe_steps < p.unit_work) "the probe slice was not cut";
            check
              (wall < seconds +. 0.25)
              (Printf.sprintf "probes ran past the deadline: %.3f s for %.1f s" wall seconds))
          [
            policy ~lanes:1 ~unit_work:1_000_000_000 ();
            policy ~lanes:2 ~unit_work:1_000_000_000 ~restart:false ();
            policy ~lanes:0 ~e:1 ~unit_work:1_000_000_000 ();
            policy ~lanes:1 ~unit_work:1_000_000_000 ~measure:Slices.Generated ();
          ];
        (* The whole worker, probes included, respects its time limit. *)
        let theory = Tptp.parse endless in
        List.iter
          (fun p ->
            let r = Scheduler.portfolio (sliced ~seconds:0.3 p) (fun () -> Theory.copy theory) in
            check
              (r.wall_seconds < 0.3 +. 0.25)
              (Printf.sprintf "sliced worker overran: %.3f s" r.wall_seconds))
          [
            policy ~lanes:2 ~unit_work:1 ~sequence:(Slices.Geometric 64) ();
            policy ~lanes:2 ~unit_work:1 ~sequence:(Slices.Geometric 64) ~restart:false ();
          ] );
  ]

(* Every search here runs its scheduling costs on a stopped clock (the CLI's
   AXIOM_MEASURE_COST_CLOCK=stopped), so that which engine wins, and how far each gets in a
   bounded run, depends on the input alone, not on the machine's load. *)
let () =
  (Engine.cost_clock := fun () -> 0.);
  run (if Array.mem "--timing" Sys.argv then timing_tests else tests)
