open Axiom_fuzzer
open Test_support
open Wire

(* e208 on the ported lean loop: these fixtures need Passive to grow under the queue mix before
   the refutation, which the E loop of the member finds sooner. *)
let e208_ported =
  let s = Strategy.of_name "e208" in
  match s.heuristic with
  | Some h -> { s with heuristic = Some { h with loop = Heuristic.loop_ported } }
  | None -> s

let unlimited = { Engine.default_limits with seconds = 5. }

let engine ?(budget = Engine.no_budget) ?(limits = unlimited) theory =
  let e = Engine.create { Engine.default_config with limits; budget } in
  List.iter (Engine.add_axiom e) (Theory.fixed theory);
  e

let live (e : Engine.t) = e.root = None && e.stopped = None

(* An equational problem with plenty of derived clauses for every strategy. *)
let group_cube =
  "cnf(left_identity,axiom,mult(e,X)=X). cnf(left_inverse,axiom,mult(inv(X),X)=e). \
   cnf(associativity,axiom,mult(mult(X,Y),Z)=mult(X,mult(Y,Z))). \
   cnf(cube,axiom,mult(X,mult(X,X))=e). \
   cnf(goal,negated_conjecture,mult(a,mult(b,mult(a,mult(b,mult(a,b)))))!=e)."

let steps (e : Engine.t) n =
  for _ = 1 to n do
    if live e && Engine.has_work e then Engine.step e
  done

(* Goal-only fixtures, as in goal_tests: no ordinary saturation helpers. *)
let goal_settings =
  {
    Engine.default_config with
    avatar = false;
    subsumption = false;
    demodulation = false;
    backward_demodulation = false;
    collect_every = 0;
    limits = { unlimited with max_given = 2000; max_generated = 30000; max_retained = 30000 };
  }

let advance ?(attempts = 16) (e : Engine.t) =
  Engine.protect (fun () ->
      Goal.advance ~attempts e.goals
        ~guard:(fun () -> Engine.check_time e)
        ~blocked:(Avatar.blocked e.avatar ~guard:(fun () -> ()))
        ~alive:(Engine.current_ticket e) ~record:(Engine.record e) ~emit:(Engine.emit e)
        ~redundant:(fun parents clause ->
          let support =
            List.concat_map (Avatar.dependency e.avatar) parents |> List.sort_uniq compare
          in
          Avatar.duplicate e.avatar ~guard:(fun () -> ()) ~variants:true ~except:(-1) support clause)
        ~demand:e.on_demand)

(* Every sign pattern over three unary atoms: unsatisfiable, refuted by Goal alone. *)
let cube =
  List.init 8 (fun i ->
      let literals =
        List.init 3 (fun bit ->
            (if i land (1 lsl bit) = 0 then "" else "~") ^ Printf.sprintf "q%d(X)" bit)
      in
      Printf.sprintf "cnf(c%d,axiom,(%s))." i (String.concat "|" literals))
  |> String.concat " "

let goal_refutation ~drop =
  let theory = Tptp.parse cube in
  let e = Engine.create goal_settings in
  List.iter (Engine.add_axiom e) (Theory.fixed theory);
  let dropped = ref 0 in
  for _ = 1 to 20000 do
    if live e && Goal.has_work e.goals then (
      advance ~attempts:1 e;
      if drop then dropped := !dropped + Goal.drop_cursors e.goals)
  done;
  (theory, e, !dropped)

let tests =
  [
    ( "count caps default to unlimited and the legacy caps stay reachable",
      fun () ->
        let l = Engine.default_limits in
        check
          (l.max_given = max_int && l.max_generated = max_int && l.max_retained = max_int)
          "default count caps are not unlimited";
        equal Engine.attempt_limits
          { Engine.max_given = 2000; max_generated = 50000; max_retained = 20000; seconds = 10. }
          "attempt caps changed";
        equal Engine.default_config.budget Engine.default_budget "default budget not applied";
        equal Scheduler.default_config.engine.budget Engine.default_budget
          "portfolio default lost the budget";
        check
          (Engine.default_budget.heap_words > 0 && Engine.default_budget.proof_nodes > 0)
          "memory budgets disabled by default";
        check
          (rejects (fun () ->
               ignore
                 (Engine.create
                    {
                      Engine.default_config with
                      budget = { Engine.default_budget with proof_nodes = -1 };
                    })))
          "negative budget accepted";
        (* An explicit cap remains a permanent stop with its former reason. *)
        let e = engine ~limits:{ unlimited with max_generated = 200 } (Theory.create "zf") in
        steps e 1000000;
        equal e.stopped (Some "generated clause limit") "explicit generated cap no longer stops";
        equal e.metrics.budget_responses 0 "budget acted without pressure" );
    ( "the proof-node budget trims Passive between steps and the worker keeps running",
      fun () ->
        (* The ZF fixed axioms keep about 200 active clauses here, well below
           the three-quarter target, so trimming always leaves Passive work. *)
        let budget = { Engine.heap_words = 0; proof_nodes = 1500 } in
        (* A generated-clause cap, not the wall clock, ends the run, and the scheduling costs run
           on a stopped clock: the same steps on a loaded machine. *)
        let e =
          engine ~budget
            ~limits:{ unlimited with seconds = 120.; max_generated = 20_000 }
            (Theory.create "zf")
        in
        let over = ref 0 in
        let saved = !Engine.cost_clock in
        (Engine.cost_clock := fun () -> 0.);
        Fun.protect
          ~finally:(fun () -> Engine.cost_clock := saved)
          (fun () ->
            while live e && Engine.has_work e do
              Engine.step e;
              if live e && Engine.budget_nodes e >= budget.proof_nodes then incr over
            done);
        equal !over 0 "node budget exceeded after a step";
        check (e.metrics.budget_node_responses > 0) "node budget never responded";
        check (e.metrics.budget_trimmed > 0) "node budget never trimmed Passive";
        equal e.metrics.budget_heap_responses 0 "disabled heap budget responded";
        equal e.stopped (Some "generated clause limit")
          (Printf.sprintf "worker ended by %s with nodes=%d passive=%d"
             (Option.value ~default:"exhaustion" e.stopped)
             (Engine.budget_nodes e) (Passive.length e.passive));
        check (e.metrics.generated >= 20_000) "worker stopped before its cap";
        check (e.ground_boolean.capacity <= budget.proof_nodes) "ground context escaped the budget"
    );
    ( "the heap budget drops every suspended cursor at each response and escalates after settling",
      fun () ->
        check (Telemetry.domain_major_words () > 0) "per-Domain heap statistics unavailable";
        check (Telemetry.major_cycles () >= 0) "major-cycle count unavailable";
        (* Readings are passed in, so the ladder is tested and not the collector.
           Real readings stay far below this budget. *)
        let b = 1 lsl 40 in
        let e = engine ~budget:{ Engine.heap_words = b; proof_nodes = 0 } (Theory.create "zf") in
        let suspended () =
          Tbl.Int.fold
            (fun _ (s : Goal.state) n -> if s.cursor <> None then n + 1 else n)
            e.goals.states 0
          + Tbl.Int.fold
              (fun _ (q : Goal_transfer.request) n -> if q.cursor <> None then n + 1 else n)
              e.transfer.requests 0
        in
        let run_until_suspended () =
          e.budget_settled <- max_int;
          let n = ref 0 in
          while live e && Engine.has_work e && suspended () = 0 && !n < 100000 do
            Engine.step e;
            incr n
          done
        in
        run_until_suspended ();
        let first = suspended () in
        check (first > 0) "fixture never suspended a cursor";
        equal e.metrics.budget_responses 0 "budget acted without pressure";
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:b e;
        equal e.metrics.budget_heap_responses 1 "pressure without a response";
        equal e.metrics.budget_cursor_drops first "not every suspended cursor was dropped";
        equal (suspended ()) 0 "a cursor survived the response";
        equal e.metrics.budget_trimmed 0 "the first response discarded clauses";
        check e.budget_escalate "a response did not arm escalation";
        check (e.metrics.budget_first_seconds >= 0.) "first response time missing";
        (* Readings taken before the response has been swept repeat nothing. *)
        e.budget_settled <- max_int;
        Engine.enforce_budget ~words:(4 * b) e;
        equal e.metrics.budget_heap_responses 1 "response repeated before settling";
        check (live e) "an unsettled reading stopped the worker";
        (* Rebuilt cursors are not protected: the next response drops them too. *)
        run_until_suspended ();
        let second = suspended () in
        check (second > 0) "no cursor was rebuilt";
        let victims = List.length (Engine.trimmable e) and passive = Passive.length e.passive in
        check (victims >= 4) "fixture has too few derived Passive clauses";
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:b e;
        equal e.metrics.budget_heap_responses 2 "settled pressure without a response";
        equal e.metrics.budget_cursor_drops (first + second) "rebuilt cursors were protected";
        equal e.metrics.budget_trimmed (victims / 4) "escalation did not trim a quarter";
        equal (Passive.length e.passive) (passive - (victims / 4)) "trimmed clauses stayed passive";
        check (live e) "escalation below the ceiling stopped the worker";
        (* Just under the budget the pressure stays; below three quarters of it,
           relief disarms escalation, so a reading at the ceiling first responds. *)
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:(b - 1) e;
        check e.budget_escalate "a reading just under the budget ended the pressure";
        equal e.metrics.budget_heap_responses 2 "a reading under the budget responded";
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:(b / 4 * 3) e;
        check e.budget_escalate "a reading at three quarters ended the pressure";
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:((b / 4 * 3) - 1) e;
        check (not e.budget_escalate) "relief kept escalation armed";
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:(Engine.ceiling * b) e;
        check (live e && e.metrics.budget_heap_responses = 3) "the ceiling skipped the response";
        (* A settled response that left the heap at the ceiling stops the worker,
           though Passive still has clauses. *)
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:(Engine.ceiling * b) e;
        equal e.stopped (Some "memory budget exhausted") "the ceiling did not stop the worker";
        check (e.finished <> None) "the ceiling stop was not sealed";
        check (Passive.length e.passive > 0) "the stop waited for an empty Passive" );
    ( "budget trimming never discards fixed input clauses",
      fun () ->
        let e = engine (Theory.create "zf") in
        let inputs () =
          Tbl.Int.fold
            (fun id _ n -> match (Proof.get e.proof id).rule with Input _ -> n + 1 | _ -> n)
            e.passive.live 0
        in
        let n = ref 0 in
        while live e && Engine.has_work e && Engine.trimmable e = [] && !n < 100000 do
          Engine.step e;
          incr n
        done;
        let kept = inputs () in
        check
          (kept > 0 && Engine.trimmable e <> [])
          "fixture lacks input or derived Passive clauses";
        Engine.trim_passive e max_int;
        equal (Engine.trimmable e) [] "a derived clause survived a full trim";
        equal (inputs ()) kept "trimming discarded an input clause";
        equal (Passive.length e.passive) kept "Passive kept a clause that is neither" );
    ( "heap readings belong to the calling Domain",
      fun () ->
        let ready = Atomic.make false and release = Atomic.make false in
        let before = Telemetry.domain_major_words () in
        let worker =
          Domain.spawn (fun () ->
              let start = Telemetry.domain_major_words () in
              let keep = Array.init 32 (fun i -> Array.make 100000 (float i)) in
              let grown = Telemetry.domain_major_words () - start in
              Atomic.set ready true;
              while not (Atomic.get release) do
                Domain.cpu_relax ()
              done;
              (grown, Array.length keep))
        in
        while not (Atomic.get ready) do
          Domain.cpu_relax ()
        done;
        let during = Telemetry.domain_major_words () in
        Atomic.set release true;
        let grown, _ = Domain.join worker in
        check (grown >= 3000000) "a Domain did not see its own large allocations";
        check (during - before < 1000000) "another Domain's heap was counted" );
    ( "exhausting a trimmed clause set is not reported as saturation",
      fun () ->
        (* Satisfiable, with derived clauses for the node budget to trim. *)
        let text =
          "cnf(a,axiom,p(a)). cnf(b,axiom,~p(X)|q(X)). cnf(c,axiom,~q(X)|r(X)). \
           cnf(d,axiom,~r(X)|s(X)). cnf(e,axiom,~s(X)|t(X)). cnf(f,axiom,~t(X)|u(X))."
        in
        let note k =
          Printf.sprintf " after the memory budget discarded %d passive clause%s" k
            (if k = 1 then "" else "s")
        in
        let trimmed budget =
          let e =
            engine ~budget:{ Engine.heap_words = 0; proof_nodes = budget } (Tptp.parse text)
          in
          Engine.finish e;
          if e.stopped = None && e.metrics.budget_trimmed > 0 then Some (budget, e) else None
        in
        match List.find_map trimmed (List.init 40 (fun i -> i + 4)) with
        | None -> failwith "no node budget trimmed a derived clause and exhausted"
        | Some (budget, e) ->
            let k = e.metrics.budget_trimmed in
            equal (Engine.reason e)
              ("finite clause set exhausted" ^ note k ^ "; consistency not established")
              "trimmed exhaustion reported as saturation";
            let r =
              Scheduler.run
                {
                  config with
                  engine =
                    { config.engine with budget = { Engine.heap_words = 0; proof_nodes = budget } };
                }
                (Tptp.parse text)
            in
            check (r.certificate = None) "satisfiable fixture refuted";
            let k = r.engine.metrics.budget_trimmed in
            check (k > 0) "the scheduler run trimmed nothing";
            check
              (String.ends_with ~suffix:(note k ^ "; consistency not established") r.reason)
              ("scheduler hid the trimming: " ^ r.reason) );
    ( "memory pressure never withholds guidance, and withdrawn instances return",
      fun () ->
        (* Readings are injected and every one counts as settled: over the
           budget but under the ceiling, so each step escalates, until [relieve]
           holds, then under it. *)
        let b = 1 lsl 20 in
        (* Instances injected while withdrawn ones were held back by pressure. *)
        let early = ref 0 in
        let search ?(guided = false) ?(relieve = fun _ -> false) budget seconds =
          let engine = ref None in
          let prepare (e : Engine.t) =
            engine := Some e;
            e.heap_reading <-
              (fun () ->
                e.budget_settled <- 0;
                if relieve e then b / 2 else 3 * b / 2)
          in
          let on_instance _ =
            Option.iter
              (fun (e : Engine.t) ->
                if
                  Engine.memory_pressure e && Engine.ordinary_has_work e
                  && e.metrics.budget_released > e.metrics.budget_reinjected
                then incr early)
              !engine
          in
          early := 0;
          Scheduler.run_search ~prepare ~on_instance
            {
              config with
              reference = false;
              guided;
              engine = { config.engine with budget; limits = { unlimited with seconds } };
            }
            (Theory.create "zf")
        in
        (* Instances in order of first injection; a returned one repeats. *)
        let fresh (r : Scheduler.result) =
          let seen = Hashtbl.create 64 in
          List.filter_map
            (fun (trace : Scheduler.trace) ->
              let key = (trace.axiom.origin, trace.axiom.formula) in
              if trace.generator = Scheduler.Exhaustive && not (Hashtbl.mem seen key) then (
                Hashtbl.add seen key ();
                Some key)
              else None)
            r.traces
        in
        let pressure = { Engine.heap_words = b; proof_nodes = 0 } in
        let pressed = search pressure 3. in
        let early_pressed = !early in
        let free = search Engine.no_budget 3. in
        let m = pressed.engine.metrics in
        let prefix xs ys = List.filteri (fun i _ -> i < List.length xs) ys = xs in
        equal free.engine.metrics.budget_released 0 "instances withdrawn without a budget";
        check (pressed.engine.stopped = Some "time limit") "the pressed run did not run its time";
        check (m.budget_heap_responses > 1 && m.budget_trimmed > 0) "pressure never escalated";
        check (m.budget_released > 0) "pressure withdrew no instance";
        equal (List.length (fresh free)) config.max_instances "fixture missed the instance limit";
        (* The streams pause only while withdrawn instances wait. *)
        check (prefix (fresh pressed) (fresh free)) "pressure reordered enumeration";
        equal early_pressed 0 "an instance was injected while withdrawn ones waited";
        (* Withdrawn instances may return only when trimming emptied the
           worker's ordinary work, so at most as many as were withdrawn. *)
        check (m.budget_reinjected <= m.budget_released) "returned more instances than withdrawn";
        (* Relief returns every withdrawn instance, each traced once more, and
           the streams finish in order. *)
        let relieved = search ~relieve:(fun e -> e.metrics.budget_released > 0) pressure 3. in
        let m = relieved.engine.metrics in
        check (m.budget_released > 0) "the relieved run withdrew nothing";
        equal m.budget_reinjected m.budget_released
          (Printf.sprintf "a withdrawn instance did not return (%d of %d; escalate=%b; stop=%s)"
             m.budget_reinjected m.budget_released relieved.engine.budget_escalate
             (Option.value ~default:"-" relieved.engine.stopped));
        equal (List.length relieved.traces)
          (List.length (fresh relieved) + m.budget_reinjected)
          "a returned instance was not traced once";
        equal (fresh relieved) (fresh free) "relief reordered enumeration";
        (* Pressure starts at the first step, so every guidance turn ran under it. *)
        let guided = search ~guided:true pressure 2. in
        check (guided.engine.metrics.budget_heap_responses > 0) "no response in the guided run";
        check (guided.engine.control.arms.(3).runs > 0) "pressure withheld guidance";
        equal (List.hd guided.workers).guidance.dropped_events 0 "guidance events were dropped" );
    ( "withdrawn instances wait until the reading is back at half the budget",
      fun () ->
        let b = 1 lsl 20 in
        let e = engine ~budget:{ Engine.heap_words = b; proof_nodes = 0 } (Theory.create "zf") in
        let reading = ref 0 in
        e.heap_reading <- (fun () -> !reading);
        check (not (Engine.holds_instances e)) "an engine without pressure held instances";
        reading := b;
        e.budget_settled <- 0;
        Engine.enforce_budget e;
        check (Engine.memory_pressure e && Engine.holds_instances e) "a response held no instance";
        reading := (b / 2) + 1;
        e.budget_settled <- 0;
        Engine.enforce_budget e;
        check (not (Engine.memory_pressure e)) "relief kept the pressure";
        check (Engine.holds_instances e) "instances returned above half the budget";
        reading := b / 2;
        check (not (Engine.holds_instances e)) "instances still held at half the budget";
        let free = engine (Theory.create "zf") in
        free.heap_reading <- (fun () -> max_int);
        check (not (Engine.holds_instances free)) "a disabled budget held instances" );
    ( "budget trimming withdraws releasable instances whole and only once",
      fun () ->
        let theory = Theory.create "zf" in
        let e = engine theory in
        let schema = List.hd (Theory.schemas theory) in
        let ids =
          Theory.enumerate theory schema |> Seq.filter_map Fun.id |> Seq.take 3 |> List.of_seq
          |> List.mapi (fun i phi ->
              let a = Theory.instantiate_parameter theory ~id:(100000 + i) schema phi in
              Engine.add_axiom ~releasable:true e a;
              a.axiom_id)
        in
        let passive_inputs keep =
          Tbl.Int.fold
            (fun id _ n ->
              match (Proof.get e.proof id).rule with Input (a, _) when keep a -> n + 1 | _ -> n)
            e.passive.live 0
        in
        let fixed = passive_inputs (fun a -> not (List.mem a ids)) in
        check
          (List.for_all (fun a -> passive_inputs (( = ) a) > 0) ids && fixed > 0)
          "fixture lacks Passive input clauses";
        Engine.trim_passive e max_int;
        equal (passive_inputs (fun a -> not (List.mem a ids))) fixed "a fixed input was discarded";
        equal (passive_inputs (fun a -> List.mem a ids)) 0 "a withdrawn instance kept a clause";
        equal
          (List.sort compare (List.of_seq (Queue.to_seq e.released)))
          ids "withdrawn instances not queued once each";
        equal e.metrics.budget_released 3 "released count";
        Engine.trim_passive e max_int;
        equal (Queue.length e.released) 3 "an instance was withdrawn twice" );
    ( "a heap response ends in the installed sweep, flagged first once",
      fun () ->
        let b = 1 lsl 40 in
        let e = engine ~budget:{ Engine.heap_words = b; proof_nodes = 0 } (Theory.create "zf") in
        let calls = ref [] in
        Engine.set_budget_sweep e (fun ~first -> calls := first :: !calls);
        steps e 20;
        equal !calls [] "the sweep ran without pressure";
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:b e;
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:b e;
        equal (List.rev !calls) [ true; false ] "sweep not called once per response";
        equal e.metrics.budget_heap_responses 2 "responses" );
    ( "the default heap response runs the adaptive sweep and the first one resets its interval",
      fun () ->
        (* The memory budget with the collection runtime: a response never goes through
           [periodic_collect] (which may skip the sweep). It runs the adaptive sweep, which restarts
           the interval and guards; the worker's first response also resets the interval to every
           collection point, and while the pressure lasts every collection point sweeps. *)
        let b = 1 lsl 40 in
        let e = engine ~budget:{ Engine.heap_words = b; proof_nodes = 0 } (Theory.create "zf") in
        check e.config.collect_adaptive "the default is the adaptive sweep";
        steps e 50;
        let sweeps () = e.metrics.collections in
        e.sweep_interval <- 64;
        e.sweep_wait <- 7;
        let before = sweeps () in
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:b e;
        equal (sweeps ()) (before + 1) "the first response did not sweep";
        equal (e.sweep_interval, e.sweep_wait) (1, 0) "the first response kept the interval";
        equal e.sweep_stored (Proof.stored e.proof) "the sweep guards did not restart";
        check (Engine.memory_pressure e) "no pressure after a response";
        (* Under pressure every collection point sweeps, whatever the interval. *)
        e.sweep_interval <- 64;
        e.sweep_wait <- 0;
        let before = sweeps () in
        Engine.periodic_collect e Producer_schedule.Trace.Producer;
        equal (sweeps ()) (before + 1) "a collection point under pressure skipped the sweep";
        (* A later response sweeps but adapts the interval instead of resetting it. *)
        e.sweep_interval <- 32;
        let before = sweeps () in
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:b e;
        equal (sweeps ()) (before + 1) "a later response did not sweep";
        check (e.sweep_interval >= 16) "a later response reset the interval";
        (* Relief ends the pressure; collection points follow the interval again. *)
        e.budget_settled <- 0;
        Engine.enforce_budget ~words:0 e;
        check (not (Engine.memory_pressure e)) "relief kept the pressure";
        e.sweep_interval <- 64;
        e.sweep_wait <- 0;
        let before = sweeps () in
        Engine.periodic_collect e Producer_schedule.Trace.Producer;
        equal (sweeps ()) before "a collection point without pressure swept early" );
    ( "budget trimming works under an E queue mix",
      fun () ->
        (* The memory budget with the E queues: under a queue mix the production heaps are empty and a
           Passive clause lives in [live], the mix evaluations and every E heap. Trimming retires
           through Passive.invalidate; stale heap entries are skipped and compacted later. *)
        let theory = Tptp.parse group_cube in
        let e =
          Engine.create
            {
              Engine.default_config with
              limits = unlimited;
              budget = Engine.no_budget;
              strategy = e208_ported;
            }
        in
        Engine.prepare_ordering e (Theory.fixed theory);
        List.iter (Engine.add_axiom e) (Theory.fixed theory);
        let n = ref 0 in
        while live e && Engine.has_work e && List.length (Engine.trimmable e) < 40 && !n < 5000 do
          Engine.step e;
          incr n
        done;
        check (live e) "the fixture closed before Passive grew";
        check (Passive.mix_selections e.passive <> [||]) "e208 runs without a queue mix";
        let victims = Engine.trimmable e in
        let count = List.length victims / 2 in
        let length = Passive.length e.passive in
        Engine.trim_passive e count;
        equal e.metrics.budget_trimmed count "trimmed count";
        equal (Passive.length e.passive) (length - count) "Passive length after trimming";
        let trimmed =
          List.filter (fun (_, id) -> not (Tbl.Int.mem e.passive.live id)) victims |> List.map snd
        in
        equal (List.length trimmed) count "trimmed clauses still live";
        let selected = ref [] in
        for _ = 1 to 400 do
          if live e && Engine.has_work e then (
            Engine.step e;
            List.iter
              (fun id ->
                if Index.mem e.index id || Index.mem e.retained_index id then
                  selected := id :: !selected)
              trimmed)
        done;
        equal !selected [] "a trimmed clause was selected from a stale E heap entry";
        Engine.collect e;
        check (Passive.length e.passive >= 0) "compaction under a mix failed";
        match Engine.certificate e ~theory:(Theory.name theory) with
        | None -> ()
        | Some cert -> (
            match Kernel.check theory cert with
            | Ok _ -> ()
            | Error m -> failwith ("kernel rejected a proof after trimming under a mix: " ^ m)) );
    ( "a budget response past the deadline or a stop request records the stop and does no work",
      fun () ->
        (* The response runs between steps, outside [protect]: it must neither raise nor run a
           stage (trimming, sweep) that is linear in the search state once the worker should
           stop. A lean E worker's response took longer than the supervisor's stop grace. *)
        let theory = Tptp.parse group_cube in
        let b = 1 lsl 40 in
        let fixture ?(seconds = 60.) cancelled =
          let e =
            Engine.create ~cancelled
              {
                Engine.default_config with
                limits = { unlimited with seconds };
                budget = { Engine.heap_words = b; proof_nodes = 0 };
                strategy = e208_ported;
              }
          in
          Engine.prepare_ordering e (Theory.fixed theory);
          List.iter (Engine.add_axiom e) (Theory.fixed theory);
          let n = ref 0 in
          while live e && Engine.has_work e && List.length (Engine.trimmable e) < 40 && !n < 5000 do
            Engine.step e;
            incr n
          done;
          check (live e) "the fixture closed before Passive grew";
          let sweeps = ref 0 in
          Engine.set_budget_sweep e (fun ~first:_ -> incr sweeps);
          (* Armed: the next settled response would trim a quarter of Passive. *)
          e.budget_escalate <- true;
          e.budget_settled <- 0;
          (e, sweeps)
        in
        let seconds = 0.5 in
        let e, sweeps = fixture ~seconds (fun () -> false) in
        while Engine.elapsed e <= seconds do
          ignore (Sys.opaque_identity (Array.make 64 0))
        done;
        let passive = Passive.length e.passive in
        Engine.enforce_budget ~words:b e;
        equal e.stopped (Some "time limit") "the deadline was not recorded";
        check (e.finished <> None) "the deadline stop was not sealed";
        equal
          (e.metrics.budget_heap_responses, e.metrics.budget_trimmed, !sweeps)
          (0, 0, 0) "a response ran past the deadline";
        equal (Passive.length e.passive) passive "Passive was trimmed past the deadline";
        let stop = ref false in
        let e, sweeps = fixture (fun () -> !stop) in
        stop := true;
        Engine.enforce_budget ~words:b e;
        equal e.stopped (Some "cancelled") "the stop request was not recorded";
        equal (e.metrics.budget_trimmed, !sweeps) (0, 0) "a response ran after the stop request";
        (* A stop request during the trimming ends it there, before the sweep. *)
        let armed = ref false and polls = ref 0 in
        let e, sweeps =
          fixture (fun () ->
              !armed
              &&
              (incr polls;
               !polls > 6))
        in
        let quarter = List.length (Engine.trimmable e) / 4 in
        armed := true;
        Engine.enforce_budget ~words:b e;
        equal e.stopped (Some "cancelled") "a stop request during trimming was not recorded";
        check
          (e.metrics.budget_trimmed > 0 && e.metrics.budget_trimmed < quarter)
          (Printf.sprintf "trimming did not stop at the request (%d of %d)" e.metrics.budget_trimmed
             quarter);
        equal !sweeps 0 "the sweep ran after the stop request" );
    ( "the CLI budget is fixed per worker, in 64-bit footprint words",
      fun () ->
        (* The same for every worker count and platform: MiB of 8-byte words. *)
        let mib n = n * 131072 in
        equal (Engine.worker_budget ()).heap_words (mib 256) "default";
        equal (Engine.worker_budget ()) Engine.default_budget "default budget";
        equal (Engine.worker_budget ~mib:1000 ()).heap_words (mib 1000) "explicit budget";
        equal (Engine.worker_budget ~mib:1000 ()).proof_nodes Engine.default_budget.proof_nodes
          "an explicit budget changed the node budget";
        equal (Engine.worker_budget ~mib:0 ()) Engine.no_budget "0 does not disable";
        equal (Footprint.to_mib (Footprint.of_mib 768)) 768 "unit conversion";
        check
          (Engine.safety_words Engine.default_budget = 16 * mib 256
          && Engine.safety_words { Engine.heap_words = 1; proof_nodes = 0 } = mib 1024)
          "safety limit is not 16 budgets with a 1 GiB floor";
        check
          (try
             ignore (Engine.worker_budget ~mib:(-1) ());
             false
           with Invalid_argument _ -> true)
          "negative budget accepted" );
    ( "the reference reports its own heap",
      fun () ->
        let r =
          Scheduler.portfolio
            {
              config with
              reference = true;
              reference_config =
                { Reference.default_config with seconds = 0.3; max_trials = max_int };
              engine = { config.engine with limits = { unlimited with seconds = 0.3 } };
            }
            (fun () -> Theory.create "separation")
        in
        match r.reference_report with
        | None -> failwith "no reference report"
        | Some rr ->
            check (rr.trials > 4096) "reference too slow for a sample";
            check (rr.peak_domain_words > 0) "reference heap not sampled" );
    ( "proofs through withdrawn and returned instances pass the kernel",
      fun () ->
        (* Every reading is settled and over the budget until the first
           withdrawal, then under it, so instances leave and come back early. *)
        let b = 1 lsl 20 in
        let returned = ref 0 in
        List.iter
          (fun name ->
            let prepare (e : Engine.t) =
              e.heap_reading <-
                (fun () ->
                  e.budget_settled <- 0;
                  if e.metrics.budget_released > 0 then b / 2 else 3 * b / 2)
            in
            let r =
              Scheduler.run_search ~prepare
                {
                  config with
                  reference = false;
                  engine =
                    {
                      config.engine with
                      budget = { Engine.heap_words = b; proof_nodes = 0 };
                      limits = { unlimited with seconds = 2. };
                    };
                }
                (Theory.create name)
            in
            returned := !returned + r.engine.metrics.budget_reinjected;
            Option.iter
              (fun c ->
                check
                  (Result.is_ok (Kernel.check (Theory.create name) c))
                  (name ^ ": rejected proof"))
              r.certificate)
          [ "naive"; "separation-universal"; "foundation-self"; "mutated-separation"; "zf" ];
        check (!returned > 0) "no instance came back in any run" );
    ( "budget responses never change what the kernel accepts",
      fun () ->
        List.iter
          (fun budget ->
            List.iter
              (fun name ->
                let theory = Theory.create name in
                let r =
                  Scheduler.run
                    {
                      config with
                      engine =
                        { config.engine with budget; limits = { unlimited with seconds = 1. } };
                    }
                    theory
                in
                Option.iter
                  (fun c ->
                    check
                      (Result.is_ok (Kernel.check (Theory.create name) c))
                      (name ^ ": rejected proof"))
                  r.certificate;
                if r.certificate = None then
                  check
                    (r.engine.metrics.budget_responses > 0)
                    (name ^ ": unsolved without pressure"))
              [ "naive"; "separation-universal"; "foundation-self"; "mutated-separation" ])
          [
            { Engine.heap_words = 1; proof_nodes = 0 }; { Engine.heap_words = 0; proof_nodes = 12 };
          ] );
    ( "budget readings and responses do not depend on the collector or on other Domains",
      fun () ->
        (* With the scheduling costs on a stopped clock a bounded search depends on its input
           alone, and so must every footprint reading and every response: under any collector
           setting, with forced collections, and on another Domain while a third one allocates. *)
        let saved = !Engine.cost_clock in
        (Engine.cost_clock := fun () -> 0.);
        Fun.protect
          ~finally:(fun () -> Engine.cost_clock := saved)
          (fun () ->
            let budget = { Engine.heap_words = Footprint.of_mib 2; proof_nodes = 0 } in
            let run ?(between = fun _ -> ()) ?(reading = fun (_ : Engine.t) -> ()) () =
              let e =
                engine ~budget ~limits:{ unlimited with seconds = 120. } (Theory.create "zf")
              in
              reading e;
              let trace = ref [] and n = ref 0 in
              while live e && Engine.has_work e && !n < 4000 do
                let responses = e.metrics.budget_responses in
                Engine.step e;
                incr n;
                if e.metrics.budget_responses <> responses then
                  trace := (e.metrics.budget_checks, e.metrics.budget_trimmed) :: !trace;
                between !n
              done;
              let m = e.metrics in
              ( (m.budget_checks, m.budget_digest, m.peak_footprint_words, List.rev !trace),
                (m.budget_heap_responses, m.budget_cursor_drops, m.budget_trimmed),
                (m.given, m.generated, e.stopped) )
            in
            let base = run () in
            let _, (responses, drops, trimmed), _ = base in
            check (responses >= 3 && drops > 0 && trimmed > 0) "the fixture did not escalate";
            let gc = Gc.get () in
            let under params ?between () =
              Gc.set params;
              Fun.protect ~finally:(fun () -> Gc.set gc) (fun () -> run ?between ())
            in
            equal
              (under
                 { gc with minor_heap_size = 4096; space_overhead = 20 }
                 ~between:(fun n -> if n mod 500 = 0 then Gc.full_major ())
                 ())
              base "a small minor heap and eager collection changed the budget";
            equal
              (under { gc with minor_heap_size = 1 lsl 21; space_overhead = 400 } ())
              base "a large minor heap and lazy collection changed the budget";
            let stop = Atomic.make false in
            let noise =
              Domain.spawn (fun () ->
                  let keep = ref [] and n = ref 0 in
                  while not (Atomic.get stop) do
                    incr n;
                    keep := Array.make 4096 !n :: (if !n mod 64 = 0 then [] else !keep)
                  done;
                  !n)
            in
            let other = Domain.join (Domain.spawn (fun () -> run ())) in
            Atomic.set stop true;
            check (Domain.join noise > 0) "the noise Domain never ran";
            equal other base "another Domain under allocation load changed the budget";
            (* The collector's own reading, by contrast, is not the same twice. *)
            let gc_reading e = e.Engine.heap_reading <- Telemetry.budget_words in
            let control =
              List.map
                (fun params ->
                  Gc.set params;
                  Fun.protect ~finally:(fun () -> Gc.set gc) (fun () -> run ~reading:gc_reading ()))
                [ gc; { gc with minor_heap_size = 4096; space_overhead = 20 } ]
            in
            check
              (match control with [ a; b ] -> a <> b | _ -> false)
              "the collector's reading did not depend on the collector") );
    ( "a dropped Goal scan continues exactly where it stopped",
      fun () ->
        let t = Goal.create () in
        let guard () = () and alive _ = true in
        let fn name args = Fn (Original name, args) in
        let a = fn "a" [] and x = V (0, 0) in
        let lit positive atom = { positive; atom } in
        let note id clause =
          Goal.note t ~guard ~support:[] (id, 0)
            { id; clause = Clause.normalize clause; rule = Input (id, 0) }
        in
        (* A residual of height one also posts rewrite targets. *)
        let residual id clause =
          let step = { id = -id; clause = Clause.normalize clause; rule = Input (id, 0) } in
          ignore
            (Goal.add_state t ~guard ~owner:(id, 0) ~depth:4 ~weight:100
               {
                 step;
                 raw = step.clause;
                 parents = [];
                 leaves = [ (id, 0) ];
                 support = [];
                 height = 1;
               })
        in
        note 0
          [
            lit false (P ("p", [ fn "f" [ x ] ]));
            lit false (P ("q", [ x; fn "g" [ x; a ] ]));
            lit true (E (x, fn "f" [ a ]));
          ];
        for i = 1 to 12 do
          let c = fn ("c" ^ string_of_int i) [] in
          note i [ lit true (P ("p", [ fn "f" [ c ] ])); lit true (P ("p", [ x ])) ];
          note (100 + i) [ lit true (P ("q", [ c; fn "g" [ c; a ] ])) ];
          note (200 + i) [ lit true (E (fn "f" [ c ], c)) ];
          residual (300 + i) [ lit false (P ("r", [ fn "f" [ c ]; fn "g" [ c; c ] ])) ]
        done;
        let middle = t.epoch / 2 and epoch = t.epoch in
        let proof = (Tbl.Int.find t.states 0).proof in
        let key (parents, _) = List.map (fun (p : Goal.recipe) -> p.step.id) parents in
        let whole since =
          List.of_seq (Seq.map key (fst (Goal.cursor ~since t ~guard ~alive proof)))
        in
        (* Drop and rebuild after every element. Re-entering a posting without
           skipping what it already yielded would never get past it. *)
        let dropped since bound =
          let stream, scan = Goal.cursor ~since t ~guard ~alive proof in
          let rec go n acc stream =
            if n > bound then failwith "drops made the scan repeat itself";
            match stream () with
            | Seq.Nil -> List.rev acc
            | Seq.Cons (element, _) ->
                Equality_index.detach scan.equality;
                go (n + 1) (key element :: acc)
                  (fst (Goal.cursor ~upto:epoch ~from:scan t ~guard ~alive proof))
          in
          go 0 [] stream
        in
        List.iter
          (fun since ->
            let full = whole since in
            check (List.length full > 40) "fixture scan is too short";
            check (since > 0 || List.mem [ 0 ] full) "a replay scan lacked its unary inferences";
            equal
              (List.sort compare (dropped since (2 * List.length full)))
              (List.sort compare full) "drops skipped or repeated attempts")
          [ 0; middle ] );
    ( "Goal still refutes when every suspended cursor is dropped after every slice",
      fun () ->
        let _, kept, _ = goal_refutation ~drop:false in
        check (kept.root <> None) "fixture is not refuted by Goal alone";
        check (kept.goals.metrics.resumed > 0) "fixture never resumed a cursor";
        let theory, e, dropped = goal_refutation ~drop:true in
        check (dropped > 0) "no suspended cursor was dropped";
        check (e.root <> None) "cursor drops lost the Goal refutation";
        equal e.metrics.given 0 "fixture used ordinary saturation";
        Engine.collect e;
        match Engine.certificate e ~theory:(Theory.name theory) with
        | None -> failwith "no certificate"
        | Some c -> ( match Kernel.check theory c with Ok _ -> () | Error error -> failwith error)
    );
  ]

let () = run tests
