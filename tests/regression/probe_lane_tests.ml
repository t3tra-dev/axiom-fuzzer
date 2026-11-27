open Axiom_fuzzer
open Test_support

(* Schema probe lane (lib/scheduler/probe_lane.ml) and its finite-model
   helpers (lib/synthesis/semantic.ml), and its observational source
   (lib/synthesis/observational.ml). The library has no condition prior;
   tests that exercise the lane's experiment hook ([prior]) use the small
   test-local streams below (the schema benchmark's Lawvere prior is checked by
   [schema_bench prior-check]). *)

let lane_config = { config with reference = false }

(* ~(x in x) first, then x in x. *)
let russell_first : Probe_lane.prior =
 fun _ ->
  List.to_seq
    [
      Wire.Neg (Wire.Pred ("member", [ Wire.F 0; Wire.F 0 ]));
      Wire.Pred ("member", [ Wire.F 0; Wire.F 0 ]);
    ]

(* Many pairwise distinct conditions x in w_i (parameters, closed by the instance). *)
let many_conditions : Probe_lane.prior =
 fun _ -> Seq.init 1_000 (fun i -> Wire.Pred ("member", [ Wire.F 0; Wire.F (i + 1) ]))

let prior_lane = { Probe_lane.fixed_escalate with prior = Some russell_first }

let contains text part =
  let n = String.length part in
  let rec go i = i + n <= String.length text && (String.sub text i n = part || go (i + 1)) in
  go 0

let roundtrip theory (cert : Wire.certificate) =
  let decoded = Certificate_io.decode (Certificate_io.encode cert) in
  match Kernel.check (Theory.copy theory) decoded with
  | Ok _ -> ()
  | Error e -> failwith ("probe certificate rejected after roundtrip: " ^ e)

let create_lane ?(inject = fun _ _ _ -> ()) ?admit ?synthesis ?bounds lane theory =
  Probe_lane.create ~started:(Telemetry.now ()) ?admit ?synthesis ?bounds ~inject lane config.engine
    theory

let drive lane ~turns =
  let rec go n =
    if n > 0 && Probe_lane.has_work lane then (
      Probe_lane.turn lane;
      go (n - 1))
  in
  go turns

let first_parameters theory schema n =
  let rec take k seq acc =
    if k = 0 then List.rev acc
    else
      match seq () with
      | Seq.Nil -> List.rev acc
      | Seq.Cons (None, rest) -> take k rest acc
      | Seq.Cons (Some p, rest) -> take (k - 1) rest (p :: acc)
  in
  take n (Theory.enumerate theory schema) []

(* A small arithmetic signature for registered test schemas: p(s^n(z)). *)
let numeral_sg = Signature.make ~functions:[ ("z", 0); ("s", 1) ] ~predicates:[ ("p", 1) ]
let rec numeral n = if n = 0 then Wire.App ("z", []) else Wire.App ("s", [ numeral (n - 1) ])

(* A registered integer schema: [expand n] in an arena, validated against the
   same Wire formula. *)
let int_schema ~name expand =
  Theory.Schema.create ~name ~revision:"1" ~encode:string_of_int
    ~decode:(fun d -> Option.bind (int_of_string_opt d) (fun n -> if n < 0 then None else Some n))
    ~enumerate:(fun _ _ -> Seq.ints 0)
    ~expand:(fun a n -> Wire.import a (expand n))
    ~check:(fun _ n f -> f = expand n)
    ()

(* "quiet": an infinite stream of harmless instances (each, whatever n, says
   that the first six numerals are pairwise distinct: false in every
   structure with at most 4 elements, so a pool calls every one a killer, yet
   consistent). "needle": p(s^n(z)), contradicting the fixed axiom
   ~p(s^3(z)) at n = 3. *)
let distinct _ =
  let k = 6 in
  Wire.Conj
    (List.concat
       (List.init k (fun i ->
            List.init (k - i - 1) (fun j -> Wire.Neg (Wire.Eq (numeral i, numeral (i + j + 1)))))))

let quiet = int_schema ~name:"quiet" distinct
let needle = int_schema ~name:"needle" (fun n -> Wire.Pred ("p", [ numeral n ]))

let two_schemas () =
  let base =
    Theory.custom ~name:"two-schemas" numeral_sg
      [ ("not-p3", Wire.Neg (Wire.Pred ("p", [ numeral 3 ]))) ]
  in
  Theory.register_schema (Theory.register_schema base quiet) needle

let schema_named theory name =
  List.find (fun k -> Wire.schema_name k = name) (Theory.schemas theory)

let found_in theory (t : Probe_lane.t) name =
  match t.winning with Some item -> item.schema = schema_named theory name | None -> false

let tests =
  [
    ( "lane off runs exactly the main search and reports no lane",
      fun () ->
        let r =
          Scheduler.run { lane_config with lane = Probe_lane.disabled } (Theory.create "naive")
        in
        check (r.certificate <> None) "main search lost naive";
        check
          (String.starts_with ~prefix:"heuristic:" r.proof_source)
          "lane-off proof not heuristic";
        check ((List.hd r.workers).lane = None) "lane-off worker carried lane statistics";
        check (not (contains r.reason "[lane:")) "lane-off reason mentions the lane" );
    ( "a probe certificate uses the lane's own ID space and survives a kernel roundtrip",
      fun () ->
        (* The first condition of the test prior is ~(x in x). A prior is
           guided synthesis, so guidance is on (with a guided budget); with no
           exhaustive budget the main engine has no clause to work on, so the
           lane refutes naive by itself. *)
        let theory = Theory.create "naive" in
        let r =
          Scheduler.run
            {
              lane_config with
              guided = true;
              max_instances = 0;
              max_guided_instances = 4;
              lane = prior_lane;
            }
            theory
        in
        let cert = match r.certificate with Some c -> c | None -> failwith r.reason in
        equal r.proof_source "probe:0" "naive was not refuted by the lane";
        roundtrip theory cert;
        let instances =
          List.filter (fun (a : Wire.axiom) -> Wire.is_instance a.origin) cert.axioms
        in
        equal (List.length instances) 1 "a probe certificate has exactly one instance";
        let instance = List.hd instances in
        equal instance.axiom_id
          (List.length (Theory.fixed theory))
          "probe instance outside the lane ID space";
        equal instance.name "comprehension_0" "probe instance name does not follow its ID";
        check (r.axioms = cert.axioms) "result axioms are not the probe certificate's axioms";
        let w = List.hd r.workers in
        equal w.guided_used 1 "a prior lane proof was not attributed to the guided budget";
        match w.lane with
        | Some s -> equal s.winner "prior" "lane statistics do not name the prior winner"
        | None -> failwith "lane statistics missing" );
    ( "probes never consume main-engine instance IDs",
      fun () ->
        (* Pool mode scans and probes killers while the main engine injects;
           the main engine's instance IDs stay contiguous from the first ID
           after the fixed axioms (the prototype's scan bumped this counter). *)
        let theory = Theory.create "zf" in
        let ids = ref [] in
        let cfg =
          {
            lane_config with
            lane = { Probe_lane.default with prior = Some russell_first };
            max_size = 0;
            max_instances = 40;
            max_guided_instances = 40;
            engine =
              {
                config.engine with
                (* A given-clause cap, not the wall clock, ends the run, and the scheduling costs
                   run on a stopped clock: the lane gets the same turns on a loaded machine. *)
                limits = { config.engine.limits with seconds = 120.; max_given = 400 };
              };
          }
        in
        let r =
          let saved = !Engine.cost_clock in
          (Engine.cost_clock := fun () -> 0.);
          Fun.protect
            ~finally:(fun () -> Engine.cost_clock := saved)
            (fun () ->
              Scheduler.run ~on_instance:(fun tr -> ids := tr.axiom.axiom_id :: !ids) cfg theory)
        in
        let ids = List.rev !ids in
        let first = List.length (Theory.fixed theory) in
        check (ids <> []) "main engine injected nothing";
        equal ids (List.init (List.length ids) (fun i -> first + i)) "main instance IDs have gaps";
        match (List.hd r.workers).lane with
        | Some s -> check (s.probes > 0) "the lane never probed"
        | None -> failwith "lane did not run on zf" );
    ( "the look-ahead scan does not mark rejected instances as seen",
      fun () ->
        (* separation's instances are true in the one-element empty-membership
           model, so no instance is a killer: every scanned one is rejected. *)
        let theory = Theory.create "separation" in
        let lane = create_lane Probe_lane.with_pool theory in
        let rec build n =
          if lane.builder <> None && n > 0 then (
            Probe_lane.turn lane;
            build (n - 1))
        in
        build 10_000;
        check (Probe_lane.ready_pool lane <> None) "pool was not built";
        Probe_lane.scan lane;
        check (lane.stats.scanned > 0) "scan examined nothing";
        equal lane.stats.killers 0 "a separation instance was classified as a killer";
        let schema = List.hd (Theory.schemas theory) in
        let scanned = first_parameters theory schema (min 8 lane.stats.scanned) in
        List.iter
          (fun p ->
            check (not (Hashtbl.mem lane.queued (schema, p))) "a rejected instance was marked seen")
          scanned;
        let before = Probe_lane.Pending.length lane.fresh in
        List.iter (Probe_lane.offer lane schema) scanned;
        equal
          (Probe_lane.Pending.length lane.fresh)
          (before + List.length scanned)
          "an injected instance seen by the scan was not queued for its probe" );
    ( "a killer from the scan enters the main engine after failing every level",
      fun () ->
        let lane =
          { Probe_lane.with_pool with escalations = 0; killer_level = 0; instance_budget = 1 }
        in
        let theory = Theory.create "separation" in
        let injected = ref 0 in
        let t = create_lane ~inject:(fun _ _ _ -> incr injected) lane theory in
        let schema = List.hd (Theory.schemas theory) in
        let p = List.hd (first_parameters theory schema 1) in
        Probe_lane.enqueue t t.killers
          {
            Probe_lane.schema;
            parameter = p;
            source = Scanned;
            level = 0;
            killer = true;
            shape = 0;
          };
        t.pool <- Some { Semantic.empty with models = [] };
        t.builder <- None;
        Probe_lane.escalate t t.killers (Option.get (Probe_lane.take t t.killers)) `Settled;
        equal !injected 1 "a failed scanned killer was not handed to the main engine" );
    ( "enumerated theories get FIFO probes in their own ID space",
      fun () ->
        (* Theory.of_enumerator has an unrestricted signature: no pool and no
           prior, but injected stages are still probed in isolation. *)
        let p = Wire.Pred ("p", [ Wire.App ("c", []) ]) in
        let theory =
          Theory.of_enumerator ~name:"lane-enumerated" ~revision:"1" ~step:(function
            | 3 -> Some (Wire.Conj [ p; Wire.Neg p ])
            | n when n mod 2 = 0 -> Some (Wire.Pred ("q" ^ string_of_int n, []))
            | _ -> None)
        in
        let lane = create_lane { Probe_lane.default with prior = Some russell_first } theory in
        check (lane.finite = None) "an unrestricted signature produced a finite one";
        check (lane.builder = None) "a pool was configured over an unrestricted signature";
        let schema = List.hd (Theory.schemas theory) in
        List.iter (Probe_lane.offer lane schema) (first_parameters theory schema 3);
        drive lane ~turns:10;
        (match lane.result with
        | None -> failwith "the contradictory stage was not refuted by its probe"
        | Some cert ->
            roundtrip theory cert;
            List.iter
              (fun (a : Wire.axiom) -> equal a.axiom_id 0 "enumerated probe used a main-engine ID")
              cert.axioms);
        let r = Scheduler.run { lane_config with max_size = 0; lane = Probe_lane.default } theory in
        check (r.certificate <> None) "enumerated theory not refuted";
        match (List.hd r.workers).lane with
        | Some s -> check (s.offered + s.scanned > 0) "lane saw no enumerated stage"
        | None -> failwith "lane disabled for an enumerated theory" );
    ( "the fixed-axiom probe is resumed in growing slices and refutes inconsistent fixed axioms",
      fun () ->
        let sg = Signature.make ~functions:[ ("a", 0) ] ~predicates:[ ("member", 2) ] in
        let a = Wire.App ("a", []) in
        let theory =
          Theory.custom ~name:"lane-fixed" sg
            [
              ("inside", Wire.Pred ("member", [ a; a ]));
              ("outside", Wire.Neg (Wire.Pred ("member", [ a; a ])));
            ]
        in
        (* No schema here; drive the lane directly. *)
        let lane = create_lane Probe_lane.fixed_escalate theory in
        drive lane ~turns:10;
        match lane.result with
        | Some cert ->
            roundtrip theory cert;
            equal lane.stats.winner "fixed" "fixed probe did not win"
        | None -> failwith "fixed probe missed an inconsistent fixed axiom set" );
    ( "the default lane has no condition prior and spreads its probes",
      fun () ->
        (* The library defaults use only general mechanisms: no preset sets the
           experiment hook, so axiom-fuzz never runs a condition prior. *)
        List.iter
          (fun (name, (l : Probe_lane.config)) ->
            check (Option.is_none l.prior) (name ^ " carries a condition prior"))
          [
            ("Scheduler.default_config.lane", Scheduler.default_config.lane);
            ("default", Probe_lane.default);
            ("with_pool", Probe_lane.with_pool);
            ("fixed_escalate", Probe_lane.fixed_escalate);
            ("fifo", Probe_lane.fifo);
            ("disabled", Probe_lane.disabled);
          ];
        let l = Scheduler.default_config.lane in
        check (l.enabled && l.fixed && l.pool && l.breadth) "the default lane lost a mechanism";
        (* Without a prior the prior sub-lane never runs, even with guidance. *)
        let t = create_lane Probe_lane.default (Theory.create "naive") in
        check (not (Probe_lane.prior_ready t)) "a prior sub-lane without a prior" );
    ( "the incremental pool equals the one-shot pool and is bounded by evaluation steps",
      fun () ->
        let theory = Theory.create "zf" in
        let axioms = List.map (fun (a : Wire.axiom) -> a.formula) (Theory.fixed theory) in
        let whole = Semantic.pool Signature.sets axioms in
        let b = Semantic.builder ~budget:20_000_000 Signature.sets axioms in
        let rec go n =
          match Semantic.advance b ~quota:1_000 with Some p -> (p, n) | None -> go (n + 1)
        in
        let sliced, slices = go 1 in
        check (slices > 1) "pool construction was not sliced";
        equal (List.length sliced.models) (List.length whole.models) "sliced pool differs";
        equal sliced.axioms_used whole.axioms_used "sliced pool kept other axioms";
        check (whole.axioms_used < whole.axioms_total) "infinity was not dropped from the pool";
        let tiny = Semantic.builder ~budget:100 Signature.sets axioms in
        (match Semantic.advance tiny ~quota:max_int with
        | Some _ -> ()
        | None -> failwith "budget did not end construction");
        check (Semantic.builder_steps tiny < 100 + 20_000) "evaluation budget overrun" );
    ( "the lane obeys a zero instance budget (--max-instances 0)",
      fun () ->
        (* No instance may be used, so naive stays unrefuted, also by a look-ahead or diagonal
           probe of the lane. *)
        List.iter
          (fun lane ->
            let r =
              Scheduler.run
                {
                  lane_config with
                  guided = true;
                  max_size = 0;
                  max_instances = 0;
                  max_guided_instances = 0;
                  lane;
                }
                (Theory.create "naive")
            in
            check (r.certificate = None) "the lane used an instance outside a zero budget";
            check (contains r.reason "schema instance limit") ("unexpected reason " ^ r.reason);
            match (List.hd r.workers).lane with
            | Some s ->
                equal (s.charged_exhaustive + s.charged_guided) 0 "the lane charged an instance";
                equal s.probes 0 "the lane probed an instance"
            | None -> failwith "lane did not run")
          [ Probe_lane.default; prior_lane; Probe_lane.fifo ] );
    ( "lane probes are charged to the generator budgets and stop when they are spent",
      fun () ->
        (* Direct lane, no main engine: an admit hook with two exhaustive and
           one guided slot. The look-ahead (fifo) stops after two charged
           instances; nothing else is probed. *)
        let theory = two_schemas () in
        let used = Hashtbl.create 8 and slots = ref 2 in
        let admit (source : Probe_lane.source) schema p : Probe_lane.admission =
          if Hashtbl.mem used (schema, p) then Free
          else if source = Scanned && !slots > 0 then (
            decr slots;
            Hashtbl.replace used (schema, p) ();
            Charged)
          else Refused
        in
        let t = create_lane ~admit Probe_lane.fifo theory in
        drive t ~turns:50;
        equal t.stats.charged_exhaustive 2 "the look-ahead did not use exactly its two slots";
        equal t.stats.probes 2 "a probe used an instance outside the budget";
        check (t.stats.refused >= 1) "the spent budget was never noticed";
        check (not (Probe_lane.scan_ready t)) "the look-ahead continued after its budget";
        check (t.result = None) "refuted outside the budget";
        (* Without guided synthesis a condition prior never runs. *)
        let t = create_lane ~synthesis:false prior_lane (Theory.create "naive") in
        check (not (Probe_lane.prior_ready t)) "a prior without guided synthesis" );
    ( "the restored guidance budget contract holds with the lane on",
      fun () ->
        (* synthesis_tests' budget test, with the default lane: guided = false
           must not refute naive at max_size 1 (no prior, bounded
           look-ahead), and the lane's look-ahead honours max_size. *)
        let bounded =
          {
            lane_config with
            max_size = 1;
            max_instances = 4;
            max_guided_instances = 4;
            engine = { config.engine with limits = { config.engine.limits with max_given = 300 } };
          }
        in
        let r = Scheduler.run bounded (Theory.create "naive") in
        check (r.certificate = None) "bounded lane refuted naive without guidance";
        match (List.hd r.workers).lane with
        | Some s -> check (s.charged_guided = 0) "a prior ran without guided synthesis"
        | None -> failwith "lane did not run" );
    ( "the look-ahead serves every schema, not only the first",
      fun () ->
        (* The needle is in the second schema; the first is infinite. Before
           the fix the scan spent its whole budget on the first stream. *)
        List.iter
          (fun lane ->
            let theory = two_schemas () in
            let t = create_lane lane theory in
            drive t ~turns:400;
            check (t.result <> None) "needle in the second schema never probed";
            check (found_in theory t "needle") "the win did not come from the second schema";
            roundtrip theory (Option.get t.result))
          [ Probe_lane.fifo; Probe_lane.with_pool; Probe_lane.default ] );
    ( "arrival-order probes keep their share while pool killers wait",
      fun () ->
        (* 200 harmless killers wait; the needle arrives from the main engine.
           Before the fix every killer was probed first. *)
        let theory = two_schemas () in
        let t = create_lane { Probe_lane.with_pool with scan = 0 } theory in
        let rec build n =
          if t.builder <> None && n > 0 then (
            Probe_lane.turn t;
            build (n - 1))
        in
        build 10_000;
        check (Probe_lane.ready_pool t <> None) "pool was not built";
        let q = schema_named theory "quiet" in
        List.iter
          (fun p ->
            Probe_lane.enqueue t t.killers
              {
                Probe_lane.schema = q;
                parameter = p;
                source = Scanned;
                level = 0;
                killer = true;
                shape = 0;
              })
          (first_parameters theory q 200);
        Probe_lane.offer t (schema_named theory "needle")
          (List.nth (first_parameters theory (schema_named theory "needle") 4) 3);
        drive t ~turns:20;
        check (found_in theory t "needle") "the arrival-order needle waited behind the killers";
        check (t.stats.probes < 20) "arrival order got no share" );
    ( "a pool that calls most candidates killers stops ranking",
      fun () ->
        (* Every "quiet" instance is false in all small structures. *)
        let base = Theory.custom ~name:"weak-pool" numeral_sg [] in
        let theory = Theory.register_schema base quiet in
        let t =
          create_lane
            { Probe_lane.with_pool with killer_level = 0; escalations = 0; instance_budget = 4_000 }
            theory
        in
        drive t ~turns:40;
        check t.stats.weak
          (Printf.sprintf
             "a non-discriminating pool kept ranking (pool %d, examined %d, killers %d, turns %d)"
             t.stats.pool_models t.examined t.scan_killers t.stats.turns);
        check (t.stats.killers >= 64) "the scan did not examine enough candidates";
        check (Probe_lane.Pending.is_empty t.killers) "demoted killers kept their priority" );
    ( "the look-ahead never starts a step predicted to end after the deadline",
      fun () ->
        let theory = two_schemas () in
        (* 50 ms before the deadline, with a previous step of 1 s. *)
        let started = Telemetry.now () -. (config.engine.limits.seconds -. 0.05) in
        let t =
          Probe_lane.create ~started ~inject:(fun _ _ _ -> ()) Probe_lane.fifo config.engine theory
        in
        List.iter (fun (s : Probe_lane.stream) -> s.s_seconds <- 1.) t.scan_streams;
        Probe_lane.scan t;
        equal t.stats.scanned 0 "a slow stream was stepped next to the deadline";
        let until = Telemetry.now () +. 0.06 in
        while Telemetry.now () < until do
          ()
        done;
        Probe_lane.turn t;
        equal t.stats.turns 0 "a lane turn started after the deadline" );
    ( "the look-ahead stops at its per-worker cap",
      fun () ->
        (* Only the harmless infinite schema: nothing ends the look-ahead but
           its cap. *)
        let theory = Theory.register_schema (Theory.custom ~name:"capped" numeral_sg []) quiet in
        let t = create_lane { Probe_lane.fifo with scan_cap = 30; instance_budget = 50 } theory in
        drive t ~turns:400;
        equal t.stats.scanned 30 "the look-ahead did not stop at its cap";
        check (not (Probe_lane.scan_ready t)) "the look-ahead kept its streams after the cap" );
    ( "lane engines get their own stored-proof-node budget",
      fun () ->
        let t = create_lane { Probe_lane.fifo with probe_retained = 7 } (Theory.create "zf") in
        let e = Probe_lane.engine t ~retained:t.config.probe_retained in
        equal e.config.limits.max_retained 7 "probe engine memory budget ignored";
        let e = Probe_lane.engine t ~retained:max_int in
        equal e.config.limits.max_retained config.engine.limits.max_retained
          "the main engine's own bound was exceeded" );
    ( "lane engines inherit the worker's memory budget, strategy and prepare hook",
      fun () ->
        (* A lane engine is one of the worker's engines. It carries the
           worker's memory budgets (it answers the worker's heap pressure like
           the main engine and slice probes do), runs the worker's strategy
           with its precedence prepared from the fixed axioms, and gets the
           worker's [prepare] hook. *)
        let budget = { Engine.default_budget with heap_words = 12345 } in
        let strategy = Strategy.of_name "e208" in
        let engine_config = { config.engine with budget; strategy } in
        let prepared = ref 0 in
        let t =
          Probe_lane.create ~worker:1 ~workers:2 ~phase:3
            ~prepare:(fun _ -> incr prepared)
            ~started:(Telemetry.now ())
            ~inject:(fun _ _ _ -> ())
            Probe_lane.fifo engine_config (Theory.create "zf")
        in
        let e = Probe_lane.engine t ~retained:t.config.probe_retained in
        check (e.config.budget = budget) "the lane engine lost the worker's memory budget";
        check (e.config.strategy == strategy) "the lane engine lost the worker's strategy";
        equal !prepared 1 "prepare did not run on the lane engine";
        equal t.phase 3 "the lane did not take the worker's queue phase";
        (* Through the scheduler: every lane engine of the worker gets [prepare]. *)
        let engines = ref 0 in
        let r =
          Scheduler.run_search
            ~prepare:(fun _ -> incr engines)
            {
              lane_config with
              guided = true;
              max_instances = 0;
              max_guided_instances = 4;
              lane = prior_lane;
            }
            (Theory.create "naive")
        in
        equal r.proof_source "probe:0" "naive was not refuted by the lane";
        check (!engines >= 2) "prepare did not reach the lane engines" );
    ( "a lane turn is due only within its share of the work",
      fun () ->
        let t = create_lane Probe_lane.fifo (Theory.create "naive") in
        check (Probe_lane.due t) "a fresh lane is not due";
        (* Pretend the lane did all the work so far: it is over its share. *)
        t.stats.instance_work <- 1e12;
        check (not (Probe_lane.due t)) "a lane over its share is due";
        t.stats.instance_work <- 0.;
        check (Probe_lane.due t) "a lane back within its share is not due" );
    ( "workers split a condition prior by index modulo the worker count",
      fun () ->
        let theory () = Theory.create "naive" in
        let take ?(workers = 2) worker =
          let t =
            Probe_lane.create ~worker ~workers ~started:(Telemetry.now ())
              ~inject:(fun _ _ _ -> ())
              { Probe_lane.fixed_escalate with prior = Some many_conditions; prior_cap = 40 }
              config.engine (theory ())
          in
          let rec go acc =
            match Probe_lane.next_prior t with
            | Some item -> go (Theory.parameter_text t.theory item.parameter :: acc)
            | None -> List.rev acc
          in
          go []
        in
        let take_all () = take ~workers:1 0 in
        (* naive has one schema, so each stream index yields at most one item. *)
        let w0 = take 0 and w1 = take 1 in
        equal (List.length w0) 20 "worker 0 did not take its half";
        equal (List.length w1) 20 "worker 1 did not take its half";
        check (List.for_all (fun x -> not (List.mem x w1)) w0) "the workers' shares overlap";
        let single = take_all () in
        equal (List.length single) 40 "one worker alone did not take every index" );
    ( "breadth: every schema gets an equal share of the probe work",
      fun () ->
        (* 200 harmless "quiet" instances arrive before one "needle" instance.
           In arrival order the needle waits behind all of them; with breadth
           its schema has no probe work yet, so it is probed next. *)
        let run_with lane =
          let theory = two_schemas () in
          let t = create_lane { lane with Probe_lane.scan = 0 } theory in
          let q = schema_named theory "quiet" and n = schema_named theory "needle" in
          List.iter (Probe_lane.offer t q) (first_parameters theory q 200);
          Probe_lane.offer t n (List.nth (first_parameters theory n 4) 3);
          drive t ~turns:5;
          (theory, t)
        in
        let theory, t = run_with { Probe_lane.fifo with breadth = true } in
        check (found_in theory t "needle") "breadth left the needle schema waiting";
        roundtrip theory (Option.get t.result);
        equal t.stats.schemas_probed 2 "breadth did not probe both schemas";
        let theory, t = run_with Probe_lane.fifo in
        check (not (found_in theory t "needle")) "arrival order reached the needle early" );
    ( "breadth: no shape takes more than its cap while other shapes wait",
      fun () ->
        (* One schema, two shapes: instance 7 is p(s^3(z)) (refuted by the fixed
           axiom), every other one the same harmless conjunction. It arrives
           last; with breadth its shape is probed as soon as the first shape is
           over its cap. *)
        let mixed =
          int_schema ~name:"mixed" (fun k ->
              if k = 7 then Wire.Pred ("p", [ numeral 3 ]) else distinct k)
        in
        let make () =
          Theory.register_schema
            (Theory.custom ~name:"two-shapes" numeral_sg
               [ ("not-p3", Wire.Neg (Wire.Pred ("p", [ numeral 3 ]))) ])
            mixed
        in
        let run_with lane =
          let theory = make () in
          let t = create_lane { lane with Probe_lane.scan = 0 } theory in
          let m = List.hd (Theory.schemas theory) in
          let ps = first_parameters theory m 300 in
          let needle = List.nth ps 7 in
          List.iter (Probe_lane.offer t m) (List.filter (fun p -> p != needle) ps);
          Probe_lane.offer t m needle;
          drive t ~turns:5;
          t
        in
        let t = run_with { Probe_lane.fifo with breadth = true } in
        check (t.result <> None) "the second shape waited behind the first";
        equal t.stats.shapes_probed 2 "breadth did not probe both shapes";
        let t = run_with Probe_lane.fifo in
        check (t.result = None) "arrival order reached the last shape early" );
    ( "the lane reports its breadth",
      fun () ->
        let theory = two_schemas () in
        let t = create_lane Probe_lane.default theory in
        drive t ~turns:400;
        let s = t.stats in
        equal s.schemas 2 "schema count";
        check (s.schemas_probed = 2 && s.shapes_probed >= 2) "breadth counters did not move";
        check (s.probe_work > 0.) "no probe work recorded";
        let top = Probe_lane.top_schema_share s and shape = Probe_lane.top_shape_share s in
        check (top > 0. && top <= 1. && shape > 0. && shape <= top) "inconsistent shares";
        check (contains (Probe_lane.summary t) " schemas=2/2 ") "summary lacks the breadth fields"
    );
    ( "observational tables agree with direct evaluation in every pool model",
      fun () ->
        (* A signature with a constant and a unary function exercises every
           atom form; the pool has no axioms, so it samples arbitrary small
           structures. *)
        let sg = Signature.make ~functions:[ ("a", 0); ("g", 1) ] ~predicates:[ ("member", 2) ] in
        let pool = Semantic.pool ~budget:2_000_000 ~capacity:24 sg [] in
        check (List.length pool.models >= 8) "pool too small";
        let e = Observational.create sg pool in
        let seen = ref [] in
        Observational.advance e ~quota:max_int ~emit:(fun f table ->
            seen := (f, table) :: !seen;
            List.length !seen >= 1_500);
        check (List.length !seen = 1_500) "too few conditions";
        let rec sub_t = function
          | Wire.F 0 -> Wire.App ("__x", [])
          | Wire.App (s, ts) -> Wire.App (s, List.map sub_t ts)
          | t -> t
        in
        let rec sub = function
          | Wire.Pred (p, ts) -> Wire.Pred (p, List.map sub_t ts)
          | Wire.Eq (a, b) -> Wire.Eq (sub_t a, sub_t b)
          | Wire.Neg f -> Wire.Neg (sub f)
          | Wire.Conj fs -> Wire.Conj (List.map sub fs)
          | Wire.Disj fs -> Wire.Disj (List.map sub fs)
          | Wire.All f -> Wire.All (sub f)
          | Wire.Ex f -> Wire.Ex (sub f)
          | f -> f
        in
        let models = Observational.models e in
        let quantified = ref 0 in
        List.iter
          (fun (f, table) ->
            let w = Observational.condition f in
            let rec quantifies = function
              | Wire.All _ | Wire.Ex _ -> true
              | Wire.Neg f -> quantifies f
              | Wire.Conj fs | Wire.Disj fs -> List.exists quantifies fs
              | _ -> false
            in
            if quantifies w then incr quantified;
            Array.iteri
              (fun i (m : Semantic.model) ->
                let ext = Observational.extension e table i in
                for x = 0 to m.size - 1 do
                  let funs = Hashtbl.copy m.funs in
                  Hashtbl.replace funs ("__x", 0) [| x |];
                  let m' = { m with funs } in
                  match Semantic.eval m' (sub w) with
                  | Some v ->
                      if v <> ((ext lsr x) land 1 = 1) then
                        failwith "a truth table disagrees with direct evaluation"
                  | None -> failwith "evaluation failed"
                done)
              models)
          !seen;
        check (!quantified > 100) "too few quantified conditions checked" );
    ( "observational classes are distinct, grow by size and repeat exactly",
      fun () ->
        let pool = Semantic.pool ~budget:2_000_000 Signature.sets [] in
        let run () = Observational.enumerate ~limit:2_000 Signature.sets pool in
        let first = run () and again = run () in
        equal (List.length first) 2_000 "too few conditions";
        check (first = again) "the enumeration is not deterministic";
        (* Level-1 sizes never decrease (buckets are built by diagonal). *)
        ignore
          (List.fold_left
             (fun last f ->
               let s = Observational.size f in
               check (s >= last) "a smaller condition came later";
               s)
             0 first);
        (* One formula per class: x in x is kept, its double negation never is. *)
        let xx = Observational.Pred ("member", [ Observational.Var 0; Observational.Var 0 ]) in
        check (List.mem xx first) "x in x is missing";
        check (List.mem (Observational.Not xx) first) "~(x in x) is missing";
        check
          (not (List.mem (Observational.Not (Observational.Not xx)) first))
          "double negation kept";
        let tables = Hashtbl.create 64 in
        let e = Observational.create Signature.sets pool in
        Observational.advance e ~quota:max_int ~emit:(fun _ table ->
            check (not (Hashtbl.mem tables table)) "two conditions share a truth table";
            Hashtbl.add tables table ();
            Hashtbl.length tables >= 2_000) );
    ( "the observational bank stays within its word cap",
      fun () ->
        let pool = Semantic.pool ~budget:2_000_000 Signature.sets [] in
        let e = Observational.create ~word_cap:50_000 Signature.sets pool in
        Observational.advance e ~quota:max_int ~emit:(fun _ _ -> false);
        check (Observational.finished e) "the capped bank did not finish";
        check (Observational.words e <= 50_000 + 200) "the bank overran its word cap";
        check (Observational.levels e >= 2) "the pool allows too few levels" );
    ( "the observational source alone refutes naive comprehension",
      fun () ->
        (* No main engine and no look-ahead: the only conditions are the
           observational ones. Its proof is an ordinary probe certificate. *)
        let theory = Theory.create "naive" in
        let admit (source : Probe_lane.source) _ _ : Probe_lane.admission =
          match source with Observed -> Charged | Prior | Scanned | Injected -> Free
        in
        let t = create_lane ~admit { Probe_lane.default with scan = 0; fixed = false } theory in
        drive t ~turns:2_000;
        (match t.result with
        | Some cert -> roundtrip theory cert
        | None -> failwith ("observational source found nothing" ^ Probe_lane.summary t));
        equal t.stats.winner "observed" "the refutation did not come from the source";
        check (t.stats.oe_offered > 0 && t.stats.oe_killers > 0) "no condition was offered";
        check (t.stats.charged_guided >= 1) "the probe was not charged to the guided budget";
        check (contains (Probe_lane.summary t) " oe=") "summary lacks the source's fields" );
    ( "the observational source needs guided synthesis and its budget",
      fun () ->
        let theory = Theory.create "naive" in
        (* Guided synthesis off: no conditions at all. *)
        let off = create_lane ~synthesis:false { Probe_lane.default with scan = 0 } theory in
        drive off ~turns:400;
        equal off.stats.oe_offered 0 "conditions without guided synthesis";
        (* A spent guided budget: killers are refused and the source stops. *)
        let admit (source : Probe_lane.source) _ _ : Probe_lane.admission =
          match source with Observed | Prior -> Refused | Scanned | Injected -> Free
        in
        let t = create_lane ~admit { Probe_lane.default with scan = 0; fixed = false } theory in
        drive t ~turns:400;
        check (t.result = None) "a refused condition was probed";
        check (t.stats.refused >= 1) "no refusal recorded";
        equal t.stats.charged_guided 0 "a refused condition was charged";
        check (not (Probe_lane.oe_ready t)) "the source kept running after its budget" );
    ( "the observational source stays within its share of the instance sub-lane",
      fun () ->
        (* A consistent theory (correct separation): nothing is refuted, the
           source keeps enumerating, and its work stays within its share
           (up to one turn). *)
        let theory = Theory.create "separation" in
        let t = create_lane Probe_lane.default theory in
        drive t ~turns:600;
        let s = t.stats in
        check (t.result = None) "correct separation refuted";
        check (s.oe_work > 0.) "the source never ran";
        check
          (s.oe_work <= (Probe_lane.default.oe_share *. s.instance_work) +. 3_000.)
          (Printf.sprintf "source work %.0f over its share of %.0f" s.oe_work s.instance_work) );
    ( "the look-ahead promotes an injected pool killer that still waits",
      fun () ->
        (* The main engine injects the needle (p(s^3(z)), a pool killer)
           before the look-ahead reads it: the look-ahead then moves the
           waiting arrival to the killers instead of skipping it. *)
        let theory = two_schemas () in
        let t = create_lane { Probe_lane.with_breadth with fixed = false } theory in
        let rec build n =
          if n > 0 && t.pool = None then (
            Probe_lane.turn t;
            build (n - 1))
        in
        build 1_000;
        check (t.pool <> None) "the pool was not built";
        let needle_schema = schema_named theory "needle" in
        let p3 = List.nth (first_parameters theory needle_schema 4) 3 in
        Probe_lane.offer t needle_schema p3;
        drive t ~turns:200;
        check (t.stats.promoted >= 1) "the waiting killer was not promoted";
        check (found_in theory t "needle") ("the needle was not refuted" ^ Probe_lane.summary t);
        check (contains (Probe_lane.summary t) " promoted=") "summary lacks promoted" );
    ( "evaluation overrides parse, validate and leave the default alone",
      fun () ->
        let c = Probe_lane.parse_overrides Probe_lane.default "clock=events,ev_main=3,luby=0.25" in
        check (c.clock = Probe_lane.Events) "clock=events not applied";
        check (c.ev_main = 3. && c.luby_share = 0.25) "numeric overrides not applied";
        let c =
          Probe_lane.parse_overrides Probe_lane.default "main_weight=2.8,pad=0.25:0.5,mace=on"
        in
        check (c.main_weight = 2.8 && c.main_pad = (0.25, 0.5) && c.mace) "overrides not applied";
        check (Probe_lane.parse_overrides Probe_lane.default "" = Probe_lane.default) "empty text";
        check
          (rejects (fun () -> ignore (Probe_lane.parse_overrides Probe_lane.default "clock=wall")))
          "an unknown clock was accepted";
        check
          (rejects (fun () -> ignore (Probe_lane.parse_overrides Probe_lane.default "luby=2")))
          "a re-probe share above one was accepted";
        check
          (rejects (fun () -> ignore (Probe_lane.parse_overrides Probe_lane.default "speed=fast")))
          "an unknown key was accepted";
        let d = Probe_lane.default in
        check
          (d.clock = Probe_lane.Allocation
          && d.main_weight = Probe_lane.calibrated_main_weight
          && d.main_pad = (0., 0.))
          "the default lane clock changed";
        check (d.luby_share = 0. && not d.mace) "the default lane changed";
        let c = Probe_lane.candidate in
        check
          (c.luby_share > 0. && c.mace && c.observational && c.clock = Probe_lane.Allocation)
          "the candidate lane lacks re-probes or SAT models" );
    ( "the default allocation clock counts the main engine at the calibrated rate",
      fun () ->
        (* Lane-clock option (b): the calibrated exchange rate is a constant of the default (and
           of the candidate), not of the environment; the arrival-order ladder, which reproduces
           earlier defaults, keeps rate 1. AXIOM_LANE=main_weight=1 restores rate 1.
           Pinned value: recalibrate with bench/schema/scripts/lane_calibrate.py and update it
           here. *)
        check (Probe_lane.calibrated_main_weight = 1.5) "the calibrated rate changed";
        check
          (Probe_lane.candidate.main_weight = Probe_lane.calibrated_main_weight)
          "the candidate does not share the default clock";
        List.iter
          (fun (l : Probe_lane.config) ->
            check (l.main_weight = 1.) "a ladder preset changed its rate")
          [
            Probe_lane.disabled;
            Probe_lane.fifo;
            Probe_lane.fixed_escalate;
            Probe_lane.with_pool;
            Probe_lane.with_breadth;
          ];
        check (Scheduler.default_config.lane = Probe_lane.default) "the CLI lane is not the default";
        let env value k = if k = "AXIOM_LANE" then value else None in
        check
          (((Eval.of_env (env None)).config Scheduler.default_config).lane = Probe_lane.default)
          "an unset environment changed the lane";
        let a = (Eval.of_env (env (Some "main_weight=1"))).config Scheduler.default_config in
        check
          (a.lane = { Probe_lane.default with main_weight = 1. })
          "AXIOM_LANE=main_weight=1 does not give rate 1";
        (* The share test: after a lane turn of work L, the lane is due again once the main
           engine has allocated L / rate (share 1/2), not L. Allocation in one-unit steps
           (1,024 words) between the checks. *)
        let theory = Theory.create "separation" in
        let t = create_lane Probe_lane.default theory in
        Probe_lane.turn t;
        let lane = Probe_lane.work t in
        let rate = Probe_lane.calibrated_main_weight in
        check (lane > 50.) (Printf.sprintf "the first turn did only %.1f units" lane);
        check (rate *. Probe_lane.main_work t < lane) "due before the main engine allocated";
        let rec spin n =
          if n > 0 && not (Probe_lane.due t) then (
            ignore (Sys.opaque_identity (Array.make 1023 0));
            spin (n - 1))
        in
        spin 10_000_000;
        check (Probe_lane.due t) "never due";
        let main = Probe_lane.main_work t in
        check
          (rate *. main >= lane && rate *. (main -. 4.) < lane)
          (Printf.sprintf "due at main work %.1f, not at %.1f / %.2f" main lane rate);
        (* The events clock ignores the allocation rate: ev_main is its exchange rate. Main
           events just short of the rate-1 threshold do not make it due. *)
        let main_events = ref 0 in
        let e =
          Probe_lane.create ~started:(Telemetry.now ())
            ~main_events:(fun () -> (!main_events, 0))
            ~inject:(fun _ _ _ -> ())
            { Probe_lane.default with clock = Probe_lane.Events }
            config.engine theory
        in
        let rec turns n =
          if n > 0 && Probe_lane.work e < 100. && Probe_lane.has_work e then (
            Probe_lane.turn e;
            turns (n - 1))
        in
        turns 200;
        let per_event = e.config.ev_main *. e.config.ev_engine in
        main_events := int_of_float (Probe_lane.work e /. per_event);
        while per_event *. Float.of_int !main_events >= Probe_lane.work e do
          decr main_events
        done;
        check
          (rate *. per_event *. Float.of_int !main_events >= Probe_lane.work e)
          (Printf.sprintf "the check below would not tell the rates apart (lane work %.2f)"
             (Probe_lane.work e));
        check (not (Probe_lane.due e)) "the events clock used the allocation rate";
        incr main_events;
        while per_event *. Float.of_int !main_events < Probe_lane.work e do
          incr main_events
        done;
        check (Probe_lane.due e) "main-engine events did not make the events-clock lane due" );
    ( "the events clock splits by search events, not by allocation",
      fun () ->
        (* The main engine's events come from the scheduler's hook. With the
           events clock, allocation between lane turns (the main engine's
           work under the allocation clock) does not make the lane due; main
           events do. With the allocation clock it is the other way round. *)
        let theory = Theory.create "separation" in
        let main = ref 0 in
        let lane clock =
          Probe_lane.create ~started:(Telemetry.now ())
            ~main_events:(fun () -> (!main, 0))
            ~inject:(fun _ _ _ -> ())
            { Probe_lane.default with clock } config.engine theory
        in
        let garbage () =
          for _ = 1 to 200_000 do
            ignore (Sys.opaque_identity (Array.make 7 0))
          done
        in
        let t = lane Probe_lane.Events in
        Probe_lane.turn t;
        check (Probe_lane.work t > 0.) "an events-clock turn was free";
        check (not (Probe_lane.due t)) "due without any main-engine event";
        garbage ();
        check (not (Probe_lane.due t)) "allocation made the events-clock lane due";
        main := 1 + int_of_float (Probe_lane.work t /. (t.config.ev_main *. t.config.ev_engine));
        check (Probe_lane.due t) "main-engine events did not make the lane due";
        let a = lane Probe_lane.Allocation in
        Probe_lane.turn a;
        garbage ();
        check (Probe_lane.due a) "allocation did not make the allocation-clock lane due" );
    ( "non-killers that stop with engine work left are re-probed inside their share",
      fun () ->
        (* Correct separation: nothing is refuted, every probe runs out of its
           budget, so with re-probes on the exhausted non-killers come back at
           doubling budgets, inside [luby_share] of the instance sub-lane (up
           to one probe); off by default. No pool: the look-ahead queues every
           candidate as a non-killer. *)
        let theory = Theory.create "separation" in
        let run lane =
          let t = create_lane lane theory in
          drive t ~turns:400;
          t
        in
        let off = run Probe_lane.fifo in
        check (off.stats.probes > 0) "no probe";
        equal off.stats.luby_probes 0 "re-probes without the option";
        let share = 0.25 in
        let t = run { Probe_lane.fifo with luby_share = share; luby_levels = 3 } in
        let s = t.stats in
        check (t.result = None) "correct separation refuted";
        check (s.luby_probes > 0) ("no re-probe" ^ Probe_lane.summary t);
        check (s.reprobes >= s.luby_probes) "re-probes not counted as re-probes";
        check
          (s.luby_work <= (share *. s.instance_work) +. 8_000.)
          (Printf.sprintf "re-probe work %.0f over its share of %.0f" s.luby_work s.instance_work);
        check (contains (Probe_lane.summary t) " luby=") "summary lacks the re-probe fields" );
    ( "Mace pools hold verified, pairwise non-isomorphic models, deterministically",
      fun () ->
        let sg = Signature.make ~functions:[ ("a", 0); ("g", 1) ] ~predicates:[ ("member", 2) ] in
        (* g is injective and maps into a's members, plus an axiom with no
           finite model of at most 4 elements (5 distinct elements). *)
        let mem x y = Wire.Pred ("member", [ x; y ]) and a = Wire.App ("a", []) in
        let g x = Wire.App ("g", [ x ]) in
        let into = Wire.All (mem (g (Wire.B 0)) a) in
        let injective =
          Wire.All
            (Wire.All
               (Wire.Disj
                  [ Wire.Neg (Wire.Eq (g (Wire.B 1), g (Wire.B 0))); Wire.Eq (Wire.B 1, Wire.B 0) ]))
        in
        let five =
          let rec nest k vars =
            if k = 0 then
              Wire.Conj
                (List.concat_map
                   (fun i ->
                     List.filter_map
                       (fun j ->
                         if i < j then Some (Wire.Neg (Wire.Eq (Wire.B i, Wire.B j))) else None)
                       vars)
                   vars)
            else Wire.Ex (nest (k - 1) vars)
          in
          nest 5 [ 0; 1; 2; 3; 4 ]
        in
        let axioms = [ into; injective; five ] in
        let p = Mace.pool ~budget:5_000_000 sg axioms in
        check (List.length p.models >= 4) "too few models";
        equal p.axioms_used 2 "the maximal satisfiable subset at sizes 1-4";
        check (List.length p.active = 2) "active axioms";
        List.iter
          (fun (m : Semantic.model) ->
            List.iter
              (fun f ->
                check (Semantic.eval m f = Some true) "a pool model falsifies an active axiom")
              p.active)
          p.models;
        let meter = Semantic.meter () in
        let forms = List.map (fun m -> Mace.canonical m ~meter) p.models in
        equal
          (List.length (List.sort_uniq compare forms))
          (List.length forms) "two pool models are isomorphic";
        let again = Mace.pool ~budget:5_000_000 sg axioms in
        check (List.map (fun m -> Mace.canonical m ~meter) again.models = forms) "not deterministic"
    );
    ( "Mace finds small counter-models and none for contradictions",
      fun () ->
        (* A false killer of the observational source: separation of the
           empty elements over a functional relation r onto the subsets of a.
           It has a 3-element model (e empty, b = {e}, a = {e, a, b}, r the
           identity). *)
        let sg = Signature.make ~functions:[ ("a", 0) ] ~predicates:[ ("member", 2); ("r", 2) ] in
        let mem x y = Wire.Pred ("member", [ x; y ]) and r x y = Wire.Pred ("r", [ x; y ]) in
        let a = Wire.App ("a", []) in
        let b i = Wire.B i in
        let functional =
          Wire.All
            (Wire.All
               (Wire.All
                  (Wire.Disj
                     [ Wire.Neg (r (b 2) (b 1)); Wire.Neg (r (b 2) (b 0)); Wire.Eq (b 1, b 0) ])))
        in
        let surjection =
          Wire.All
            (Wire.Disj
               [
                 Wire.Neg (Wire.All (Wire.Disj [ Wire.Neg (mem (b 0) (b 1)); mem (b 0) a ]));
                 Wire.Ex (Wire.Conj [ mem (b 0) a; r (b 0) (b 1) ]);
               ])
        in
        let iff x y = Wire.Conj [ Wire.Disj [ Wire.Neg x; y ]; Wire.Disj [ x; Wire.Neg y ] ] in
        let instance =
          Wire.All
            (Wire.Ex
               (Wire.All
                  (iff
                     (mem (b 0) (b 1))
                     (Wire.Conj [ mem (b 0) (b 2); Wire.Neg (Wire.Ex (mem (b 0) (b 1))) ]))))
        in
        let meter = Semantic.meter () in
        (match Mace.find_model ~budget:2_000_000 ~meter sg [ functional; surjection ] instance with
        | Some m ->
            List.iter
              (fun f -> check (Semantic.eval m f = Some true) "the counter-model is not one")
              [ functional; surjection; instance ]
        | None -> failwith "no counter-model");
        check (meter.steps > 0 && meter.steps <= 2_000_000 + 10_000) "steps not charged";
        (* Naive comprehension of ~(x in x) has no model of any size. *)
        let russell = Wire.Ex (Wire.All (iff (mem (b 0) (b 1)) (Wire.Neg (mem (b 0) (b 0))))) in
        let meter = Semantic.meter () in
        check
          (Mace.find_model ~budget:2_000_000 ~meter Signature.sets [] russell = None)
          "a model of Russell's comprehension";
        (* Least-number symmetry breaking keeps models of distinct constants. *)
        let sg3 = Signature.make ~functions:[ ("c1", 0); ("c2", 0); ("c3", 0) ] ~predicates:[] in
        let c i = Wire.App ("c" ^ string_of_int i, []) in
        let distinct =
          Wire.Conj
            [
              Wire.Neg (Wire.Eq (c 1, c 2));
              Wire.Neg (Wire.Eq (c 2, c 3));
              Wire.Neg (Wire.Eq (c 1, c 3));
            ]
        in
        match Mace.find_model ~budget:1_000_000 sg3 [] distinct with
        | Some m -> equal m.size 3 "three distinct constants need three elements"
        | None -> failwith "symmetry breaking lost the model of three distinct constants" );
    ( "the observational source with Mace refutes naive comprehension",
      fun () ->
        let theory = Theory.create "naive" in
        let admit (source : Probe_lane.source) _ _ : Probe_lane.admission =
          match source with Observed -> Charged | Prior | Scanned | Injected -> Free
        in
        let t =
          create_lane ~admit { Probe_lane.default with scan = 0; fixed = false; mace = true } theory
        in
        drive t ~turns:2_000;
        (match t.result with
        | Some cert -> roundtrip theory cert
        | None -> failwith ("the source with Mace found nothing" ^ Probe_lane.summary t));
        equal t.stats.winner "observed" "the refutation did not come from the source";
        check (t.stats.pool_models > 0) "no SAT pool";
        check (contains (Probe_lane.summary t) " mace=") "summary lacks the Mace field" );
    ( "lane configurations are validated",
      fun () ->
        check
          (rejects (fun () -> Probe_lane.validate { Probe_lane.fifo with share = 0.75 }))
          "a share above one half was accepted";
        check
          (rejects (fun () -> Probe_lane.validate { Probe_lane.fifo with instance_budget = 0 }))
          "an empty probe budget was accepted";
        check
          (rejects (fun () -> Probe_lane.validate { Probe_lane.default with shape_cap = 0. }))
          "a zero shape cap was accepted";
        check
          (rejects (fun () -> Probe_lane.validate { Probe_lane.default with oe_share = 0. }))
          "a zero observational share was accepted";
        Probe_lane.validate { Probe_lane.disabled with share = 0.9 } );
  ]

let () = run tests
