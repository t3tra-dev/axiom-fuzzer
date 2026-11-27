open Axiom_fuzzer
open Axiom_cli

let main () =
  (* Before any worker exists: forked workers and spawned Domains inherit it. *)
  Minor_heap.apply ();
  let started = Pipeline_profile.sample () in
  let theory = ref "naive" and certificate = ref "" and quiet = ref false and workers = ref 1 in
  let stats = ref false in
  let explicit_theory = ref false in
  let problem = ref ""
  and fof = ref ""
  and cnf = ref ""
  and tstp = ref ""
  and rocq = ref ""
  and metrics = ref "" in
  let profile_path = ref "" in
  let worker_metrics = ref "" and schema_metrics = ref "" in
  let guided_proofs = ref [] and eval_strategies = ref None in
  let config = ref Scheduler.default_config and memory_budget = ref None in
  let engine f = config := { !config with engine = f !config.engine } in
  let limits f = engine (fun e -> { e with limits = f e.limits }) in
  let options =
    [
      ( "--theory",
        Arg.String
          (fun name ->
            theory := name;
            explicit_theory := true),
        Printf.sprintf "NAME Built-in theory: %s (default naive)" (String.concat ", " Theory.names)
      );
      ("--problem", Arg.Set_string problem, "FILE TPTP FOF/CNF input");
      ( "--seconds",
        Arg.Float (fun n -> limits (fun l -> { l with seconds = n })),
        "N Shared wall budget (default 10)" );
      ( "--max-given",
        Arg.Int (fun n -> limits (fun l -> { l with max_given = n })),
        "N Hard cap on selected clauses per worker; stops it (default unlimited)" );
      ( "--max-generated",
        Arg.Int (fun n -> limits (fun l -> { l with max_generated = n })),
        "N Hard cap on generated clauses per worker; stops it (default unlimited)" );
      ( "--max-retained",
        Arg.Int (fun n -> limits (fun l -> { l with max_retained = n })),
        "N Hard cap on stored proof nodes per worker; stops it (default unlimited)" );
      ( "--memory-budget",
        Arg.Int
          (fun mib ->
            if mib < 0 || mib > max_int / (1024 * 1024 * 16) then
              raise (Arg.Bad "--memory-budget must be between 0 and the platform limit");
            memory_budget := Some mib),
        Printf.sprintf
          "MIB Search-state budget of each worker, in deterministic units; over it a worker trims \
           its state instead of stopping (default %d; 0 disables it; docs/cli.md)"
          (Footprint.to_mib Engine.default_budget.heap_words) );
      ( "--max-instances",
        Arg.Int (fun n -> config := { !config with max_instances = n; max_guided_instances = n }),
        "N Per-generator schema-instance budget (default unlimited)" );
      ( "--workers",
        Arg.Set_int workers,
        "N Search workers, 1 to 64, each with its own search and strategy (default 1; docs/cli.md)"
      );
      (* Evaluation only, hidden from --help: per-worker strategies for A/A and
         measurement runs (balanced | standard | NAME for every worker | NAME,...
         per worker; the default is balanced, production is the all-production
         A/A baseline, which also runs one worker as production alone, without
         the balanced single-worker share). The last occurrence
         wins whole: [balanced], [standard] and lists reset the base strategy
         that an earlier single name set to production. *)
      ( "--eval-strategies",
        Arg.String
          (fun spec ->
            let portfolio, base = Strategy.portfolio_of_string spec in
            let strategy = Option.value base ~default:Scheduler.default_config.engine.strategy in
            eval_strategies := Some spec;
            config := { !config with portfolio };
            engine (fun e -> { e with strategy })),
        "" );
      (* Evaluation only, hidden from --help: the AXIOM_* evaluation switches (Eval). *)
      ( "--eval-help",
        Arg.Unit
          (fun () ->
            print_string (Eval.help ());
            exit 0),
        "" );
      ( "--history",
        Arg.String (fun path -> guided_proofs := path :: !guided_proofs),
        "FILE Checked proof supplying synthesis hints (repeatable; default none)" );
      ( "--checkpoint",
        Arg.String
          (fun path ->
            config :=
              {
                !config with
                reference_config = { !config.reference_config with checkpoint = Some path };
              }),
        "FILE Save/resume the certified enumeration cursor" );
      ("--certificate", Arg.Set_string certificate, "FILE Replayable refutation");
      ("--output", Arg.Set_string certificate, "FILE Same as --certificate");
      ("--export-fof", Arg.Set_string fof, "FILE Source axioms used by the selected search");
      ("--export-cnf", Arg.Set_string cnf, "FILE Hybrid CNF of the selected axioms");
      ("--tstp", Arg.Set_string tstp, "FILE TSTP refutation");
      ("--rocq", Arg.Set_string rocq, "FILE Checkable Rocq Source refutation");
      ("--metrics", Arg.Set_string metrics, "FILE Search metrics CSV");
      ("--profile", Arg.Set_string profile_path, "FILE Pipeline wall/CPU/allocation measurements");
      ("--worker-metrics", Arg.Set_string worker_metrics, "FILE Per-worker metrics CSV");
      ("--schema-metrics", Arg.Set_string schema_metrics, "FILE Schema coverage CSV");
      ("--quiet", Arg.Set quiet, " Suppress candidate and proof listings");
      ( "--stats",
        Arg.Set stats,
        " Also print the search statistics: the lane counters, the reference worker, every \
         heuristic worker's stop and the selected search's counters" );
      Cli.version_option "axiom-fuzz";
    ]
  in
  Arg.parse options (fun x -> raise (Arg.Bad ("unexpected argument: " ^ x))) "axiom-fuzz [options]";
  (* The evaluation switches (Eval): none is set in a normal run, and a run with any of them set
     says so. *)
  let eval = Eval.of_env Sys.getenv_opt in
  Option.iter prerr_endline
    (Eval.note ?extra:(Option.map (fun s -> [ ("--eval-strategies", s) ]) !eval_strategies) eval);
  config := eval.config !config;
  engine (fun e -> { e with budget = Engine.worker_budget ?mib:!memory_budget () });
  (* Workers that would repeat another worker's search (the same strategy at a queue phase
     congruent modulo its period) run, but add nothing new: say so instead of hiding it. A
     deterministic E strategy repeat is refused here already. *)
  if !workers >= 1 && !workers <= 64 then
    Option.iter prerr_endline (Scheduler.repeat_warning ~workers:!workers !config);
  (* The clock, trace and report hooks of the evaluation switches; forked workers inherit them. *)
  eval.install ();
  config :=
    {
      !config with
      reference_config =
        {
          !config.reference_config with
          seconds = !config.engine.limits.seconds;
          max_trials = max_int;
        };
    };
  let isolation = eval.isolation in
  Pipeline_profile.with_file !profile_path ~started (fun profile ->
      let on_instance (trace : Scheduler.trace) =
        if not !quiet then
          Printf.printf "[%d] %s%s: %s\n%!" trace.axiom.axiom_id
            (match trace.generator with Exhaustive -> "" | Guided -> "guided ")
            trace.axiom.name trace.predicate
      in
      if !problem <> "" && !explicit_theory then
        invalid_arg "--problem and --theory cannot be combined";
      let manifest =
        if !problem = "" then
          Pipeline_profile.stage profile "theory_setup" (fun () -> Theory.create !theory)
        else
          let text =
            Pipeline_profile.stage profile "input_read" (fun () -> Sexp.read_file !problem)
          in
          Pipeline_profile.stage profile "input_parse" (fun () ->
              (* Roles are search hints only (conjecture-relative clause evaluation);
                 they never reach the manifest or a certificate. *)
              let manifest, roles = Tptp.parse_annotated text in
              let goal_names =
                List.filter_map
                  (fun (name, role) -> if role = "negated_conjecture" then Some name else None)
                  roles
              in
              engine (fun e ->
                  {
                    e with
                    goal_names;
                    vampire_symbols = Vampire.parse_order_of_text text;
                    e_text = E_initial.of_text text;
                  });
              manifest)
      in
      (* The portfolio constructs every theory before starting any worker.
         Give the first worker the already prepared arena; copy only the rest.
         The CLI reads the manifest again only after all workers have joined. *)
      let available = ref true in
      let make_theory () =
        if !available then (
          available := false;
          manifest)
        else
          Pipeline_profile.stage profile "theory_copy" (fun () ->
              Theory.copy ~preserve_arena:true manifest)
      in
      let history =
        Pipeline_profile.stage profile "history" (fun () ->
            List.rev !guided_proofs
            |> List.concat_map (fun path -> Guided.learn manifest (Certificate_io.read path)))
      in
      let interrupted = Atomic.make false in
      (* Ctrl-C stops cooperatively. Worker processes run in their own sessions, so the terminal
         interrupts only this supervisor; SIGTERM and SIGHUP (a closed terminal) are handled the
         same way so that they, too, stop and reap the workers instead of leaving them to their
         lifeline (see Portfolio). *)
      let signals =
        match isolation with
        | Portfolio.Domains -> [ Sys.sigint ]
        | Portfolio.Processes -> [ Sys.sigint; Sys.sigterm; Sys.sighup ]
      in
      let previous =
        List.map
          (fun s -> (s, Sys.signal s (Sys.Signal_handle (fun _ -> Atomic.set interrupted true))))
          signals
      in
      (* The handlers stay until every output is written: a stop request that arrives after the
         portfolio returned changes nothing, and must not cut an output write short (that would
         leave its temporary file behind). *)
      Fun.protect ~finally:(fun () -> List.iter (fun (s, h) -> Sys.set_signal s h) previous)
      @@ fun () ->
      let result =
        Pipeline_profile.stage profile "portfolio" (fun () ->
            Portfolio.run ?profile ~history ~workers:!workers
              ~cancelled:(fun () -> Atomic.get interrupted)
              ~on_instance ~isolation !config make_theory)
      in
      let output_seconds =
        Pipeline_profile.stage profile "output" (fun () ->
            let output_started = Telemetry.now () in
            (* The summary; --stats adds the measurement lines, in the format of the search
               statistics that tools parse (docs/cli.md). *)
            Printf.printf "Theory: %s\nResult: %s\nReason: %s\n" (Theory.name manifest)
              (if result.certificate = None then "UNKNOWN" else "UNSAT")
              (if !stats then result.reason else Cli.without_lane_counters result.reason);
            if !fof <> "" then
              Pipeline_profile.stage profile "export_fof" (fun () ->
                  Cli.write_file !fof (Tptp.problem result.axioms));
            if !cnf <> "" then
              Pipeline_profile.stage profile "export_cnf" (fun () ->
                  Cli.write_file !cnf (Tptp.cnf_problem ~mode:result.cnf_mode result.axioms));
            (match result.certificate with
            | None -> ()
            | Some cert ->
                let premises, proof_steps, label =
                  match cert.natural with
                  | None ->
                      ( cert.axioms,
                        fst (Proof.statistics cert),
                        if cert.avatar = None then "Proof clauses" else "Proof steps (FO + Boolean)"
                      )
                  | Some code -> (result.axioms, fst (Natural.statistics code), "Deduction steps")
                in
                Printf.printf "Used axioms: %s\n%s: %d\n"
                  (String.concat ", " (List.map (fun (a : Wire.axiom) -> a.name) premises))
                  label proof_steps;
                if !stats then print_string "Replay verified: true\n";
                if not !quiet then
                  List.iter
                    (fun (s : Wire.step) ->
                      Printf.printf "#%d  %s\n" s.id (Wire.clause_string s.clause))
                    cert.steps;
                if !certificate <> "" then (
                  let text =
                    Pipeline_profile.stage profile "certificate_encode" (fun () ->
                        Certificate_io.encode cert)
                  in
                  Pipeline_profile.stage profile "certificate_write" (fun () ->
                      Cli.write_file !certificate text);
                  Printf.printf "Certificate: %s\n" !certificate;
                  (* The written file ends with a newline. Over [Sexp.max_file_bytes] the
                     independent replay (axiom-replay) and --history refuse to read it, although
                     the in-process kernel check above accepted the proof: say so. *)
                  let bytes = String.length text + 1 in
                  let readable = bytes <= Sexp.max_file_bytes in
                  if !stats then
                    Printf.printf "Certificate bytes: %d limit=%d readable=%b\n" bytes
                      Sexp.max_file_bytes readable;
                  if not readable then
                    Printf.eprintf
                      "Warning: the certificate %s has %d bytes, over the %d-byte reader limit \
                       (Sexp.max_file_bytes): axiom-replay and --history cannot read it, although \
                       the in-process kernel check accepted it\n\
                       %!"
                      !certificate bytes Sexp.max_file_bytes);
                if !tstp <> "" then
                  Pipeline_profile.stage profile "export_tstp" (fun () ->
                      Cli.write_file !tstp (Tptp.tstp cert));
                if !rocq <> "" then
                  Pipeline_profile.stage profile "export_rocq" (fun () ->
                      match Kernel.rocq_document manifest cert with
                      | Ok text -> Cli.write_file !rocq text
                      | Error e -> failwith e));
            if !stats then (
              Option.iter
                (fun (r : Reference.report) ->
                  Printf.printf
                    "Reference: ticks=%d cumulative=%d stage=%d seconds=%.6f resumed=%b reason=%s\n"
                    r.trials r.tested r.stage r.seconds r.resumed r.reason;
                  Printf.printf "Reference heap: peak_domain_words=%d\n" r.peak_domain_words)
                result.reference_report;
              Printf.printf "Proof source: %s\n" result.proof_source;
              (* Why and when every heuristic worker stopped, in worker order: from the engines in
               Domain mode and from each worker process's report under processes. *)
              let stops =
                match result.processes with
                | None ->
                    List.map
                      (fun (w : Scheduler.worker_metrics) ->
                        (w.worker_id, w.reason, Some (Scheduler.counters w.engine)))
                      result.workers
                | Some p ->
                    List.sort compare
                      (List.map
                         (fun (w : Scheduler.remote_worker) ->
                           (w.remote_id, w.remote_reason, w.remote_counters))
                         p.remote_workers)
              in
              List.iter
                (fun (id, reason, counters) ->
                  match counters with
                  | Some (c : Scheduler.counters) ->
                      Printf.printf
                        "Heuristic %d: stop=%S active_seconds=%.3f collection_seconds=%.3f \
                         given=%d budget_responses=%d cursor_drops=%d trimmed=%d \
                         peak_domain_words=%d peak_footprint_words=%d budget_checks=%d \
                         budget_digest=%016x\n"
                        id reason c.seconds c.collection_seconds c.given c.budget_responses
                        c.budget_cursor_drops c.budget_trimmed c.peak_domain_words
                        c.peak_footprint_words c.budget_checks c.budget_digest
                  | None -> Printf.printf "Heuristic %d: stop=%S\n" id reason)
                stops;
              (* The selected search; a reference proof reports worker 0's counters. *)
              let counters =
                match result.processes with
                | None ->
                    if result.workers <> [] then Some (Scheduler.counters result.engine) else None
                | Some p ->
                    let id = max 0 result.worker_id in
                    List.find_map
                      (fun (w : Scheduler.remote_worker) ->
                        if w.remote_id = id then w.remote_counters else None)
                      p.remote_workers
              in
              Option.iter
                (fun (c : Scheduler.counters) ->
                  Printf.printf
                    "Metrics: generated=%d retained=%d given=%d unifications=%d postings=%d \
                     heap_words=%d seconds=%.6f replay_seconds=%.6f reference_trials=%d\n\
                     %!"
                    c.generated c.retained c.given c.unifications c.postings c.heap_words c.seconds
                    result.replay_seconds
                    (match result.reference_report with Some r -> r.trials | None -> 0))
                counters);
            Telemetry.now () -. output_started)
      in
      Pipeline_profile.stage profile "metrics_write" (fun () ->
          if !metrics <> "" then
            Cli.write_file !metrics (Metrics_csv.summary ~output_seconds result);
          if !worker_metrics <> "" then Cli.write_file !worker_metrics (Metrics_csv.workers result);
          if !schema_metrics <> "" then Cli.write_file !schema_metrics (Metrics_csv.schemas result)))

let () = Cli.run main
