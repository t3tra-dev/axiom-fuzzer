(* The certified reference in a forked OS process. OCaml 5 refuses [Unix.fork] once this
   process has spawned any Domain, so these tests live in their own executable and never
   spawn one. *)
open Axiom_fuzzer
open Test_support

let source = "fof(f,axiom,$false)."

let with_path f =
  let path = Filename.temp_file "axiom-reference-process-" ".checkpoint" in
  Sys.remove path;
  Fun.protect
    ~finally:(fun () ->
      List.iter (fun p -> if Sys.file_exists p then Sys.remove p) [ path; path ^ ".lock" ])
    (fun () -> f path)

let no_children () =
  match Unix.waitpid [ Unix.WNOHANG ] (-1) with
  | exception Unix.Unix_error (Unix.ECHILD, _, _) -> ()
  | _ -> failwith "a process outlived the portfolio"

(* A frontier whose first task is the code of a valid one-step natural deduction. *)
let witness_checkpoint path theory =
  let module N = Natural_checker in
  let code =
    N.certificate_code
      {
        N.assumptions = [ Wire_types.Pair (Number 0, N.permission_code (N.FixedPermission 0)) ];
        deduction = N.Assume 0;
      }
  in
  let rec encode = function
    | Wire_types.Number n -> [ 0; n ]
    | Pair (x, y) -> (1 :: encode x) @ encode y
  in
  let word = encode code in
  let level = List.fold_left max (List.length word) word in
  let n = Certificate_io.number in
  Sexp.write_file path
    (Sexp.to_string
       (Sexp.List
          [
            Atom "certified-frontier";
            Reference.manifest theory;
            n level;
            List [ List [ List (List.map n word); n 0 ] ];
            n 0;
            List [];
          ]))

let reference_only seconds checkpoint =
  {
    Scheduler.default_config with
    reference_only = true;
    reference_config = { seconds; max_trials = max_int; checkpoint };
  }

let tests =
  [
    ( "process reference returns a parent-checked certificate",
      fun () ->
        with_path (fun path ->
            let theory = Tptp.parse source in
            witness_checkpoint path theory;
            let r =
              Portfolio.processes (reference_only 5. (Some path)) (fun () -> Tptp.parse source)
            in
            no_children ();
            equal r.proof_source "reference" "process reference proof was not selected";
            let cert = Option.get r.certificate in
            check (cert.natural <> None) "process reference lost the natural deduction";
            check (Result.is_ok (Kernel.check theory cert)) "process certificate failed replay";
            let rr = Option.get r.reference_report in
            check
              (rr.trials >= 1 && rr.trials <= Portfolio.reference_batch)
              "process reference report lost its ticks") );
    ( "process reference keeps its budget after heuristic exhaustion",
      fun () ->
        let r =
          Portfolio.processes ~workers:2
            {
              Scheduler.default_config with
              reference = true;
              reference_config = { seconds = 3.; max_trials = 96; checkpoint = None };
            }
            (fun () -> Tptp.parse "fof(p,axiom,p(a)).")
        in
        no_children ();
        let rr = Option.get r.reference_report in
        equal rr.trials 96 "process reference stopped with heuristic exhaustion";
        equal
          (List.length (Option.get r.processes).remote_workers)
          2 "heuristic worker metrics missing";
        check (r.certificate = None) "consistent input was refuted" );
    ( "a stopped process reference saves its checkpoint before it exits",
      fun () ->
        with_path (fun path ->
            let problem () = Tptp.parse "fof(p,axiom,p(a))." in
            let started = Unix.gettimeofday () in
            let r =
              Portfolio.processes
                ~cancelled:(fun () -> Unix.gettimeofday () -. started > 0.3)
                (reference_only 30. (Some path)) problem
            in
            no_children ();
            check (Unix.gettimeofday () -. started < 5.) "reference did not stop when cancelled";
            let rr = Option.get r.reference_report in
            check (rr.trials > 0) "reference made no progress";
            check (Sys.file_exists path) "checkpoint was not saved";
            let again = Portfolio.processes (reference_only 0.05 (Some path)) problem in
            no_children ();
            let resumed = Option.get again.reference_report in
            check resumed.resumed "checkpoint did not resume";
            check (resumed.tested >= rr.tested) "resumed reference lost saved ticks") );
    ( "a reference certificate the supervisor rejects is an internal error",
      fun () ->
        let satisfiable () = Tptp.parse "fof(p,axiom,p(a))." in
        let forged =
          {
            Reference.certificate =
              Some
                {
                  Wire.natural = Some (Wire_types.Number 0);
                  avatar = None;
                  cnf_mode = Wire.Hybrid;
                  theory = "tptp";
                  axioms = [];
                  steps = [];
                  root = 0;
                };
            reason = "forged";
            tested = 1;
            trials = 1;
            script_tested = 0;
            byte_tested = 0;
            stage = 0;
            seconds = 0.;
            replay_seconds = 0.;
            axioms = [];
            resumed = false;
            peak_domain_words = -1;
          }
        in
        let hook role fd =
          match role with
          | Portfolio.Reference_role ->
              Process_frame.write fd (Portfolio.Reference_done (forged, 0., 0.));
              Unix._exit 0
          | Portfolio.Worker _ -> ()
        in
        (* The reference process returns only witnesses its kernel accepted, so a rejection by
           the supervisor is an internal error, raised as the Domain reference raises it. *)
        (match Portfolio.processes ~hook (reference_only 1. None) satisfiable with
        | _ -> failwith "forged reference certificate ended the run quietly"
        | exception Invalid_argument m ->
            check
              (String.starts_with ~prefix:(Reference.rejected_certified_replay "") m)
              ("error: " ^ m));
        no_children () );
  ]

let () = run tests
