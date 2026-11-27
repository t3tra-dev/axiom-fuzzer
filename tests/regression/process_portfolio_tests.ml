(* The forked-process portfolio. OCaml 5 refuses [Unix.fork] once any Domain has been spawned,
   so this executable never spawns one except in its last test. After every portfolio this
   process must have no child left: none running, none unreaped. *)
open Axiom_fuzzer
open Test_support

let no_children () =
  match Unix.waitpid [ Unix.WNOHANG ] (-1) with
  | exception Unix.Unix_error (Unix.ECHILD, _, _) -> ()
  | 0, _ -> failwith "a worker process is still running"
  | pid, _ -> failwith (Printf.sprintf "an unreaped worker process %d was left" pid)

let dead pid =
  match Unix.kill pid 0 with
  | () -> false
  | exception Unix.Unix_error (Unix.ESRCH, _, _) -> true
  | exception Unix.Unix_error _ -> false

let processes_of (r : Scheduler.result) =
  match r.processes with Some p -> p | None -> failwith "missing process information"

let pids (r : Scheduler.result) =
  let p = processes_of r in
  List.map (fun (w : Scheduler.remote_worker) -> w.remote_process.pid) p.remote_workers
  @ Option.fold ~none:[] ~some:(fun (s : Scheduler.process_stats) -> [ s.pid ]) p.reference_process

let checked (r : Scheduler.result) =
  no_children ();
  List.iter (fun pid -> check (dead pid) "a worker process outlived the portfolio") (pids r);
  r

let contains text part =
  let n = String.length part in
  let rec at i = i + n <= String.length text && (String.sub text i n = part || at (i + 1)) in
  at 0

let fast_timing = { Portfolio.margin = 0.2; grace = 0.3; reference_grace = 0.3; proof_grace = 0.3 }

let quick_config ?(seconds = 3.) () =
  { config with engine = { config.engine with limits = { config.engine.limits with seconds } } }

let refutable = "fof(a,axiom,p(c)).\nfof(b,axiom,![X]: ~p(X))."

(* The schema probe lane alone refutes naive here: a test-local condition prior (the lane's
   experiment hook; no default sets one) offers ~(x in x) first, guidance is on (a prior is guided
   synthesis) with a small guided budget, and with no exhaustive budget the main engine has no
   clause to work on. *)
let russell_first : Probe_lane.prior =
 fun _ ->
  List.to_seq
    [
      Wire.Neg (Wire.Pred ("member", [ Wire.F 0; Wire.F 0 ]));
      Wire.Pred ("member", [ Wire.F 0; Wire.F 0 ]);
    ]

let lane_naive_config () =
  {
    (quick_config ()) with
    reference = false;
    guided = true;
    max_instances = 0;
    max_guided_instances = 4;
    lane = { Probe_lane.fixed_escalate with prior = Some russell_first };
  }

let parse text () = Tptp.parse text

(* TPTP input nests terms at most 256 deep, but unification composes them: the refutation of
   these clauses binds Y to a term nested [2 * depth] deep. Above about 250 levels the
   S-expression certificate exceeds its 512-level parser limit, so an S-expression IPC would
   lose the proof. *)
let deep depth =
  let rec wrap n x = if n = 0 then x else "f(" ^ wrap (n - 1) x ^ ")" in
  Printf.sprintf "fof(a,axiom,![X]: p(X,%s)).\nfof(b,axiom,![Y]: ~p(%s,Y))." (wrap depth "X")
    (wrap depth "c")

let rows csv = List.filter (fun l -> l <> "") (String.split_on_char '\n' csv)

let fields line =
  (* Enough of RFC 4180 for these rows: quoted fields may contain commas and doubled quotes. *)
  let out = ref [] and b = Buffer.create 16 and quoted = ref false in
  let n = String.length line in
  let i = ref 0 in
  while !i < n do
    let c = line.[!i] in
    if !quoted then
      if c = '"' && !i + 1 < n && line.[!i + 1] = '"' then (
        Buffer.add_char b '"';
        incr i)
      else if c = '"' then quoted := false
      else Buffer.add_char b c
    else if c = '"' then quoted := true
    else if c = ',' then (
      out := Buffer.contents b :: !out;
      Buffer.clear b)
    else Buffer.add_char b c;
    incr i
  done;
  List.rev (Buffer.contents b :: !out)

let column csv name =
  match rows csv with
  | header :: data ->
      let h = fields header in
      let index =
        let rec find i = function
          | [] -> failwith ("missing column " ^ name)
          | x :: _ when x = name -> i
          | _ :: rest -> find (i + 1) rest
        in
        find 0 h
      in
      List.map (fun line -> List.nth (fields line) index) data
  | [] -> failwith "empty CSV"

let forged : Wire.certificate =
  {
    natural = None;
    avatar = None;
    cnf_mode = Wire.Hybrid;
    theory = "tptp";
    axioms = [];
    steps = [ { id = 0; clause = []; rule = Wire.Input (0, 0) } ];
    root = 0;
  }

(* A worker's report as a hook writes it in place of the real search. *)
let report ?certificate ?(row = []) id =
  Portfolio.Worker_done
    {
      id;
      certificate;
      proof_source = "heuristic:" ^ string_of_int id;
      reason = "hook report";
      axioms = [];
      traces = [];
      cnf_mode = Wire.Hybrid;
      row;
      schema_rows = [];
      counters = Scheduler.counters (Engine.create Engine.default_config);
      profile = [];
      cpu_seconds = 0.;
      peak_rss_bytes = 0.;
    }

let proof text = Option.get (Scheduler.run_search (quick_config ()) (Tptp.parse text)).certificate

(* Waits [seconds] whatever signals arrive (a worker that is checking or encoding a proof does
   not look at stop requests). *)
let busy seconds =
  let until = Unix.gettimeofday () +. seconds in
  while Unix.gettimeofday () < until do
    try Unix.sleepf 0.01 with Unix.Unix_error (Unix.EINTR, _, _) -> ()
  done

let remote (r : Scheduler.result) i =
  List.find (fun (w : Scheduler.remote_worker) -> w.remote_id = i) (processes_of r).remote_workers

(* Descriptors open in this process (macOS and Linux both list them in /dev/fd). *)
let open_fds () = Array.length (Sys.readdir "/dev/fd")

let with_dir f =
  let dir =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "axiom-fuzzer-portfolio-%d-%d" (Unix.getpid ()) (Random.bits ()))
  in
  Unix.mkdir dir 0o700;
  let clean () =
    Array.iter (fun n -> Sys.remove (Filename.concat dir n)) (Sys.readdir dir);
    Unix.rmdir dir
  in
  Fun.protect ~finally:clean (fun () -> f dir)

(* Runs [supervise] in a forked process (the supervisor of a portfolio) and returns its PID and
   the process ID that the portfolio's child [role] sends through [announce] (from its hook). *)
let forked_supervisor supervise =
  let rd, wr = Unix.pipe () in
  match Unix.fork () with
  | 0 ->
      Unix.close rd;
      let announce () =
        let line = Printf.sprintf "%d\n" (Unix.getpid ()) in
        ignore (Unix.write_substring wr line 0 (String.length line));
        Unix.close wr
      in
      (try supervise announce with _ -> ());
      Unix._exit 0
  | supervisor ->
      Unix.close wr;
      let ic = Unix.in_channel_of_descr rd in
      let child = int_of_string (input_line ic) in
      close_in ic;
      (supervisor, child)

(* Waits until [pid] (not our child) is gone; SIGKILLs it after [within] seconds so that a
   failing test leaves nothing behind. Returns how long it lived. *)
let await_death pid within =
  let started = Unix.gettimeofday () in
  while (not (dead pid)) && Unix.gettimeofday () -. started < within do
    Unix.sleepf 0.002
  done;
  let lived = Unix.gettimeofday () -. started in
  (if not (dead pid) then try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
  lived

let tests =
  [
    ( "a process worker proof is re-checked and selected",
      fun () ->
        let r =
          checked
            (Portfolio.processes ~workers:2
               { (quick_config ()) with reference = true }
               (parse refutable))
        in
        check (r.certificate <> None) "process portfolio lost the proof";
        check (String.starts_with ~prefix:"heuristic:" r.proof_source) "proof source";
        check
          (Result.is_ok (Kernel.check (Tptp.parse refutable) (Option.get r.certificate)))
          "selected certificate fails replay";
        let p = processes_of r in
        equal (List.length p.remote_workers) 2 "remote worker rows";
        equal p.lost [] "a worker was reported lost";
        check (p.reference_process <> None) "reference process missing";
        let rr = Option.get r.reference_report in
        check (rr.certificate = None) "reference claimed the heuristic proof" );
    ( "worker metrics are serialized into the CSV outputs",
      fun () ->
        let r =
          checked
            (Portfolio.processes ~workers:3 { config with max_size = 3; reference = false }
               (fun () -> Theory.create "naive"))
        in
        check (r.certificate <> None) "naive comprehension was not refuted";
        let workers = Metrics_csv.workers r in
        equal (List.length (rows workers)) 4 "worker CSV rows";
        equal (column workers "worker") [ "0"; "1"; "2" ] "worker ids";
        check
          (List.for_all
             (fun e -> String.starts_with ~prefix:"exit" e)
             (column workers "worker_exit"))
          "worker exit status";
        let summary = Metrics_csv.summary ~output_seconds:0. r in
        let total = int_of_string (List.hd (column summary "total_generated")) in
        equal total
          (List.fold_left ( + ) 0 (List.map int_of_string (column workers "generated")))
          "summary total does not match worker rows";
        equal (column summary "isolation") [ "processes" ] "isolation column";
        equal (column summary "workers") [ "3" ] "worker count";
        let schemas = Metrics_csv.schemas r in
        equal
          (List.fold_left ( + ) 0 (List.map int_of_string (column schemas "injected")))
          (List.fold_left ( + ) 0 (List.map int_of_string (column workers "injected_instances")))
          "schema rows do not match worker rows";
        check (List.length (rows schemas) > 1) "schema rows missing" );
    ( "the time budget ends every process and keeps the reason",
      fun () ->
        let started = Unix.gettimeofday () in
        let r =
          checked
            (Portfolio.processes ~workers:2 ~timing:fast_timing
               {
                 (quick_config ~seconds:0.5 ()) with
                 max_size = 0;
                 max_instances = max_int;
                 reference = true;
                 reference_config = { seconds = 0.5; max_trials = max_int; checkpoint = None };
               }
               (fun () -> Theory.create "zf"))
        in
        let wall = Unix.gettimeofday () -. started in
        check (r.certificate = None) "zf was refuted";
        check (contains r.reason "time limit") ("reason: " ^ r.reason);
        check (wall < 0.5 +. fast_timing.margin +. 0.5) (Printf.sprintf "wall %.3f" wall);
        equal (processes_of r).lost [] "a worker was lost at its own deadline" );
    ( "the supervisor's deadline counts from the first fork, after the theory copies",
      fun () ->
        (* Three copies (two workers and the reference) of 0.3 s each take longer than the
           margin: a deadline counted from before the copies stopped the workers right after
           they started, before their own 0.5 s budgets ended. The count caps of the test
           configuration are lifted: a worker fast enough to reach one (3,000 retained proof
           nodes) within 0.5 s would stop before its deadline, which this test does not
           measure. *)
        let make () =
          Unix.sleepf 0.3;
          Theory.create "zf"
        in
        let base = quick_config ~seconds:0.5 () in
        let started = Unix.gettimeofday () in
        let r =
          checked
            (Portfolio.processes ~workers:2 ~timing:fast_timing
               {
                 base with
                 engine = { base.engine with limits = { Engine.default_limits with seconds = 0.5 } };
                 max_size = 0;
                 max_instances = max_int;
                 reference = true;
                 reference_config = { seconds = 0.5; max_trials = max_int; checkpoint = None };
               }
               make)
        in
        let wall = Unix.gettimeofday () -. started in
        check (r.certificate = None) "zf was refuted";
        List.iter
          (fun (w : Scheduler.remote_worker) ->
            check (contains w.remote_reason "time limit") ("worker reason: " ^ w.remote_reason))
          (processes_of r).remote_workers;
        equal (processes_of r).lost [] "a worker was lost";
        check (wall >= 0.9 +. 0.5 -. 0.05) (Printf.sprintf "wall %.3f" wall) );
    ( "a forked worker's memory budget counts its own heap, not the supervisor's",
      fun () ->
        (* 128 MiB of live supervisor heap before the fork: every child inherits it, and a
           reading that counted it would start the worker near or over its budget. The search
           itself (100 given clauses of p(f^n(c))) grows the heap by far less. *)
        let words = 16 * 1024 * 1024 in
        let ballast = Array.make words 1 in
        check (Telemetry.domain_major_words () >= words) "the ballast is not on this Domain's heap";
        let base = quick_config ~seconds:2. () in
        let r =
          checked
            (Portfolio.processes ~workers:1 ~timing:fast_timing
               {
                 base with
                 reference = false;
                 engine = { base.engine with limits = { base.engine.limits with max_given = 100 } };
               }
               (parse "fof(a,axiom,p(c)).\nfof(b,axiom,![X]: (p(X) => p(f(X))))."))
        in
        let w = remote r 0 in
        let c = Option.get w.remote_counters in
        check (c.given > 0) "the worker ran no step";
        check
          (c.peak_domain_words >= 0 && c.peak_domain_words < words / 4)
          (Printf.sprintf "worker budget reading %d words with %d inherited (given %d)"
             c.peak_domain_words words c.given);
        (* The supervisor itself still reads its whole heap. *)
        check (Telemetry.budget_words () >= words) "the supervisor's reading lost its baseline";
        ignore (Sys.opaque_identity ballast) );
    ( "a worker that ignores the stop request is killed at the deadline",
      fun () ->
        let hook role _ =
          match role with
          | Portfolio.Worker 1 ->
              Sys.set_signal Sys.sigterm Sys.Signal_ignore;
              while true do
                Unix.sleepf 10.
              done
          | _ -> ()
        in
        let started = Unix.gettimeofday () in
        let r =
          checked
            (Portfolio.processes ~workers:2 ~timing:fast_timing ~hook
               { (quick_config ~seconds:0.5 ()) with max_size = 0; max_instances = max_int }
               (fun () -> Theory.create "zf"))
        in
        let wall = Unix.gettimeofday () -. started in
        let budget = 0.5 +. fast_timing.margin +. fast_timing.grace in
        check (wall >= budget -. 0.05 && wall < budget +. 0.5) (Printf.sprintf "wall %.3f" wall);
        let p = processes_of r in
        check (List.exists (fun s -> contains s "worker 1 lost") p.lost) "stuck worker not reported";
        check (contains r.reason "worker 1 lost") ("reason: " ^ r.reason);
        let w1 =
          List.find (fun (w : Scheduler.remote_worker) -> w.remote_id = 1) p.remote_workers
        in
        equal w1.remote_process.exit "signal SIGKILL" "stuck worker was not killed";
        let workers = Metrics_csv.workers r in
        equal (List.length (rows workers)) 3 "a lost worker keeps its CSV row";
        equal (List.nth (column workers "given") 1) "" "a lost worker has no counters" );
    ( "a crashed worker is lost while the others still prove",
      fun () ->
        let hook role _ =
          match role with Portfolio.Worker 1 -> Unix.kill (Unix.getpid ()) Sys.sigkill | _ -> ()
        in
        let r =
          checked
            (Portfolio.processes ~workers:2 ~timing:fast_timing ~hook (quick_config ())
               (parse refutable))
        in
        equal r.proof_source "heuristic:0" "the surviving worker's proof was not selected";
        check
          (List.exists (fun s -> contains s "worker 1 lost: no report") (processes_of r).lost)
          "crash not reported" );
    ( "an exception in a worker is an error after every process stopped",
      fun () ->
        let hook role _ =
          match role with Portfolio.Worker 1 -> invalid_arg "injected worker failure" | _ -> ()
        in
        (match
           Portfolio.processes ~workers:3 ~timing:fast_timing ~hook
             { (quick_config ~seconds:30. ()) with max_size = 0; max_instances = max_int }
             (fun () -> Theory.create "zf")
         with
        | _ -> failwith "worker exception was swallowed"
        | exception Invalid_argument m -> equal m "injected worker failure" "error text");
        no_children () );
    ( "cancellation stops every process cooperatively",
      fun () ->
        let started = Unix.gettimeofday () in
        let r =
          checked
            (Portfolio.processes ~workers:2 ~timing:fast_timing
               ~cancelled:(fun () -> Unix.gettimeofday () -. started > 0.3)
               {
                 (quick_config ~seconds:30. ()) with
                 max_size = 0;
                 max_instances = max_int;
                 reference = true;
                 reference_config = { seconds = 30.; max_trials = max_int; checkpoint = None };
               }
               (fun () -> Theory.create "zf"))
        in
        let wall = Unix.gettimeofday () -. started in
        check (wall < 0.3 +. fast_timing.grace) (Printf.sprintf "cancellation took %.3f s" wall);
        check (contains r.reason "cancelled") ("reason: " ^ r.reason);
        let p = processes_of r in
        equal p.lost [] "a cancelled worker was killed instead of stopping";
        check
          (List.for_all
             (fun (w : Scheduler.remote_worker) -> w.remote_counters <> None)
             p.remote_workers)
          "a cancelled worker sent no metrics" );
    ( "a certificate beyond the S-expression limits crosses intact",
      fun () ->
        let depth = 200 in
        let r = checked (Portfolio.processes ~workers:1 (quick_config ()) (parse (deep depth))) in
        let cert = Option.get r.certificate in
        check (Result.is_ok (Kernel.check (Tptp.parse (deep depth)) cert)) "deep proof fails replay";
        check
          (match Certificate_io.decode (Certificate_io.encode cert) with
          | _ -> false
          | exception Sexp.Error _ -> true)
          "the S-expression codec accepts this proof, so the test does not exercise the limit" );
    ( "frames carry more than the 32 MiB file limit and reject damaged streams",
      fun () ->
        (* Above the 32 MiB file limit and the 512-level nesting limit at once. *)
        let big () =
          let rec term n =
            if n = 0 then Wire.Fn (Wire.Original "c", [])
            else Wire.Fn (Wire.Original "f", [ term (n - 1) ])
          in
          {
            forged with
            theory = String.make (Sexp.max_file_bytes + (1024 * 1024)) 't';
            steps =
              [
                {
                  Wire.id = 0;
                  clause = [ positive (Wire.P ("p", [ term 600 ])) ];
                  rule = Wire.Input (0, 0);
                };
              ];
          }
        in
        check
          (match Certificate_io.decode (Certificate_io.encode (big ())) with
          | _ -> false
          | exception Sexp.Error _ -> true)
          "the S-expression codec accepts the large certificate";
        let rd, wr = Unix.pipe () in
        (match Unix.fork () with
        | 0 ->
            Unix.close rd;
            Process_frame.write wr
              (Portfolio.Worker_done
                 {
                   id = 0;
                   certificate = Some (big ());
                   proof_source = "heuristic:0";
                   reason = "big";
                   axioms = [];
                   traces = [];
                   cnf_mode = Wire.Hybrid;
                   row = [];
                   schema_rows = [];
                   counters = Scheduler.counters (Engine.create Engine.default_config);
                   profile = [];
                   cpu_seconds = 0.;
                   peak_rss_bytes = 0.;
                 });
            Unix._exit 0
        | _ -> ());
        Unix.close wr;
        let b = Buffer.create (1 lsl 20) and chunk = Bytes.create 65536 in
        let rec drain () =
          match Unix.read rd chunk 0 65536 with
          | 0 -> ()
          | n ->
              Buffer.add_subbytes b chunk 0 n;
              drain ()
        in
        drain ();
        Unix.close rd;
        ignore (Unix.wait ());
        let data = Buffer.contents b in
        check (String.length data > Sexp.max_file_bytes) "frame is not above the 32 MiB file limit";
        (match (Process_frame.unpack data : (Portfolio.message, string) result) with
        | Ok (Portfolio.Worker_done r) ->
            check (r.certificate = Some (big ())) "certificate changed in transit"
        | _ -> failwith "large frame was not decoded");
        let damaged = Bytes.of_string data in
        Bytes.set damaged (Bytes.length damaged / 2) 'X';
        check
          (Result.is_error
             (Process_frame.unpack (Bytes.to_string damaged) : (Portfolio.message, string) result))
          "a damaged frame was accepted";
        check
          (Result.is_error
             (Process_frame.unpack (String.sub data 0 (String.length data - 1))
               : (Portfolio.message, string) result))
          "a truncated frame was accepted";
        check
          (Result.is_error (Process_frame.unpack "garbage" : (Portfolio.message, string) result))
          "garbage was accepted";
        no_children () );
    ( "frame writes resume exactly after partial writes and EINTR",
      fun () ->
        (* Deterministic: a scripted single-write primitive returns short counts and raises
           EINTR having written nothing (the contract of Unix.single_write_substring). *)
        let payload = String.init 200_000 (fun i -> Char.chr (i * 31 land 255)) in
        let frame = Process_frame.encode payload in
        let out = Buffer.create (String.length frame) in
        let script = [| 1; -1; 65536; -1; -1; 7; 4096; 3; -1 |] in
        let calls = ref 0 and interrupted = ref 0 in
        let write _ s offset length =
          let step = script.(!calls mod Array.length script) in
          incr calls;
          if step < 0 then (
            incr interrupted;
            raise (Unix.Unix_error (Unix.EINTR, "single_write", "")))
          else
            let n = min step length in
            Buffer.add_substring out s offset n;
            n
        in
        Process_frame.write_all ~write Unix.stdout frame 0;
        check (Buffer.contents out = frame) "partial writes or EINTR changed the frame";
        check (!interrupted >= 3) "the script raised no EINTR";
        check
          (Process_frame.decode (Buffer.contents out) = Process_frame.Payload payload)
          "frame does not decode" );
    ( "a frame written while the reader stalls and signals arrive crosses intact",
      fun () ->
        (* The reader stays away until the writer is blocked on the full pipe; then three
           signals interrupt the writer 50 ms apart, and only then is the pipe drained. Every
           signal after the first write(2) of a call finds it blocked with nothing written, so
           Unix.write_substring (the primitive used before the EINTR fix: 64 KiB chunks, EINTR
           even after a partial write) duplicates bytes in this scenario every time. *)
        let transfer write =
          let frame =
            Process_frame.encode (String.init (1024 * 1024) (fun i -> Char.chr (i land 255)))
          in
          let rd, wr = Unix.pipe () and ready_rd, ready_wr = Unix.pipe () in
          let pid =
            match Unix.fork () with
            | 0 ->
                Unix.close rd;
                Unix.close ready_rd;
                let signals = ref 0 in
                Sys.set_signal Sys.sigusr1 (Sys.Signal_handle (fun _ -> incr signals));
                ignore (Unix.write_substring ready_wr "r" 0 1);
                (try write wr frame with _ -> Unix._exit 255);
                Unix._exit (min 100 !signals)
            | pid -> pid
          in
          Unix.close wr;
          Unix.close ready_wr;
          ignore (Unix.read ready_rd (Bytes.create 1) 0 1);
          Unix.close ready_rd;
          Unix.sleepf 0.1;
          for _ = 1 to 3 do
            Unix.kill pid Sys.sigusr1;
            Unix.sleepf 0.05
          done;
          let b = Buffer.create (2 * String.length frame) and chunk = Bytes.create 65536 in
          let rec drain () =
            match Unix.read rd chunk 0 65536 with
            | 0 -> ()
            | n ->
                Buffer.add_subbytes b chunk 0 n;
                drain ()
            | exception Unix.Unix_error (Unix.EINTR, _, _) -> drain ()
          in
          drain ();
          Unix.close rd;
          let signals = match snd (Unix.waitpid [] pid) with Unix.WEXITED n -> n | _ -> -1 in
          (Buffer.contents b = frame, signals)
        in
        (* The writer of every report frame, with its default primitive. *)
        let intact, signals = transfer (fun fd frame -> Process_frame.write_all fd frame 0) in
        check (signals >= 1 && signals <= 100) "no signal reached the blocked writer";
        check intact "frame damaged by signals during the write";
        let intact, signals =
          transfer (fun fd frame -> Process_frame.write_all ~write:Unix.write_substring fd frame 0)
        in
        check
          (signals >= 1 && not intact)
          "Unix.write_substring kept the frame intact, so the test does not exercise the bug";
        no_children () );
    ( "a certificate the supervisor rejects is an internal error, as in Domain mode",
      fun () ->
        (* A worker reports a certificate as if its own kernel had accepted it (run_search
           raises otherwise). The supervisor's kernel rejects it: the run must fail like a
           Domain worker whose check rejects its proof, not end in a quiet UNKNOWN. *)
        let forge role fd =
          match role with
          | Portfolio.Worker 0 ->
              Process_frame.write fd (report ~certificate:forged 0);
              Unix._exit 0
          | _ -> ()
        in
        let started = Unix.gettimeofday () in
        (match
           Portfolio.processes ~workers:3 ~timing:fast_timing ~hook:forge
             { (quick_config ~seconds:30. ()) with max_size = 0; max_instances = max_int }
             (fun () -> Theory.create "zf")
         with
        | _ -> failwith "a rejected certificate ended the run quietly"
        | exception Failure m ->
            check (String.starts_with ~prefix:(Scheduler.rejected_search_proof "") m) ("error: " ^ m);
            check (contains m "supervisor re-check of worker 0") ("error: " ^ m));
        no_children ();
        check (Unix.gettimeofday () -. started < 5.) "the other workers were not stopped" );
    ( "undecodable reports lose only their worker",
      fun () ->
        let hook role fd =
          match role with
          | Portfolio.Worker 1 ->
              ignore (Unix.write_substring fd "garbage" 0 7);
              Unix._exit 0
          | Portfolio.Worker 2 ->
              let frame = Process_frame.pack (report 2) in
              ignore (Unix.write_substring fd frame 0 (String.length frame - 1));
              Unix._exit 0
          | _ -> ()
        in
        let r =
          checked
            (Portfolio.processes ~workers:3 ~timing:fast_timing ~hook (quick_config ())
               (parse refutable))
        in
        equal r.proof_source "heuristic:0" "the intact worker's proof was not selected";
        let lost = (processes_of r).lost in
        check
          (List.exists (fun s -> contains s "worker 1 lost: bad frame") lost)
          "garbage not reported";
        check
          (List.exists (fun s -> contains s "worker 2 lost: truncated frame") lost)
          "truncated frame not reported" );
    ( "reports that arrive in the same poll are taken in spawn order",
      fun () ->
        (* The supervisor oversleeps its first poll while worker 1 and the reference report a
           proof, then worker 0. All three are ready in one poll: worker 0 wins, as in the
           Domain portfolio (lowest heuristic worker; the reference only without one). *)
        let source = "fof(f,axiom,$false)." in
        let heuristic = proof source in
        let natural =
          let module N = Natural_checker in
          Natural.certificate (Tptp.parse source)
            (N.certificate_code
               {
                 N.assumptions =
                   [ Wire_types.Pair (Number 0, N.permission_code (N.FixedPermission 0)) ];
                 deduction = N.Assume 0;
               })
        in
        check (Result.is_ok (Kernel.check (Tptp.parse source) natural)) "reference witness";
        let reference =
          {
            Reference.certificate = Some natural;
            reason = "certified reference refutation verified";
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
          (match role with
          | Portfolio.Worker 0 ->
              busy 0.1;
              Process_frame.write fd (report ~certificate:heuristic 0)
          | Portfolio.Worker i -> Process_frame.write fd (report ~certificate:heuristic i)
          | Portfolio.Reference_role ->
              Process_frame.write fd (Portfolio.Reference_done (reference, 0., 0.)));
          Unix._exit 0
        in
        let first = ref true in
        let cancelled () =
          if !first then (
            first := false;
            Unix.sleepf 2.);
          false
        in
        let r =
          checked
            (Portfolio.processes ~workers:2 ~timing:fast_timing ~hook ~cancelled
               { (quick_config ()) with reference = true }
               (parse source))
        in
        equal r.proof_source "heuristic:0" "spawn order did not decide the winner";
        check (r.certificate = Some heuristic) "the winner's certificate was not selected";
        check
          ((Option.get r.reference_report).certificate = None)
          "the reference kept a proof that lost" );
    ( "a search announces its proof once, before reporting it",
      fun () ->
        let calls = ref 0 in
        let r =
          Scheduler.run_search
            ~on_proof:(fun () -> incr calls)
            (quick_config ()) (Tptp.parse refutable)
        in
        check (r.certificate <> None) "no proof";
        equal !calls 1 "proof announcements";
        let calls = ref 0 in
        let r =
          Scheduler.run_search
            ~on_proof:(fun () -> incr calls)
            (quick_config ()) (Tptp.parse "fof(p,axiom,p(a)).")
        in
        check (r.certificate = None) "consistent input refuted";
        equal !calls 0 "announcement without a proof" );
    ( "a worker that announced a proof is not killed before it reports it",
      fun () ->
        (* Worker 0 announces a proof, then needs 1.5 s to check and encode it: longer than the
           0.3 s budget, the margin and the grace together (the supervisor used to kill it 0.8 s
           after the start). The announcement buys it the proof grace. *)
        let cert = proof refutable in
        let hook role fd =
          match role with
          | Portfolio.Worker 0 ->
              Portfolio.write_notice fd;
              busy 1.5;
              Process_frame.write fd (report ~certificate:cert 0);
              Unix._exit 0
          | _ -> ()
        in
        let started = Unix.gettimeofday () in
        let r =
          checked
            (Portfolio.processes ~workers:1
               ~timing:{ fast_timing with proof_grace = 10. }
               ~hook (quick_config ~seconds:0.3 ()) (parse refutable))
        in
        let wall = Unix.gettimeofday () -. started in
        check (r.certificate = Some cert) ("the announced proof was lost: " ^ r.reason);
        equal r.proof_source "heuristic:0" "proof source";
        equal (processes_of r).lost [] "the announcing worker was lost";
        check (wall >= 1.5 && wall < 5.) (Printf.sprintf "wall %.3f" wall) );
    ( "an announced proof is bounded and does not outlast a verified one",
      fun () ->
        let hang role fd =
          match role with
          | Portfolio.Worker 0 ->
              Portfolio.write_notice fd;
              Sys.set_signal Sys.sigterm Sys.Signal_ignore;
              while true do
                Unix.sleepf 10.
              done
          | _ -> ()
        in
        (* Alone, a worker that announces and never reports is killed after the proof grace. *)
        let started = Unix.gettimeofday () in
        let r =
          checked
            (Portfolio.processes ~workers:1
               ~timing:{ fast_timing with proof_grace = 1. }
               ~hook:hang (quick_config ~seconds:0.3 ()) (parse refutable))
        in
        let wall = Unix.gettimeofday () -. started in
        let limit = 0.3 +. fast_timing.margin +. 1. in
        check (wall >= limit -. 0.05 && wall < limit +. 1.) (Printf.sprintf "wall %.3f" wall);
        check (r.certificate = None) "a proof appeared";
        check
          (List.exists
             (fun s -> contains s "worker 0 lost: no report (signal SIGKILL, after announcing")
             (processes_of r).lost)
          "the silent announcement was not reported";
        (* Once worker 1's proof is verified, the announcing worker gets only the plain grace. *)
        let started = Unix.gettimeofday () in
        let r =
          checked
            (Portfolio.processes ~workers:2
               ~timing:{ fast_timing with proof_grace = 30. }
               ~hook:hang (quick_config ~seconds:30. ()) (parse refutable))
        in
        let wall = Unix.gettimeofday () -. started in
        equal r.proof_source "heuristic:1" "the verified proof was not selected";
        check (wall < 5.) (Printf.sprintf "an announcement delayed a verified proof: %.3f s" wall);
        equal (remote r 0).remote_process.exit "signal SIGKILL" "announcing worker" );
    ( "a long supervisor check neither kills nor loses a worker still writing its report",
      fun () ->
        (* Worker 0 reports a valid certificate that takes the supervisor's kernel several times
           the grace to check (duplicate input steps). Meanwhile worker 1 writes a report larger
           than a pipe holds. The supervisor used to read nothing during its check and then kill
           worker 1, blocked on the full pipe, because its grace had passed. *)
        let cert = proof refutable in
        let input =
          List.find
            (fun (s : Wire.step) -> match s.rule with Wire.Input _ -> true | _ -> false)
            cert.steps
        in
        let top = List.fold_left (fun m (s : Wire.step) -> max m s.id) 0 cert.steps in
        let slow =
          {
            cert with
            steps = cert.steps @ List.init 150_000 (fun k -> { input with id = top + 1 + k });
          }
        in
        let before = Unix.gettimeofday () in
        check (Result.is_ok (Kernel.check (Tptp.parse refutable) slow)) "padded certificate";
        let seconds = Unix.gettimeofday () -. before in
        let grace = Float.max 0.02 (seconds /. 5.) in
        let hook role fd =
          match role with
          | Portfolio.Worker 0 ->
              Process_frame.write fd (report ~certificate:slow 0);
              Unix._exit 0
          | Portfolio.Worker 1 ->
              busy (seconds /. 4.);
              Process_frame.write fd (report ~row:[ String.make (4 * 1024 * 1024) 'r' ] 1);
              Unix._exit 0
          | _ -> ()
        in
        let r =
          checked
            (Portfolio.processes ~workers:2
               ~timing:{ fast_timing with grace; proof_grace = grace }
               ~hook (quick_config ~seconds:30. ()) (parse refutable))
        in
        equal r.proof_source "heuristic:0" "the slow certificate was not selected";
        equal (processes_of r).lost [] "a worker was lost during the supervisor's check";
        equal (remote r 1).remote_process.exit "exit 0" "the writing worker was killed";
        check ((remote r 1).remote_row <> None) "the writing worker's report is missing" );
    ( "a schema-lane proof announces itself before it is extracted",
      fun () ->
        (* The lane refutes naive by itself: the first condition of the test prior
           is ~(x in x), and with no exhaustive budget the main engine has no clause.
           A process worker announces such a proof like an engine proof, so the
           supervisor grants it the proof grace. *)
        let announced = ref 0 in
        let r =
          Scheduler.run_search
            ~on_proof:(fun () -> incr announced)
            (lane_naive_config ()) (Theory.create "naive")
        in
        check (r.certificate <> None) ("the lane did not refute naive: " ^ r.reason);
        equal r.proof_source "probe:0" "the lane proof was labelled as an engine proof";
        equal !announced 1 "a lane proof was not announced exactly once" );
    ( "a process worker's schema-lane proof is selected, re-checked and labelled probe:N",
      fun () ->
        let r =
          checked
            (Portfolio.processes ~workers:2 (lane_naive_config ()) (fun () -> Theory.create "naive"))
        in
        check (r.certificate <> None) ("the lane proof was lost: " ^ r.reason);
        (* Worker 0 takes the even prior indices (its worker count reached the
           child), among them the first, ~(x in x). *)
        equal r.proof_source "probe:0" "the selected lane proof was not labelled probe:0";
        check
          (Result.is_ok (Kernel.check (Theory.create "naive") (Option.get r.certificate)))
          "the selected lane certificate fails replay";
        check (contains r.reason "[lane: ") "the lane statistics are missing from the reason";
        equal (processes_of r).lost [] "a worker was lost" );
    ( "a child that never polls dies with its SIGKILLed supervisor (lifeline)",
      fun () ->
        (* Worker 0 ignores SIGTERM and never calls [cancelled]: neither a stop request nor the
           polled getppid check reaches it. Only the lifeline can end it once its supervisor
           is gone. *)
        let supervisor, worker =
          forked_supervisor (fun announce ->
              let hook role _ =
                match role with
                | Portfolio.Worker 0 ->
                    Sys.set_signal Sys.sigterm Sys.Signal_ignore;
                    announce ();
                    busy 1e9
                | _ -> ()
              in
              ignore
                (Portfolio.processes ~workers:1 ~hook
                   { (quick_config ~seconds:60. ()) with reference = false }
                   (fun () -> Theory.create "zf")))
        in
        Unix.kill supervisor Sys.sigkill;
        ignore (Unix.waitpid [] supervisor);
        let lived = await_death worker 3. in
        check (dead worker) "the worker outlived its SIGKILLed supervisor";
        check (lived < 1.) (Printf.sprintf "the orphaned worker lived %.3f s" lived);
        no_children () );
    ( "an orphaned reference saves its checkpoint, then exits",
      fun () ->
        with_dir (fun dir ->
            let path = Filename.concat dir "reference.checkpoint" in
            let supervisor, reference =
              forked_supervisor (fun announce ->
                  let hook role _ =
                    match role with Portfolio.Reference_role -> announce () | _ -> ()
                  in
                  ignore
                    (Portfolio.processes ~hook
                       {
                         Scheduler.default_config with
                         reference_only = true;
                         reference_config =
                           { seconds = 60.; max_trials = max_int; checkpoint = Some path };
                       }
                       (fun () -> Tptp.parse "fof(p,axiom,p(a)).")))
            in
            Unix.sleepf 0.3;
            Unix.kill supervisor Sys.sigkill;
            ignore (Unix.waitpid [] supervisor);
            let lived = await_death reference 15. in
            check (dead reference) "the reference outlived its SIGKILLed supervisor";
            check (lived < 5.) (Printf.sprintf "the orphaned reference lived %.3f s" lived);
            check (Sys.file_exists path) "the orphaned reference saved no checkpoint";
            check
              (Array.for_all (fun n -> not (Filename.check_suffix n ".tmp")) (Sys.readdir dir))
              "a temporary file was left";
            let again =
              checked
                (Portfolio.processes
                   {
                     Scheduler.default_config with
                     reference_only = true;
                     reference_config =
                       { seconds = 0.05; max_trials = max_int; checkpoint = Some path };
                   }
                   (fun () -> Tptp.parse "fof(p,axiom,p(a))."))
            in
            check (Option.get again.reference_report).resumed "the saved checkpoint does not resume")
    );
    ( "the supervisor reaps its children itself even when SIGCHLD is ignored",
      fun () ->
        (* With SIGCHLD ignored the kernel reaps exited children at once (waitpid then fails
           with ECHILD) and their IDs can be reused while the supervisor may still signal them.
           The supervisor restores the default action for the run and the caller's afterwards. *)
        let previous = Sys.signal Sys.sigchld Sys.Signal_ignore in
        let r, during =
          Fun.protect
            ~finally:(fun () -> Sys.set_signal Sys.sigchld previous)
            (fun () ->
              let r =
                Portfolio.processes ~workers:2 ~timing:fast_timing
                  { (quick_config ()) with reference = true }
                  (parse refutable)
              in
              (r, Sys.signal Sys.sigchld Sys.Signal_ignore))
        in
        ignore (checked r);
        check (during = Sys.Signal_ignore) "the caller's SIGCHLD action was not restored";
        check (r.certificate <> None) "the proof was lost";
        List.iter
          (fun (w : Scheduler.remote_worker) ->
            equal w.remote_process.exit "exit 0" "a worker was not reaped by the supervisor")
          (processes_of r).remote_workers;
        equal (Option.get (processes_of r).reference_process).exit "exit 0"
          "the reference was not reaped by the supervisor" );
    ( "a worker that runs out of memory or stack loses only itself",
      fun () ->
        let hook role _ =
          match role with
          | Portfolio.Worker 1 -> raise Out_of_memory
          | Portfolio.Worker 2 -> raise Stack_overflow
          | _ -> ()
        in
        let r =
          checked
            (Portfolio.processes ~workers:3 ~timing:fast_timing ~hook (quick_config ())
               (parse refutable))
        in
        equal r.proof_source "heuristic:0" "the surviving worker's proof was not selected";
        let lost = (processes_of r).lost in
        check
          (List.exists (fun s -> contains s "worker 1 lost: out of memory") lost)
          "out of memory";
        check
          (List.exists (fun s -> contains s "worker 2 lost: stack overflow") lost)
          "stack overflow" );
    ( "a reference killed while writing leaves no temporary file, and no descriptor stays open",
      fun () ->
        with_dir (fun dir ->
            let path = Filename.concat dir "reference.checkpoint" in
            let hook role _ =
              match role with
              | Portfolio.Reference_role ->
                  (* What a SIGKILL in the middle of [Sexp.write_file] leaves. *)
                  let name =
                    Filename.concat dir
                      (Sexp.temp_prefix (Unix.getpid ()) ^ "partial" ^ Sexp.temp_suffix)
                  in
                  close_out (open_out name);
                  Unix.kill (Unix.getpid ()) Sys.sigkill
              | Portfolio.Worker 1 ->
                  Sys.set_signal Sys.sigterm Sys.Signal_ignore;
                  busy 1e9
              | _ -> ()
            in
            let before = open_fds () in
            let r =
              checked
                (Portfolio.processes ~workers:2 ~timing:fast_timing ~hook
                   {
                     (quick_config ()) with
                     reference = true;
                     reference_config =
                       { seconds = 3.; max_trials = max_int; checkpoint = Some path };
                   }
                   (parse refutable))
            in
            equal (open_fds ()) before "the supervisor left a descriptor open";
            equal r.proof_source "heuristic:0" "the surviving worker's proof was not selected";
            equal (Option.get (processes_of r).reference_process).exit "signal SIGKILL" "reference";
            equal (remote r 1).remote_process.exit "signal SIGKILL" "stuck worker";
            check
              (Array.for_all (fun n -> not (Filename.check_suffix n ".tmp")) (Sys.readdir dir))
              "the killed reference's temporary file was left") );
    ( "a run removes the temporary files of dead writers in its checkpoint directory",
      fun () ->
        with_dir (fun dir ->
            let dead =
              match Unix.fork () with
              | 0 -> Unix._exit 0
              | pid ->
                  ignore (Unix.waitpid [] pid);
                  pid
            in
            let file pid tag =
              Filename.concat dir (Sexp.temp_prefix pid ^ tag ^ Sexp.temp_suffix)
            in
            let stale = file dead "stale" and live = file (Unix.getpid ()) "live" in
            let legacy = Filename.concat dir (".axiom-fuzzer-legacy" ^ Sexp.temp_suffix) in
            List.iter (fun f -> close_out (open_out f)) [ stale; live; legacy ];
            ignore
              (checked
                 (Portfolio.processes
                    {
                      Scheduler.default_config with
                      reference_only = true;
                      reference_config =
                        {
                          seconds = 0.05;
                          max_trials = max_int;
                          checkpoint = Some (Filename.concat dir "reference.checkpoint");
                        };
                    }
                    (fun () -> Tptp.parse "fof(p,axiom,p(a)).")));
            check (not (Sys.file_exists stale)) "the dead writer's temporary file was kept";
            check (Sys.file_exists live) "a live process's temporary file was removed";
            check (Sys.file_exists legacy) "a temporary file without a process ID was removed") );
    ( "Domain portfolio remains reachable for A/A runs",
      fun () ->
        (* Last: spawning a Domain forbids every later fork in this process. *)
        let r =
          Portfolio.run ~isolation:Portfolio.Domains ~workers:2 (quick_config ()) (parse refutable)
        in
        check (r.certificate <> None && r.processes = None) "Domain portfolio result";
        check
          (match Portfolio.processes ~workers:1 (quick_config ()) (parse refutable) with
          | _ -> false
          | exception Invalid_argument _ -> true)
          "fork after a Domain was not rejected";
        no_children () );
  ]

let () = run tests
