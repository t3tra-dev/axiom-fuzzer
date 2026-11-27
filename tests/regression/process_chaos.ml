(* One randomized reclamation trial of [Portfolio.processes] with synthetic children.

   process_chaos.exe MARKER SEED DIR [KILL_P]

   The trial forks a supervisor that runs a portfolio whose children never search: each child's
   hook picks a behaviour (report, prove, hang ignoring SIGTERM, stop cooperatively on a signal,
   crash, raise, write garbage, exit silently, announce a proof and hang, write a slow large
   report) and ends with [Unix._exit], so no solver work runs. Meanwhile the trial sends random
   signals at random times to the supervisor (SIGTERM/SIGINT/SIGHUP cancel it cooperatively, as
   in the CLI; SIGKILL kills it; SIGSTOP is continued later) and to its children (SIGTERM,
   SIGINT, SIGHUP, SIGKILL, SIGSEGV, SIGABRT, SIGSTOP + SIGCONT). It prints one JSON line. MARKER
   is only carried in argv, so that the driver (process_chaos.py) can find any process of the
   trial, the forked ones included, with ps. The supervisor exits 0 when the portfolio returned,
   10 when it raised the error defined for a failed child, 30 when a child was left unreaped. *)
open Axiom_fuzzer

let refutable = "fof(a,axiom,p(c)).\nfof(b,axiom,![X]: ~p(X))."

type behaviour =
  | Report of float
  | Prove of float
  | Hang_ignoring_term
  | Stop_on_signal of float
  | Crash of float * int
  | Raise_fatal
  | Raise_resource
  | Garbage
  | Silent
  | Announce_and_hang
  | Slow_big_report of float

let name = function
  | Report _ -> "report"
  | Prove _ -> "prove"
  | Hang_ignoring_term -> "hang-ignoring-term"
  | Stop_on_signal _ -> "stop-on-signal"
  | Crash _ -> "crash"
  | Raise_fatal -> "raise-fatal"
  | Raise_resource -> "raise-resource"
  | Garbage -> "garbage"
  | Silent -> "silent"
  | Announce_and_hang -> "announce-and-hang"
  | Slow_big_report _ -> "slow-big-report"

let sleep_for seconds =
  let until = Unix.gettimeofday () +. seconds in
  while Unix.gettimeofday () < until do
    try Unix.sleepf (Float.min 0.01 (until -. Unix.gettimeofday ()))
    with Unix.Unix_error (Unix.EINTR, _, _) -> ()
  done

let worker_report ?certificate ?(row = []) id =
  Portfolio.Worker_done
    {
      id;
      certificate;
      proof_source = "heuristic:" ^ string_of_int id;
      reason = "chaos report";
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

let reference_report () =
  Portfolio.Reference_done
    ( {
        Reference.certificate = None;
        reason = "chaos reference";
        tested = 0;
        trials = 0;
        script_tested = 0;
        byte_tested = 0;
        stage = 0;
        seconds = 0.;
        replay_seconds = 0.;
        axioms = [];
        resumed = false;
        peak_domain_words = -1;
      },
      0.,
      0. )

let () =
  let seed = int_of_string Sys.argv.(2) and dir = Sys.argv.(3) in
  let rng = Random.State.make [| seed |] in
  let pick l = List.nth l (Random.State.int rng (List.length l)) in
  let uniform a b = a +. Random.State.float rng (b -. a) in
  let workers = 1 + Random.State.int rng 4 in
  let reference = Random.State.bool rng in
  let checkpoint = reference && Random.State.int rng 3 = 0 in
  let seconds = pick [ 0.2; 0.4; 0.8 ] in
  let timing =
    {
      Portfolio.margin = pick [ 0.05; 0.2 ];
      grace = pick [ 0.1; 0.3 ];
      reference_grace = pick [ 0.3; 0.6 ];
      proof_grace = pick [ 0.3; 0.6 ];
    }
  in
  let behaviour () =
    match Random.State.int rng 12 with
    | 0 | 1 -> Report (uniform 0. (seconds *. 1.5))
    | 2 -> Prove (uniform 0. (seconds *. 1.5))
    | 3 -> Hang_ignoring_term
    | 4 -> Stop_on_signal (uniform 0. (seconds *. 2.))
    | 5 -> Crash (uniform 0. seconds, pick [ Sys.sigkill; Sys.sigsegv; Sys.sigabrt ])
    | 6 -> Raise_fatal
    | 7 -> Raise_resource
    | 8 -> Garbage
    | 9 -> Silent
    | 10 -> Announce_and_hang
    | _ -> Slow_big_report (uniform 0. seconds)
  in
  let behaviours = Array.init (workers + 1) (fun _ -> behaviour ()) in
  let source = Tptp.parse refutable in
  let cert =
    Option.get
      (Scheduler.run_search
         {
           Test_support.config with
           engine =
             {
               Test_support.config.engine with
               limits = { Test_support.config.engine.limits with seconds = 5. };
             };
         }
         source)
        .certificate
  in
  (* Children tell the trial their process IDs through this pipe. *)
  let pids_rd, pids_wr = Unix.pipe () in
  let hook role fd =
    let index, tag =
      match role with
      | Portfolio.Worker i -> (i, Printf.sprintf "w%d" i)
      | Reference_role -> (workers, "r")
    in
    let line = Printf.sprintf "%s %d\n" tag (Unix.getpid ()) in
    ignore (Unix.write_substring pids_wr line 0 (String.length line));
    let report () =
      match role with
      | Portfolio.Worker i -> worker_report i
      | Reference_role -> reference_report ()
    in
    let finish message =
      Process_frame.write fd message;
      Unix._exit 0
    in
    match behaviours.(index) with
    | Report d ->
        sleep_for d;
        finish (report ())
    | Prove d -> (
        sleep_for d;
        match role with
        | Portfolio.Worker i ->
            Portfolio.write_notice fd;
            finish (worker_report ~certificate:cert i)
        | Reference_role -> finish (report ()))
    | Hang_ignoring_term ->
        List.iter
          (fun s -> Sys.set_signal s Sys.Signal_ignore)
          [ Sys.sigterm; Sys.sigint; Sys.sighup ];
        sleep_for 1e9;
        Unix._exit 0
    | Stop_on_signal d ->
        List.iter
          (fun s -> Sys.set_signal s (Sys.Signal_handle (fun _ -> finish (report ()))))
          [ Sys.sigterm; Sys.sigint; Sys.sighup ];
        sleep_for d;
        finish (report ())
    | Crash (d, signal) ->
        sleep_for d;
        Unix.kill (Unix.getpid ()) signal;
        sleep_for 1e9;
        Unix._exit 0
    | Raise_fatal -> failwith "chaos: injected failure"
    | Raise_resource -> raise Out_of_memory
    | Garbage ->
        ignore (Unix.write_substring fd "garbage" 0 7);
        Unix._exit 0
    | Silent -> Unix._exit 0
    | Announce_and_hang ->
        (match role with Portfolio.Worker _ -> Portfolio.write_notice fd | Reference_role -> ());
        Sys.set_signal Sys.sigterm Sys.Signal_ignore;
        sleep_for 1e9;
        Unix._exit 0
    | Slow_big_report d ->
        sleep_for d;
        let frame =
          Process_frame.pack
            (match role with
            | Portfolio.Worker i -> worker_report ~row:[ String.make (2 * 1024 * 1024) 'x' ] i
            | Reference_role -> reference_report ())
        in
        let n = String.length frame in
        let rec go off =
          if off < n then (
            let k = min 65536 (n - off) in
            let w =
              try Unix.single_write_substring fd frame off k
              with Unix.Unix_error (Unix.EINTR, _, _) -> 0
            in
            sleep_for 0.002;
            go (off + w))
        in
        go 0;
        Unix._exit 0
  in
  let config =
    {
      Test_support.config with
      reference;
      reference_config =
        {
          seconds;
          max_trials = max_int;
          checkpoint =
            (if checkpoint then Some (Filename.concat dir "reference.checkpoint") else None);
        };
      engine =
        {
          Test_support.config.engine with
          limits = { Test_support.config.engine.limits with seconds };
        };
    }
  in
  let started = Unix.gettimeofday () in
  let supervisor =
    match Unix.fork () with
    | 0 ->
        Unix.close pids_rd;
        let interrupted = Atomic.make false in
        List.iter
          (fun s -> Sys.set_signal s (Sys.Signal_handle (fun _ -> Atomic.set interrupted true)))
          [ Sys.sigterm; Sys.sigint; Sys.sighup ];
        let code =
          match
            Portfolio.processes ~workers ~timing ~hook
              ~cancelled:(fun () -> Atomic.get interrupted)
              config
              (fun () -> Tptp.parse refutable)
          with
          | _ -> 0
          | exception Failure m when String.starts_with ~prefix:"chaos: injected failure" m -> 10
          | exception _ -> 20
        in
        let code =
          match Unix.waitpid [ Unix.WNOHANG ] (-1) with
          | exception Unix.Unix_error (Unix.ECHILD, _, _) -> code
          | _ -> 30
        in
        Unix._exit code
    | pid -> pid
  in
  Unix.close pids_wr;
  Unix.set_nonblock pids_rd;
  let pids = Hashtbl.create 8 and buffer = Buffer.create 256 in
  let read_pids () =
    let chunk = Bytes.create 4096 in
    let rec go () =
      match Unix.read pids_rd chunk 0 4096 with
      | 0 -> ()
      | n ->
          Buffer.add_subbytes buffer chunk 0 n;
          go ()
      | exception Unix.Unix_error ((Unix.EAGAIN | Unix.EWOULDBLOCK | Unix.EINTR), _, _) -> ()
    in
    go ();
    let text = Buffer.contents buffer in
    match String.rindex_opt text '\n' with
    | None -> ()
    | Some last ->
        String.split_on_char '\n' (String.sub text 0 last)
        |> List.iter (fun l ->
            match String.split_on_char ' ' l with
            | [ tag; pid ] -> Hashtbl.replace pids tag (int_of_string pid)
            | _ -> ());
        Buffer.clear buffer;
        Buffer.add_string buffer (String.sub text (last + 1) (String.length text - last - 1))
  in
  let horizon = seconds +. timing.margin +. Float.max timing.grace timing.proof_grace +. 0.3 in
  let injections =
    (List.init (Random.State.int rng 4) (fun _ ->
         let at = uniform 0. horizon in
         let target = pick [ `Supervisor; `Child; `Child; `Children ] in
         let signal =
           match target with
           | `Supervisor -> pick [ "TERM"; "INT"; "HUP"; "KILL"; "STOP" ]
           | _ -> pick [ "TERM"; "INT"; "HUP"; "KILL"; "SEGV"; "ABRT"; "STOP" ]
         in
         (at, target, signal))
    (* KILL_P (optional): the probability of one more SIGKILL to the supervisor at a uniformly
       random time, to exercise the children's lifeline from start-up to shutdown. *)
    @
    if Array.length Sys.argv > 4 && Random.State.float rng 1. < float_of_string Sys.argv.(4) then
      [ (uniform 0. horizon, `Supervisor, "KILL") ]
    else [])
    |> List.sort compare
  in
  let number = function
    | "TERM" -> Sys.sigterm
    | "INT" -> Sys.sigint
    | "HUP" -> Sys.sighup
    | "KILL" -> Sys.sigkill
    | "SEGV" -> Sys.sigsegv
    | "ABRT" -> Sys.sigabrt
    | _ -> Sys.sigstop
  in
  let status = ref None in
  let poll () =
    if !status = None then
      match Unix.waitpid [ Unix.WNOHANG ] supervisor with
      | 0, _ -> ()
      | _, s -> status := Some s
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> ()
  in
  let sent = ref [] and resumes = ref [] and supervisor_killed = ref false in
  let send pid signal =
    try
      Unix.kill pid signal;
      true
    with Unix.Unix_error _ -> false
  in
  let limit =
    seconds +. timing.margin +. (2. *. Float.max timing.reference_grace timing.proof_grace) +. 5.
  in
  let pending = ref injections in
  while !status = None && Unix.gettimeofday () -. started < limit do
    let now = Unix.gettimeofday () -. started in
    read_pids ();
    List.iter (fun (t, pid) -> if t <= now then ignore (send pid Sys.sigcont)) !resumes;
    resumes := List.filter (fun (t, _) -> t > now) !resumes;
    (match !pending with
    | (at, target, signal) :: rest when at <= now ->
        pending := rest;
        let children = Hashtbl.fold (fun _ pid acc -> pid :: acc) pids [] in
        let targets =
          match target with
          | `Supervisor -> [ supervisor ]
          | `Child -> (
              match children with
              | [] -> []
              | l -> [ List.nth l (Random.State.int rng (List.length l)) ])
          | `Children -> children
        in
        (* The supervisor is our child: signal it only while it is unreaped. *)
        poll ();
        if !status = None then (
          let delivered = List.exists Fun.id (List.map (fun p -> send p (number signal)) targets) in
          if signal = "KILL" && target = `Supervisor && delivered then supervisor_killed := true;
          if signal = "STOP" then
            resumes := List.map (fun p -> (now +. uniform 0.05 0.8, p)) targets @ !resumes;
          sent :=
            Printf.sprintf "{\"at\":%.4f,\"target\":\"%s\",\"signal\":\"%s\",\"delivered\":%b}" now
              (match target with
              | `Supervisor -> "supervisor"
              | `Child -> "child"
              | `Children -> "children")
              signal delivered
            :: !sent)
    | _ -> ());
    poll ();
    Unix.sleepf 0.001
  done;
  let hung = !status = None in
  if hung then (
    ignore (send supervisor Sys.sigcont);
    ignore (send supervisor Sys.sigkill);
    status := Some (snd (Unix.waitpid [] supervisor)));
  (* The stopper owns what it stopped: continue it, even after the supervisor is gone. *)
  List.iter (fun (_, pid) -> ignore (send pid Sys.sigcont)) !resumes;
  read_pids ();
  let fatal_assigned = Array.exists (fun b -> b = Raise_fatal) behaviours in
  let code, problem =
    match !status with
    | Some (Unix.WEXITED 0) -> (0, None)
    | Some (Unix.WEXITED 10) when fatal_assigned -> (10, None)
    | Some (Unix.WEXITED 30) -> (30, Some "a child was left unreaped")
    | Some (Unix.WEXITED n) -> (n, Some (Printf.sprintf "supervisor exit %d" n))
    | Some (Unix.WSIGNALED s) when s = Sys.sigkill && !supervisor_killed -> (-9, None)
    | Some (Unix.WSIGNALED s) -> (s, Some (Printf.sprintf "supervisor died by signal %d" s))
    | Some (Unix.WSTOPPED s) -> (s, Some "supervisor stopped")
    | None -> (-1, Some "no status")
  in
  let problem = if hung then Some "the supervisor missed its deadlines" else problem in
  Printf.printf
    "{\"seed\":%d,\"workers\":%d,\"reference\":%b,\"checkpoint\":%b,\"seconds\":%g,\"behaviours\":[%s],\"sent\":[%s],\"children\":[%s],\"code\":%d,\"wall\":%.4f,\"problem\":%s}\n"
    seed workers reference checkpoint seconds
    (String.concat "," (Array.to_list (Array.map (fun b -> "\"" ^ name b ^ "\"") behaviours)))
    (String.concat "," (List.rev !sent))
    (String.concat "," (Hashtbl.fold (fun _ pid acc -> string_of_int pid :: acc) pids []))
    code
    (Unix.gettimeofday () -. started)
    (match problem with None -> "null" | Some p -> "\"" ^ p ^ "\"")
