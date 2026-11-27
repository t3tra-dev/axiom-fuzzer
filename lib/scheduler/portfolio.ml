(* Portfolio isolation: heuristic workers and the certified reference either share this
   process as OCaml Domains ([Scheduler.portfolio]) or each run in a forked OS process.

   OCaml 5 Domains share stop-the-world minor collections, so every Domain waits for the
   slowest one at each collection and the allocation-heavy reference sets the collection rate.
   Processes share no heap. The supervisor (this process) forks every child before any Domain
   could exist (OCaml 5 refuses [Unix.fork] afterwards), waits with a deadline, and kills the
   children's process groups if they do not stop when asked. A child reports once, through a
   pipe, with a length-prefixed binary frame ([Process_frame]); a heuristic worker that found a
   proof first sends a one-byte notice ([proof_notice]). The supervisor trusts nothing in a
   report: a certificate becomes the result only after [Kernel.check] accepts it against the
   supervisor's own copy of the theory. An undecodable or truncated report only loses that
   child's work. A certificate that the child's own kernel accepted but the supervisor's
   rejects is an internal error, raised after every child is reaped, as the Domain portfolio
   raises when a worker's check rejects its proof.

   Reclamation (docs/architecture.md, "Processes"): every child leads its own session and
   process group; the supervisor signals a group only while its leader is unreaped (so the ID
   cannot have been reused), keeps SIGCHLD at its default action during the run (so the kernel
   never reaps a child behind its back), and reaps every child on every exit path. A child
   cannot outlive the supervisor: a lifeline pipe whose only write end the supervisor holds
   reaches end-of-file when the supervisor dies, however it dies, and a thread in the child
   that blocks on it then ends the child ([lifeline_start]); a getppid check against the PID
   read before the fork remains as a second, polled path. *)

type isolation = Domains | Processes
type role = Worker of int | Reference_role

type worker_report = {
  id : int;
  certificate : Wire.certificate option;
  proof_source : string;
      (** The worker's own label of its proof: "heuristic:i", or "probe:i" for a schema-lane proof
          (the selected result uses it). *)
  reason : string;
  axioms : Wire.axiom list;
  traces : Scheduler.trace list;
  cnf_mode : Wire.cnf_mode;
  row : string list;
  schema_rows : string list list;
  counters : Scheduler.counters;
  profile : (string * Pipeline_profile.sample * int) list;
  cpu_seconds : float;
  peak_rss_bytes : float;
}

type message =
  | Worker_done of worker_report
  | Reference_done of Reference.report * float * float  (** report, CPU seconds, peak RSS *)
  | Failed of (string * string)  (** exception kind and message *)

type timing = {
  margin : float;  (** after the longest budget, before asking children to stop *)
  grace : float;  (** after asking a heuristic worker to stop, before killing its group *)
  reference_grace : float;  (** the same for the reference when it saves a checkpoint *)
  proof_grace : float;
      (** the same for a heuristic worker that announced a proof and has not reported it yet, while
          no proof is verified and no child failed *)
}

let default_timing = { margin = 0.5; grace = 1.0; reference_grace = 10.0; proof_grace = 10.0 }

(* A heuristic worker that has derived the empty clause writes this byte before its report
   frame (a frame starts with 'A'). It then extracts, checks and encodes the proof, which no
   stop request interrupts, so the supervisor waits [proof_grace] for it instead of [grace]. *)
let proof_notice = '\001'

let write_notice fd =
  let byte = Bytes.make 1 proof_notice in
  let rec go () =
    match Unix.single_write fd byte 0 1 with
    | _ -> ()
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> go ()
  in
  try go () with Unix.Unix_error _ -> ()

(* The reference process checks its guard (cancellation and the clock) every [reference_batch]
   ticks; clock reads otherwise dominate its loop. *)
let reference_batch = 64

(* See lib/process_stubs.c: a detached thread ends this process (and its process group) when
   [fd] reaches end-of-file, after a SIGTERM and [grace_ms] milliseconds if [grace_ms] > 0. *)
external lifeline_start : Unix.file_descr -> int -> unit = "axiom_lifeline_start"

(* Exhausted resources of one child lose only that child, like a memory-killed process; every
   other exception is an error of the whole run, as in the Domain portfolio. *)
let resource_kind = "resource"

let describe = function
  | Out_of_memory -> (resource_kind, "out of memory")
  | Stack_overflow -> (resource_kind, "stack overflow")
  | Invalid_argument m -> ("invalid_argument", m)
  | Failure m -> ("failure", m)
  | Sys_error m -> ("sys_error", m)
  | Sexp.Error m -> ("sexp", m)
  | Tptp.Error m -> ("tptp", m)
  | Unix.Unix_error (e, op, arg) ->
      ("failure", Printf.sprintf "%s %s: %s" op arg (Unix.error_message e))
  | e -> ("failure", Printexc.to_string e)

let reraise (kind, m) =
  match kind with
  | "invalid_argument" -> invalid_arg m
  | "sys_error" -> raise (Sys_error m)
  | "sexp" -> raise (Sexp.Error m)
  | "tptp" -> raise (Tptp.Error m)
  | _ -> failwith m

let cpu_seconds () =
  let t = Unix.times () in
  t.tms_utime +. t.tms_stime

let children_cpu_seconds () =
  let t = Unix.times () in
  t.tms_cutime +. t.tms_cstime

(* OCaml reports known signals by its own negative numbers; name them. *)
let signal_name n =
  List.assoc_opt n
    [
      (Sys.sigkill, "SIGKILL");
      (Sys.sigterm, "SIGTERM");
      (Sys.sigint, "SIGINT");
      (Sys.sighup, "SIGHUP");
      (Sys.sigsegv, "SIGSEGV");
      (Sys.sigbus, "SIGBUS");
      (Sys.sigabrt, "SIGABRT");
      (Sys.sigfpe, "SIGFPE");
      (Sys.sigill, "SIGILL");
      (Sys.sigpipe, "SIGPIPE");
      (Sys.sigquit, "SIGQUIT");
      (Sys.sigxcpu, "SIGXCPU");
      (Sys.sigusr1, "SIGUSR1");
      (Sys.sigusr2, "SIGUSR2");
      (Sys.sigalrm, "SIGALRM");
    ]
  |> Option.value ~default:(string_of_int n)

let status_text = function
  | Unix.WEXITED n -> "exit " ^ string_of_int n
  | WSIGNALED n -> "signal " ^ signal_name n
  | WSTOPPED n -> "stopped " ^ signal_name n

let stop_signals = [ Sys.sigterm; Sys.sigint; Sys.sighup ]

(* The child of [Unix.fork]: it never returns into the caller's frames. *)
let child_main ~parent ~inherited ~lifeline ~lifeline_grace ~mask ~fd ~hook ~orphaned role body =
  let code =
    try
      ignore (Unix.setsid ());
      (* [inherited] includes the lifeline's write end: once every child has closed its copy,
         the supervisor's is the last one. *)
      List.iter (fun d -> try Unix.close d with Unix.Unix_error _ -> ()) inherited;
      lifeline_start lifeline lifeline_grace;
      let stop = Atomic.make false in
      List.iter
        (fun s -> Sys.set_signal s (Sys.Signal_handle (fun _ -> Atomic.set stop true)))
        stop_signals;
      Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
      ignore (Unix.sigprocmask Unix.SIG_SETMASK mask);
      (* The child inherits the supervisor's whole heap (the input, its parse and every theory
         copy): a worker's memory budget counts only what this process adds from here on. *)
      Telemetry.start_budget_baseline ();
      (* A parent that died without stopping us (SIGKILL) leaves us reparented. Checking every
         1024 polls costs one getppid per 1024 guard calls. *)
      let polls = ref 0 in
      let cancelled () =
        Atomic.get stop
        ||
        (incr polls;
         !polls land 1023 = 0
         && Unix.getppid () <> parent
         &&
         (orphaned ();
          Atomic.set stop true;
          true))
      in
      let announced = ref false in
      let announce () =
        if not !announced then (
          announced := true;
          write_notice fd)
      in
      let message =
        try
          hook role fd;
          body ~cancelled ~announce
        with e -> Failed (describe e)
      in
      (* The work is done; a late stop request must not interrupt the report. *)
      ignore (Unix.sigprocmask Unix.SIG_BLOCK stop_signals);
      (try Process_frame.write fd message
       with Invalid_argument _ | Failure _ ->
         Process_frame.write fd (Failed (describe (Failure "worker report could not be encoded"))));
      0
    with _ -> 2
  in
  Unix._exit code

type child = {
  role : role;
  pid : int;
  fd : Unix.file_descr;
  theory : Theory.t;
  grace : float;
  data : Buffer.t;  (** the report frame, without the notice *)
  mutable received : int;  (** bytes read from the pipe, the notice included *)
  mutable proving : bool;  (** a heuristic worker that sent [proof_notice] *)
  mutable fd_open : bool;
  mutable status : Unix.process_status option;
  mutable killed : bool;
  mutable handled : bool;
}

(* Every child leads its own session and process group, so signalling the group also reaches
   anything the child started. A child that has not yet called setsid gets it directly. Only
   unreaped children are signalled, so their process IDs cannot have been reused. *)
let signal_group c signal =
  if c.status = None then
    try Unix.kill (-c.pid) signal with
    | Unix.Unix_error (Unix.ESRCH, _, _) -> (
        try Unix.kill c.pid signal with Unix.Unix_error _ -> ())
    | Unix.Unix_error _ -> ()

let reap c =
  if c.status = None then
    match Unix.waitpid [ Unix.WNOHANG ] c.pid with
    | 0, _ -> ()
    | _, status -> c.status <- Some status
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> ()
    | exception Unix.Unix_error (Unix.ECHILD, _, _) -> c.status <- Some (Unix.WEXITED 255)

let rec reap_blocking c =
  if c.status = None then
    match Unix.waitpid [] c.pid with
    | _, status -> c.status <- Some status
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> reap_blocking c
    | exception Unix.Unix_error (Unix.ECHILD, _, _) -> c.status <- Some (Unix.WEXITED 255)

let close_fd c =
  if c.fd_open then (
    c.fd_open <- false;
    try Unix.close c.fd with Unix.Unix_error _ -> ())

let chunk = Bytes.create 65536

let read_some c =
  match Unix.read c.fd chunk 0 (Bytes.length chunk) with
  | 0 -> close_fd c
  | n ->
      let notice =
        c.received = 0
        && Bytes.get chunk 0 = proof_notice
        && match c.role with Worker _ -> true | Reference_role -> false
      in
      if notice then c.proving <- true;
      c.received <- c.received + n;
      let skip = if notice then 1 else 0 in
      Buffer.add_subbytes c.data chunk skip (n - skip)
  | exception Unix.Unix_error ((Unix.EINTR | Unix.EAGAIN), _, _) -> ()
  | exception Unix.Unix_error _ -> close_fd c

(* Last resort on every exit path of the supervisor, including its own exceptions. *)
let kill_all children =
  List.iter
    (fun c ->
      signal_group c Sys.sigkill;
      reap_blocking c;
      close_fd c)
    children

let processes ?profile ?(history = []) ?(workers = 1) ?(cancelled = fun () -> false)
    ?(on_instance = fun _ -> ()) ?(timing = default_timing) ?(hook = fun _ _ -> ())
    (config : Scheduler.config) make_theory =
  Scheduler.validate ~workers config;
  (* Every worker's final configuration exists before the first fork. *)
  let configs = Scheduler.worker_configs ~workers config in
  let started = Telemetry.now () and cpu_before = cpu_seconds () in
  let children_cpu_before = children_cpu_seconds () in
  let theories =
    if config.reference_only then [] else List.init workers (fun _ -> make_theory ())
  in
  let reference_theory = if config.reference then Some (make_theory ()) else None in
  let budget =
    List.fold_left max 0.
      ((if theories = [] then []
        else List.map (fun (c : Scheduler.config) -> c.engine.limits.seconds) configs)
      @ if config.reference then [ config.reference_config.seconds ] else [])
  in
  let parent = Unix.getpid () in
  let children = ref [] in
  (* Nobody ever writes to the lifeline; it only reaches end-of-file when the supervisor (the
     holder of the last write end) is gone. *)
  let lifeline, lifeline_wr = Unix.pipe ~cloexec:true () in
  (* An ignored SIGCHLD (inheritable through exec) makes the kernel reap children at once, so
     their IDs could be reused while the supervisor still means to signal them. *)
  let sigchld = Sys.signal Sys.sigchld Sys.Signal_default in
  let checkpoint_dir = Option.map Filename.dirname config.reference_config.checkpoint in
  (* What a reference killed while saving leaves when its supervisor is killed before it can
     reap it: nobody is left to remove it then, so the next run does. *)
  Option.iter (fun dir -> ignore (Sexp.remove_stale_temp_files ~dir : int)) checkpoint_dir;
  let spawn role theory grace body =
    flush_all ();
    let rd, wr = Unix.pipe ~cloexec:true () in
    let inherited =
      rd :: lifeline_wr :: List.map (fun c -> c.fd) (List.filter (fun c -> c.fd_open) !children)
    in
    let orphaned =
      match role with Worker _ -> fun () -> Unix._exit 3 | Reference_role -> ignore
    in
    (* An orphaned worker's result can reach nobody; an orphaned reference that saves a
       checkpoint first gets its stop request and grace. *)
    let lifeline_grace =
      match role with
      | Reference_role when checkpoint_dir <> None ->
          int_of_float (1000. *. Float.max timing.grace timing.reference_grace)
      | _ -> 0
    in
    let mask = Unix.sigprocmask Unix.SIG_BLOCK stop_signals in
    match Unix.fork () with
    | 0 ->
        child_main ~parent ~inherited ~lifeline ~lifeline_grace ~mask ~fd:wr ~hook ~orphaned role
          body
    | pid ->
        (* Recorded first, in spawn order: whatever fails below, [kill_all] still reaps it. *)
        children :=
          !children
          @ [
              {
                role;
                pid;
                fd = rd;
                theory;
                grace;
                data = Buffer.create 4096;
                received = 0;
                proving = false;
                fd_open = true;
                status = None;
                killed = false;
                handled = false;
              };
            ];
        ignore (Unix.sigprocmask Unix.SIG_SETMASK mask);
        Unix.close wr
    | exception e ->
        ignore (Unix.sigprocmask Unix.SIG_SETMASK mask);
        Unix.close rd;
        Unix.close wr;
        raise
          (match e with
          | Failure _ ->
              Invalid_argument "process isolation requires that no Domain has been spawned"
          | e -> e)
  in
  let reports = Hashtbl.create 8 and lost = ref [] and fatal = ref None in
  let verified = Hashtbl.create 2 and reference_message = ref None in
  let stop_at = ref None in
  let begin_stop now =
    if !stop_at = None then (
      stop_at := Some now;
      List.iter (fun c -> signal_group c Sys.sigterm) !children)
  in
  let fail failure = if !fatal = None then fatal := Some failure in
  let lose c why =
    let who =
      match c.role with Worker i -> Printf.sprintf "worker %d" i | Reference_role -> "reference"
    in
    lost := Printf.sprintf "%s lost: %s" who why :: !lost
  in
  let won () =
    Hashtbl.length verified > 0
    ||
    match !reference_message with
    | Some ((r : Reference.report), _, _) -> r.certificate <> None
    | None -> false
  in
  (* Once a proof is verified or a child failed, no further certificate can change the outcome. *)
  let settled () = won () || !fatal <> None in
  (* How long after the stop request a child may run before its group is killed. *)
  let allowed c =
    match c.role with
    | Worker _ when c.proving && not (settled ()) -> Float.max c.grace timing.proof_grace
    | _ -> c.grace
  in
  (* Reads what the children wrote, waiting at most [timeout], and reaps those that exited.
     Returns whether any pipe was readable. *)
  let drain timeout =
    let pending = List.filter (fun c -> c.fd_open) !children in
    let readable =
      match Unix.select (List.map (fun c -> c.fd) pending) [] [] timeout with
      | readable, _, _ ->
          List.iter (fun c -> if List.mem c.fd readable then read_some c) pending;
          readable <> []
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> false
    in
    List.iter reap !children;
    readable
  in
  (* The supervisor's own check is authoritative; an exception counts as a rejection. The
     kernel's guard keeps draining the other children (every 5 ms, up to 1 MiB per pipe; it
     never raises), so none blocks on a full pipe meanwhile, and the grace of every child is
     counted again from the end of the check, so a long check kills no child that is only
     writing its report. *)
  let last_drain = ref neg_infinity in
  let guard () =
    let now = Telemetry.now () in
    if now -. !last_drain >= 0.005 then (
      last_drain := now;
      try
        let rounds = ref 16 in
        while !rounds > 0 && drain 0. do
          decr rounds
        done
      with _ -> ())
  in
  let check theory cert =
    let outcome = try Kernel.check ~guard theory cert with e -> Error (Printexc.to_string e) in
    Option.iter (fun t0 -> stop_at := Some (Float.max t0 (Telemetry.now ()))) !stop_at;
    outcome
  in
  (* A report is parsed once its pipe is closed; the child exits right after writing it. *)
  let handle c =
    c.handled <- true;
    let exit = match c.status with Some s -> status_text s | None -> "closed" in
    let exit = if c.proving then exit ^ ", after announcing a proof" else exit in
    match (Process_frame.unpack (Buffer.contents c.data) : (message, string) result) with
    | _ when Buffer.length c.data = 0 -> lose c ("no report (" ^ exit ^ ")")
    | Error e -> lose c (e ^ " (" ^ exit ^ ")")
    | Ok (Failed (kind, m)) when kind = resource_kind -> lose c (m ^ " (" ^ exit ^ ")")
    | Ok (Failed failure) -> fail failure
    | Ok (Worker_done r) -> (
        match c.role with
        | Worker i when r.id = i -> (
            Hashtbl.replace reports i r;
            match r.certificate with
            | None -> ()
            | Some _ when settled () ->
                (* One verified proof is the result and a failed run raises: later
                   certificates are not re-checked. *)
                ()
            | Some cert -> (
                (* Let the others stop and report while this certificate is checked. *)
                begin_stop (Telemetry.now ());
                let before = Telemetry.now () in
                match check c.theory cert with
                | Ok _ -> Hashtbl.replace verified i (cert, Telemetry.now () -. before)
                | Error e ->
                    (* [Scheduler.run_search] raises unless the worker's own kernel accepted
                       this certificate, so two checks of one proof disagree. *)
                    fail
                      ( "failure",
                        Scheduler.rejected_search_proof
                          (Printf.sprintf "%s (supervisor re-check of worker %d)" e i) )))
        | _ -> lose c "report from the wrong role")
    | Ok (Reference_done (r, cpu, rss)) -> (
        match c.role with
        | Reference_role ->
            let r =
              match r.certificate with
              | None -> r
              | Some _ when settled () -> { r with certificate = None }
              | Some cert -> (
                  begin_stop (Telemetry.now ());
                  let before = Telemetry.now () in
                  match
                    Result.bind (check c.theory cert) (fun _ ->
                        try
                          Ok
                            (match cert.natural with
                            | Some code -> Natural.premises c.theory code
                            | None -> cert.axioms)
                        with e -> Error (Printexc.to_string e))
                  with
                  | Ok axioms -> { r with axioms; replay_seconds = Telemetry.now () -. before }
                  | Error e ->
                      (* [Reference.run_certified] returns only witnesses its kernel accepted. *)
                      fail
                        ( "invalid_argument",
                          Reference.rejected_certified_replay (e ^ " (supervisor re-check)") );
                      { r with certificate = None })
            in
            reference_message := Some (r, cpu, rss)
        | Worker _ -> lose c "report from the wrong role")
  in
  (* [from] is the time of the first fork: each child's budget counts from its own start, and
     building the theory copies before the forks can take seconds on a multi-MiB input. *)
  let supervise ~from () =
    let deadline = from +. budget +. timing.margin in
    let rec loop () =
      let now = Telemetry.now () in
      if !stop_at = None && (cancelled () || settled () || now >= deadline) then begin_stop now;
      (match !stop_at with
      | None -> ()
      | Some t0 ->
          List.iter
            (fun c ->
              if c.status = None && (not c.killed) && now >= t0 +. allowed c then (
                signal_group c Sys.sigkill;
                c.killed <- true)
              else if c.status <> None && now >= t0 +. allowed c +. 1. then
                (* A reaped child can only have its last pipe buffer unread, which the loop
                   drains at once; a pipe still open a second later is held by someone else. *)
                close_fd c)
            !children);
      if List.exists (fun c -> c.fd_open || c.status = None) !children then (
        let wake =
          match !stop_at with
          | None -> deadline -. now
          | Some t0 ->
              List.fold_left
                (fun m c ->
                  if c.status = None && not c.killed then min m (t0 +. allowed c -. now) else m)
                0.01 !children
        in
        ignore (drain (Float.min 0.01 (Float.max 0.0005 wake)) : bool);
        (* Children that finish in the same poll are handled in spawn order: the heuristic
           workers by id, then the reference. The first certificate checked wins, so this is
           the Domain portfolio's preference (lowest heuristic worker, the reference last). *)
        List.iter
          (fun c -> if (not c.fd_open) && c.status <> None && not c.handled then handle c)
          !children;
        loop ())
      else List.iter (fun c -> if not c.handled then handle c) !children
    in
    loop ()
  in
  let release () =
    kill_all !children;
    (* Only the reference writes files (its checkpoint, through temporary files named with its
       process ID); one killed by a signal may have left one behind. *)
    Option.iter
      (fun dir ->
        List.iter
          (fun c ->
            match c.status with
            | Some (Unix.WSIGNALED _) -> ignore (Sexp.remove_temp_files ~dir c.pid : int)
            | _ -> ())
          !children)
      checkpoint_dir;
    (try Unix.close lifeline with Unix.Unix_error _ -> ());
    (try Unix.close lifeline_wr with Unix.Unix_error _ -> ());
    Sys.set_signal Sys.sigchld sigchld
  in
  Fun.protect ~finally:release (fun () ->
      let child_profile = if workers = 1 then Option.map Pipeline_profile.child profile else None in
      let forked = Telemetry.now () in
      List.iteri
        (fun i theory ->
          let config = List.nth configs i in
          spawn (Worker i) theory timing.grace (fun ~cancelled ~announce ->
              let r =
                Scheduler.run_search ?profile:child_profile ~history ~worker_id:i ~workers
                  ~cancelled ~on_instance ~on_proof:announce config theory
              in
              let w = List.hd r.workers in
              Worker_done
                {
                  id = i;
                  certificate = r.certificate;
                  proof_source = r.proof_source;
                  reason = r.reason;
                  axioms = r.axioms;
                  traces = r.traces;
                  cnf_mode = r.cnf_mode;
                  row = Metrics_csv.values w;
                  schema_rows = Metrics_csv.schema_values w;
                  counters = Scheduler.counters r.engine;
                  profile = Option.fold ~none:[] ~some:Pipeline_profile.completed child_profile;
                  cpu_seconds = cpu_seconds ();
                  peak_rss_bytes = Telemetry.peak_rss_bytes ();
                }))
        theories;
      Option.iter
        (fun theory ->
          let grace =
            if config.reference_config.checkpoint = None then timing.grace
            else Float.max timing.grace timing.reference_grace
          in
          spawn Reference_role theory grace (fun ~cancelled ~announce:_ ->
              let r =
                Reference.run_certified ~cancelled ~batch:reference_batch config.reference_config
                  theory
              in
              Reference_done (r, cpu_seconds (), Telemetry.peak_rss_bytes ())))
        reference_theory;
      supervise ~from:forked ());
  let children = !children in
  Option.iter reraise !fatal;
  let stats c cpu rss =
    {
      Scheduler.pid = c.pid;
      exit = (match c.status with Some s -> status_text s | None -> "running");
      cpu_seconds = cpu;
      peak_rss_bytes = rss;
    }
  in
  let remote_workers =
    List.filter_map
      (fun c ->
        match c.role with
        | Reference_role -> None
        | Worker i -> (
            match Hashtbl.find_opt reports i with
            | Some r ->
                Some
                  {
                    Scheduler.remote_id = i;
                    remote_row = Some r.row;
                    remote_schema_rows = r.schema_rows;
                    remote_counters = Some r.counters;
                    remote_reason = r.reason;
                    remote_process = stats c r.cpu_seconds r.peak_rss_bytes;
                  }
            | None ->
                let why =
                  match
                    List.find_opt
                      (fun s -> String.starts_with ~prefix:(Printf.sprintf "worker %d lost: " i) s)
                      !lost
                  with
                  | Some s -> s
                  | None -> Printf.sprintf "worker %d lost" i
                in
                Some
                  {
                    Scheduler.remote_id = i;
                    remote_row = None;
                    remote_schema_rows = [];
                    remote_counters = None;
                    remote_reason = why;
                    remote_process = stats c 0. 0.;
                  }))
      children
  in
  let reference_child = List.find_opt (fun c -> c.role = Reference_role) children in
  let reference_report =
    match (reference_child, !reference_message) with
    | None, _ -> None
    | Some _, Some (r, _, _) -> Some r
    | Some c, None ->
        let reason =
          match List.find_opt (String.starts_with ~prefix:"reference lost: ") !lost with
          | Some s -> s
          | None -> "reference lost"
        in
        ignore c.pid;
        Some
          {
            Reference.certificate = None;
            reason;
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
          }
  in
  let reference_process =
    Option.map
      (fun c ->
        match !reference_message with
        | Some (_, cpu, rss) -> stats c cpu rss
        | None -> stats c 0. 0.)
      reference_child
  in
  (match Hashtbl.find_opt reports 0 with
  | Some r when workers = 1 -> Pipeline_profile.absorb profile r.profile
  | _ -> ());
  let lost = List.rev !lost in
  let engine = Engine.create config.engine in
  Engine.seal engine;
  let winner =
    List.find_map
      (fun i ->
        Option.map (fun (cert, seconds) -> (i, cert, seconds)) (Hashtbl.find_opt verified i))
      (List.init (List.length theories) Fun.id)
  in
  let first = Hashtbl.find_opt reports 0 in
  let join parts = String.concat "; " (List.filter (fun s -> s <> "") parts) in
  let with_lost reason = join (reason :: lost) in
  let base : Scheduler.result =
    {
      certificate = None;
      reason = (match first with Some r -> r.reason | None -> "");
      engine;
      traces = (match first with Some r -> r.traces | None -> []);
      reference_tested = 0;
      replay_seconds = 0.;
      worker_id = (if theories = [] then -1 else 0);
      workers = [];
      wall_seconds = 0.;
      proof_source = "none";
      reference_report;
      axioms = (match first with Some r -> r.axioms | None -> []);
      cnf_mode = (match first with Some r -> r.cnf_mode | None -> config.engine.cnf_mode);
      processes = None;
    }
  in
  let chosen : Scheduler.result =
    match (winner, reference_report) with
    | Some (i, cert, seconds), _ ->
        let r = Hashtbl.find reports i in
        {
          base with
          certificate = Some cert;
          reason = r.reason;
          worker_id = i;
          proof_source = r.proof_source;
          replay_seconds = seconds;
          traces = r.traces;
          axioms = r.axioms;
          cnf_mode = r.cnf_mode;
        }
    | None, Some r when r.certificate <> None ->
        {
          base with
          certificate = r.certificate;
          reason = r.reason;
          worker_id = -1;
          proof_source = "reference";
          replay_seconds = r.replay_seconds;
          axioms = r.axioms;
          cnf_mode = (Option.get r.certificate).cnf_mode;
        }
    | None, Some r when config.reference_only ->
        { base with reason = with_lost r.reason; axioms = r.axioms }
    | None, Some r -> { base with reason = with_lost (join [ base.reason; r.reason ]) }
    | None, None -> { base with reason = with_lost base.reason }
  in
  {
    chosen with
    reference_tested = (match reference_report with None -> 0 | Some r -> r.tested);
    wall_seconds = Telemetry.now () -. started;
    processes =
      Some
        {
          remote_workers;
          reference_process;
          supervisor_cpu_seconds = cpu_seconds () -. cpu_before;
          children_cpu_seconds = children_cpu_seconds () -. children_cpu_before;
          supervisor_peak_rss_bytes = Telemetry.peak_rss_bytes ();
          lost;
        };
  }

let run ?profile ?history ?workers ?cancelled ?on_instance ?(isolation = Domains) config make_theory
    =
  match isolation with
  | Domains ->
      Scheduler.portfolio ?profile ?history ?workers ?cancelled ?on_instance config make_theory
  | Processes -> processes ?profile ?history ?workers ?cancelled ?on_instance config make_theory
