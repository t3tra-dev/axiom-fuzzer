(* The production worker at the end of this module advances the extracted,
   proved frontier. Script/byte enumeration remains an internal regression oracle. *)
open Wire

type config = { seconds : float; max_trials : int; checkpoint : string option }

let default_config = { seconds = 0.1; max_trials = 10000; checkpoint = None }

type t = {
  manifest : Sexp.t;
  theory : Theory.t;
  enumeration : Theory.t;
  streams : (schema * Theory.parameter option Seq.t ref) list;
  mutable stage : int;
  mutable choices : int array;
  mutable bytes : int array;
  mutable tested : int;
  mutable script_tested : int;
  mutable byte_tested : int;
  mutable level : int;
  mutable axioms : axiom list;
  mutable inputs : (int * clause list) list;
  mutable witness : certificate option;
  mutable replay_seconds : float;
}

type report = {
  certificate : certificate option;
  reason : string;
  tested : int;
  trials : int;
  script_tested : int;
  byte_tested : int;
  stage : int;
  seconds : float;
  replay_seconds : float;
  axioms : axiom list;
  resumed : bool;
  peak_domain_words : int;
      (** Largest sampled reading of the reference Domain's own major heap
          ([Telemetry.domain_major_words]), taken every 4096 trials; [-1] when unavailable. *)
}

(* The certified reference keeps only its cursor (a stack of at most
   (stage + 1) * stage tasks of at most stage choices each) and the theory, so
   its live heap is small: alone, the whole process stays near 10 MiB. It
   allocates very fast, though, and what it promotes waits for the end of the
   major cycle of every Domain, so beside large heuristic heaps its reading is
   mostly that garbage. It is sampled, not budgeted: a cap that paused the
   reference cut its ticks sixfold without lowering the reading. *)
let sample_heap peak =
  let words = Telemetry.domain_major_words () in
  if words > !peak then peak := words

let manifest theory =
  let open Sexp in
  let signature = Source.signature (Theory.arena theory) in
  let symbols xs = List (List.map (fun (s, n) -> List [ Atom s; Certificate_io.number n ]) xs) in
  List
    [
      Atom (Theory.name theory);
      Atom (string_of_bool (Signature.is_unrestricted signature));
      symbols (Signature.functions signature);
      symbols (Signature.predicates signature);
      List (List.map Certificate_io.axiom (Theory.fixed theory));
      List (List.map Certificate_io.schema_id (Theory.schemas theory));
    ]

let create theory =
  let enumeration = Theory.copy theory in
  {
    manifest = manifest theory;
    theory = Theory.copy theory;
    enumeration;
    streams = List.map (fun s -> (s, ref (Theory.enumerate enumeration s))) (Theory.schemas theory);
    stage = 1;
    choices = [| 0 |];
    bytes = [||];
    tested = 0;
    script_tested = 0;
    byte_tested = 0;
    level = 0;
    axioms = Theory.fixed theory;
    inputs = [];
    witness = None;
    replay_seconds = 0.;
  }

let increment n = if n = max_int then failwith "reference cursor integer limit" else n + 1

let advance_digits base digits =
  let rec carry i =
    if i < 0 then false
    else if digits.(i) = base - 1 then (
      digits.(i) <- 0;
      carry (i - 1))
    else (
      digits.(i) <- digits.(i) + 1;
      true)
  in
  carry (Array.length digits - 1)

let advance_script (t : t) =
  let length = Array.length t.choices in
  if not (advance_digits (t.stage - length + 1) t.choices) then
    if length < t.stage then t.choices <- Array.make (length + 1) 0
    else (
      t.stage <- increment t.stage;
      t.choices <- [| 0 |])

let advance_bytes t =
  if not (advance_digits 256 t.bytes) then
    t.bytes <- Array.make (increment (Array.length t.bytes)) 0

let checkpoint_text (t : t) =
  let open Sexp in
  let n = Certificate_io.number
  and digits a = List (Array.to_list a |> List.map Certificate_io.number) in
  List
    [
      Atom "axiom-reference";
      Atom "1";
      Atom "script/15:1/hybrid32";
      t.manifest;
      n t.stage;
      digits t.choices;
      digits t.bytes;
      n t.tested;
      n t.script_tested;
      n t.byte_tested;
      (match t.witness with None -> List [] | Some c -> List [ Atom (Certificate_io.encode c) ]);
    ]
  |> to_string

let restore (t : t) text =
  let bad () = invalid_arg "invalid reference checkpoint" in
  let num x = try Certificate_io.int x with Sexp.Error _ -> bad () in
  let digits = function Sexp.List xs -> Array.of_list (List.map num xs) | _ -> bad () in
  match Sexp.parse text with
  | Sexp.List
      [
        Atom "axiom-reference";
        Atom "1";
        Atom "script/15:1/hybrid32";
        m;
        stage;
        choices;
        bytes;
        tested;
        scripts;
        raw;
        witness;
      ] ->
      if m <> t.manifest then invalid_arg "reference checkpoint theory manifest mismatch";
      let stage = num stage and choices = digits choices and bytes = digits bytes in
      let tested = num tested and scripts = num scripts and raw = num raw in
      let length = Array.length choices in
      if
        stage < 1 || length < 1 || length > stage
        || Array.exists (fun i -> i >= stage - length + 1) choices
        || Array.exists (fun i -> i > 255) bytes
        || raw > tested
        || scripts <> tested - raw
        || raw <> tested / 16
      then bad ();
      let witness =
        match witness with
        | Sexp.List [] -> None
        | List [ Atom s ] -> Some (Certificate_io.decode s)
        | _ -> bad ()
      in
      t.stage <- stage;
      t.choices <- choices;
      t.bytes <- bytes;
      t.tested <- tested;
      t.script_tested <- scripts;
      t.byte_tested <- raw;
      t.witness <- witness
  | _ -> bad ()

let ensure_inputs ~guard (t : t) =
  if t.inputs = [] then
    t.inputs <- List.map (fun (a : axiom) -> (a.axiom_id, Kernel.input_clauses ~guard a)) t.axioms;
  while t.level < t.stage do
    guard ();
    List.iter
      (fun (schema, stream) ->
        guard ();
        match Enumerate.with_guard guard !stream with
        | Seq.Nil -> stream := Seq.empty
        | Seq.Cons (None, rest) -> stream := rest
        | Seq.Cons (Some phi, rest) ->
            let id =
              List.fold_left (fun n (a : axiom) -> max n (increment a.axiom_id)) 0 t.axioms
            in
            let ax = Theory.instantiate_parameter t.enumeration ~id schema phi in
            let clauses = Kernel.input_clauses ~guard ax in
            stream := rest;
            t.axioms <- t.axioms @ [ ax ];
            t.inputs <- t.inputs @ [ (id, clauses) ])
      t.streams;
    t.level <- t.level + 1
  done

let script ~guard (t : t) =
  ensure_inputs ~guard t;
  let rec build steps index =
    guard ();
    if index = Array.length t.choices then None
    else
      match Reference_rules.choose ~guard ~inputs:t.inputs ~steps t.choices.(index) with
      | None -> None
      | Some step ->
          let steps = steps @ [ step ] in
          if step.clause = [] then
            let ids =
              List.filter_map
                (fun (s : step) -> match s.rule with Input (a, _) -> Some a | _ -> None)
                steps
            in
            Some
              {
                natural = None;
                avatar = None;
                cnf_mode = Hybrid;
                theory = Theory.name t.theory;
                axioms = List.filter (fun (a : axiom) -> List.mem a.axiom_id ids) t.axioms;
                steps;
                root = step.id;
              }
          else build steps (index + 1)
  in
  build [] 0

let step ?(guard = fun () -> ()) (t : t) =
  guard ();
  if t.tested = max_int then invalid_arg "reference trial counter limit";
  let raw = t.tested mod 16 = 15 in
  let candidate =
    if raw then
      try
        Some
          (Certificate_io.decode
             (String.init (Array.length t.bytes) (fun i -> Char.chr t.bytes.(i))))
      with Sexp.Error _ | Invalid_argument _ -> None
    else script ~guard t
  in
  let found =
    match candidate with
    | None -> None
    | Some cert ->
        let before = Telemetry.now () in
        Fun.protect
          ~finally:(fun () -> t.replay_seconds <- t.replay_seconds +. Telemetry.now () -. before)
          (fun () ->
            match Kernel.check ~guard t.theory cert with Ok _ -> Some cert | Error _ -> None)
  in
  (* Commit only after a complete attempt. Interruption retries this cursor. *)
  if raw then (
    advance_bytes t;
    t.byte_tested <- increment t.byte_tested)
  else (
    advance_script t;
    t.script_tested <- increment t.script_tested);
  t.tested <- increment t.tested;
  t.witness <- found;
  found

exception Stop of string

let process_locks = Hashtbl.create 8
let lock_mutex = Mutex.create ()

let under_mutex f =
  Mutex.lock lock_mutex;
  Fun.protect ~finally:(fun () -> Mutex.unlock lock_mutex) f

let with_checkpoint_lock path f =
  match path with
  | None -> f ()
  | Some path ->
      let key = Filename.concat (Unix.realpath (Filename.dirname path)) (Filename.basename path) in
      under_mutex (fun () ->
          if Hashtbl.mem process_locks key then
            invalid_arg "reference checkpoint is already in use in this process";
          Hashtbl.add process_locks key ());
      Fun.protect
        ~finally:(fun () -> under_mutex (fun () -> Hashtbl.remove process_locks key))
        (fun () ->
          let fd =
            Unix.openfile (path ^ ".lock") [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_CLOEXEC ] 0o600
          in
          Fun.protect
            ~finally:(fun () -> Unix.close fd)
            (fun () ->
              (try Unix.lockf fd Unix.F_TLOCK 0
               with Unix.Unix_error _ ->
                 invalid_arg "reference checkpoint is locked by another process");
              f ()))

let run ?(cancelled = fun () -> false) (config : config) theory =
  if (not (Float.is_finite config.seconds)) || config.seconds < 0. || config.max_trials < 0 then
    invalid_arg "invalid reference budget";
  with_checkpoint_lock config.checkpoint (fun () ->
      let started_ns = Telemetry.now_ns () and t = create theory in
      let started = Float.of_int started_ns *. 1e-9 in
      let deadline = Deadline.create ~now:started_ns config.seconds in
      let resumed =
        match config.checkpoint with
        | Some path when Sys.file_exists path ->
            restore t (Sexp.read_file path);
            true
        | _ -> false
      in
      let initial = t.tested and accepted = ref None and peak = ref (-1) in
      let save () =
        Option.iter (fun p -> Sexp.write_file p (checkpoint_text t)) config.checkpoint
      in
      let guard () =
        if cancelled () then raise (Stop "cancelled after another verified proof or interruption");
        if Deadline.expired deadline then raise (Stop "reference time limit")
      in
      let reason =
        Fun.protect ~finally:save (fun () ->
            try
              (match t.witness with
              | None -> ()
              | Some cert ->
                  guard ();
                  let before = Telemetry.now () in
                  (match Kernel.check ~guard t.theory cert with
                  | Error e -> invalid_arg ("invalid checkpoint witness: " ^ e)
                  | Ok _ -> ());
                  t.replay_seconds <- Telemetry.now () -. before;
                  accepted := Some cert);
              while t.witness = None do
                guard ();
                if t.tested - initial >= config.max_trials then raise (Stop "reference trial limit");
                accepted := step ~guard t;
                if t.tested land 4095 = 0 then sample_heap peak;
                if t.tested mod 1000 = 0 then save ()
              done;
              "reference refutation verified"
            with Stop reason -> reason)
      in
      {
        certificate = !accepted;
        reason;
        tested = t.tested;
        trials = t.tested - initial;
        script_tested = t.script_tested;
        byte_tested = t.byte_tested;
        stage = t.stage;
        seconds = Telemetry.now () -. started;
        replay_seconds = t.replay_seconds;
        axioms =
          (match t.witness with
          | Some { natural = Some code; _ } -> Natural.premises t.theory code
          | Some c -> c.axioms
          | None -> t.axioms);
        resumed;
        peak_domain_words =
          (sample_heap peak;
           !peak);
      })

(** The error raised when the kernel rejects a certified-reference witness (also by the process
    supervisor's re-check of a witness its reference process had accepted). *)
let rejected_certified_replay e = "certified reference replay: " ^ e

(** The production cursor is extracted from Reference.Progress. The older script/byte enumerator
    above remains an internal differential experiment. *)
let run_certified ?(cancelled = fun () -> false) ?(batch = 1) (config : config) theory =
  if (not (Float.is_finite config.seconds)) || config.seconds < 0. || config.max_trials < 0 then
    invalid_arg "invalid reference budget";
  (* [batch] ticks run between two guard checks (cancellation and the clock). Ticks are pure,
     so the cadence changes only how far past the deadline or a stop request the frontier
     advances (at most [batch - 1] ticks). The reference Domain keeps 1; the reference process
     uses a larger batch because clock reads dominate its loop. *)
  if batch < 1 then invalid_arg "invalid reference guard batch";
  let module N = Natural_checker in
  with_checkpoint_lock config.checkpoint (fun () ->
      let started_ns = Telemetry.now_ns () and state = ref N.initial and tested = ref 0 in
      let started = Float.of_int started_ns *. 1e-9 in
      let deadline = Deadline.create ~now:started_ns config.seconds in
      let manifest = manifest theory in
      let checker_theory = Theory.manifest theory in
      let resumed =
        match config.checkpoint with
        | Some path when Sys.file_exists path ->
            let open Sexp in
            (match parse (read_file path) with
            | List [ Atom "certified-frontier"; saved; level; List tasks; count; witness ]
              when saved = manifest ->
                let level = Certificate_io.int level in
                let pending =
                  List.map
                    (function
                      | List [ List prefix; depth ] ->
                          let prefix = List.map Certificate_io.int prefix
                          and depth = Certificate_io.int depth in
                          if
                            depth > level
                            || List.length prefix > level - depth
                            || not (List.for_all (fun n -> n <= level) prefix)
                          then invalid_arg "invalid certified frontier";
                          (prefix, depth)
                      | _ -> invalid_arg "invalid certified frontier")
                    tasks
                in
                let witness =
                  match witness with
                  | List [] -> None
                  | Atom text -> (
                      match (Certificate_io.decode text).natural with
                      | Some code -> Some code
                      | None -> invalid_arg "certified witness must be a natural deduction")
                  | _ -> invalid_arg "invalid certified witness"
                in
                tested := Certificate_io.int count;
                state := { N.level; pending; witness }
            | _ -> invalid_arg "certified checkpoint manifest or algorithm mismatch");
            true
        | _ -> false
      in
      let initial = !tested and accepted = ref None and replay_seconds = ref 0. in
      let peak = ref (-1) in
      let save () =
        Option.iter
          (fun path ->
            let open Sexp in
            let n = Certificate_io.number in
            let text =
              List
                [
                  Atom "certified-frontier";
                  manifest;
                  n !state.level;
                  List
                    (List.map
                       (fun (prefix, depth) -> List [ List (List.map n prefix); n depth ])
                       !state.pending);
                  n !tested;
                  (match !state.witness with
                  | None -> List []
                  | Some code -> Atom (Certificate_io.encode (Natural.certificate theory code)));
                ]
              |> to_string
            in
            write_file path text)
          config.checkpoint
      in
      let guard () =
        if cancelled () then raise (Stop "cancelled after another verified proof or interruption");
        if Deadline.expired deadline then raise (Stop "reference time limit")
      in
      let accept code =
        let certificate = Natural.certificate theory code in
        let before = Telemetry.now () in
        (match Kernel.check ~guard theory certificate with
        | Ok _ -> ()
        | Error e -> invalid_arg (rejected_certified_replay e));
        replay_seconds := !replay_seconds +. Telemetry.now () -. before;
        accepted := Some certificate
      in
      let reason =
        Fun.protect ~finally:save (fun () ->
            try
              guard ();
              Option.iter accept !state.witness;
              while !accepted = None do
                guard ();
                let remaining = ref batch in
                while !remaining > 0 && !accepted = None do
                  decr remaining;
                  if !tested - initial >= config.max_trials then raise (Stop "reference tick limit");
                  if !tested = max_int || !state.level = max_int then
                    raise (Stop "reference machine integer limit");
                  let next = N.tick checker_theory !state in
                  if batch = 1 then guard ();
                  Option.iter accept next.witness;
                  state := next;
                  incr tested;
                  if !tested land 4095 = 0 then sample_heap peak;
                  if !tested mod 1000 = 0 then save ()
                done
              done;
              "certified reference refutation verified"
            with Stop reason -> reason)
      in
      {
        certificate = !accepted;
        reason;
        tested = !tested;
        trials = !tested - initial;
        script_tested = 0;
        byte_tested = 0;
        stage = !state.level;
        seconds = Telemetry.now () -. started;
        replay_seconds = !replay_seconds;
        axioms =
          (match !accepted with
          | Some { natural = Some code; _ } -> Natural.premises theory code
          | _ -> []);
        resumed;
        peak_domain_words =
          (sample_heap peak;
           !peak);
      })
