type sample = { seconds : float; cpu_seconds : float; allocated_words : float }
(** Opt-in, exclusive pipeline measurements. Flush completed stages so a killed process leaves
    useful evidence. A profile belongs to one calling Domain. *)

let sample () =
  {
    seconds = Telemetry.now ();
    cpu_seconds = Sys.time ();
    allocated_words = Telemetry.allocated_words ();
  }

let zero = { seconds = 0.; cpu_seconds = 0.; allocated_words = 0. }

let add a b =
  {
    seconds = a.seconds +. b.seconds;
    cpu_seconds = a.cpu_seconds +. b.cpu_seconds;
    allocated_words = a.allocated_words +. b.allocated_words;
  }

let difference a b =
  {
    seconds = max 0. (a.seconds -. b.seconds);
    cpu_seconds = max 0. (a.cpu_seconds -. b.cpu_seconds);
    allocated_words = max 0. (a.allocated_words -. b.allocated_words);
  }

type t = {
  stream : out_channel;
  costs : (string, sample) Hashtbl.t;
  calls : (string, int) Hashtbl.t;
  mutable current : string option;
  mutable since : sample;
  mutable foreign : sample;
      (** CPU and allocation of stages absorbed from a forked worker process; their wall time is
          already part of this process's wall clock. *)
}

let emit t name event cost calls =
  Printf.fprintf t.stream "%s,%s,%.9f,%.9f,%.0f,%d\n%!" name event cost.seconds cost.cpu_seconds
    cost.allocated_words calls

let cost t name = Option.value ~default:zero (Hashtbl.find_opt t.costs name)

let charge t at =
  Option.iter
    (fun name -> Hashtbl.replace t.costs name (add (cost t name) (difference at t.since)))
    t.current;
  t.since <- at

let stage profile name f =
  match profile with
  | None -> f ()
  | Some t ->
      let previous = t.current in
      charge t (sample ());
      Printf.fprintf t.stream "%s,start,,,,\n%!" name;
      t.current <- Some name;
      t.since <- sample ();
      Fun.protect f ~finally:(fun () ->
          charge t (sample ());
          let calls = 1 + Option.value ~default:0 (Hashtbl.find_opt t.calls name) in
          Hashtbl.replace t.calls name calls;
          emit t name "end" (cost t name) calls;
          t.current <- previous;
          t.since <- sample ())

(* A profile for a forked worker process. It writes to the same stream while the supervisor
   waits without writing, and it starts with empty totals, so [completed] lists only the stages
   the worker ran. *)
let child t =
  {
    t with
    costs = Hashtbl.create 8;
    calls = Hashtbl.create 8;
    current = None;
    since = sample ();
    foreign = zero;
  }

let completed t =
  Hashtbl.fold
    (fun name cost acc ->
      (name, cost, Option.value ~default:0 (Hashtbl.find_opt t.calls name)) :: acc)
    t.costs []

(* Account stages that a forked worker measured (and already wrote) while this process waited in
   its current stage. Their wall time moves out of the current stage, so stages stay exclusive;
   their CPU and allocation belong to the other process and are added to the totals. *)
let absorb profile records =
  Option.iter
    (fun t ->
      List.iter
        (fun (name, (c : sample), calls) ->
          Hashtbl.replace t.costs name (add (cost t name) c);
          Hashtbl.replace t.calls name
            (calls + Option.value ~default:0 (Hashtbl.find_opt t.calls name));
          t.since <- { t.since with seconds = t.since.seconds +. c.seconds };
          t.foreign <- add t.foreign { c with seconds = 0. })
        records)
    profile

let with_file path ~started f =
  if path = "" then f None
  else
    let arguments = difference (sample ()) started in
    let stream = open_out path in
    let t =
      {
        stream;
        costs = Hashtbl.create 24;
        calls = Hashtbl.create 24;
        current = None;
        since = sample ();
        foreign = zero;
      }
    in
    let success = ref false in
    Fun.protect
      ~finally:(fun () ->
        Fun.protect
          ~finally:(fun () -> close_out_noerr stream)
          (fun () ->
            let total = add (difference (sample ()) started) t.foreign in
            let accounted = Hashtbl.fold (fun _ value sum -> add sum value) t.costs zero in
            emit t "unattributed" "end" (difference total accounted) 1;
            emit t "application" (if !success then "complete" else "error") total 1))
      (fun () ->
        output_string stream "phase,event,seconds,cpu_seconds,allocated_words,calls\n";
        Printf.fprintf stream "application,start,,,,\n%!";
        Hashtbl.add t.costs "arguments" arguments;
        emit t "arguments" "end" arguments 1;
        let result = f (Some t) in
        success := true;
        result)
