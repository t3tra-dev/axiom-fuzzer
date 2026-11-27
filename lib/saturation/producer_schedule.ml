(** Ordinary runs the Control step; Goal produces private recipes, and Consumer answers requests
    opened by selected ordinary work. Goal and Consumer never charge Ordinary's lane or operation
    clocks. All three services have equal shares with an eight-turn oldest reservation. This does
    not assert completeness or independent time budgets. *)
type kind = Ordinary | Goal | Consumer

type lane = {
  mutable ready : int;
  mutable selected : int;
  mutable runs : int;
  mutable work : int;
  mutable effort : int;
  mutable milliseconds : int;
  mutable service : float;
  mutable last : int;
}

type t = { lanes : lane array; mutable turns : int }

type snapshot = {
  ready : int;
  selected : int;
  runs : int;
  work : int;
  effort : int;
  milliseconds : int;
  service : float;
  last : int;
}

let index = function Ordinary -> 0 | Goal -> 1 | Consumer -> 2

let create () =
  {
    lanes =
      Array.init 3 (fun _ ->
          ({
             ready = 0;
             selected = 0;
             runs = 0;
             work = 0;
             effort = 0;
             milliseconds = 0;
             service = 0.;
             last = -1;
           }
            : lane));
    turns = 0;
  }

let snapshot t kind : snapshot =
  let lane = t.lanes.(index kind) in
  {
    ready = lane.ready;
    selected = lane.selected;
    runs = lane.runs;
    work = lane.work;
    effort = lane.effort;
    milliseconds = lane.milliseconds;
    service = lane.service;
    last = lane.last;
  }

let turns t = t.turns

let choose t ready =
  (* Keep caller order for ties; repeated readiness is a single observation. *)
  let ready =
    List.fold_left (fun seen kind -> if List.mem kind seen then seen else kind :: seen) [] ready
    |> List.rev
  in
  match ready with
  | [] -> None
  | first :: rest ->
      List.iter
        (fun kind ->
          let lane = t.lanes.(index kind) in
          lane.ready <- lane.ready + 1)
        ready;
      let floor = List.fold_left (fun n k -> min n t.lanes.(index k).service) infinity ready in
      Array.iteri
        (fun i (lane : lane) ->
          if not (List.exists (fun k -> index k = i) ready) then
            lane.service <- max floor lane.service)
        t.lanes;
      let better a b =
        let a = t.lanes.(index a) and b = t.lanes.(index b) in
        if t.turns mod 8 = 7 then a.last < b.last else a.service < b.service
      in
      let kind = List.fold_left (fun best k -> if better k best then k else best) first rest in
      let lane = t.lanes.(index kind) in
      lane.selected <- lane.selected + 1;
      Some kind

let charge t kind ~effort ~seconds =
  let lane = t.lanes.(index kind) and effort = max 0 effort in
  let seconds = if Float.is_nan seconds || seconds < 0. then 0. else min 1000000. seconds in
  let milliseconds = int_of_float (1000. *. seconds) in
  let work = 1 + effort + milliseconds in
  lane.runs <- lane.runs + 1;
  lane.work <- lane.work + work;
  lane.effort <- lane.effort + effort;
  lane.milliseconds <- lane.milliseconds + milliseconds;
  lane.service <- lane.service +. float work;
  lane.last <- t.turns;
  t.turns <- t.turns + 1

(** A dispatched cancellation still spends work. Sampling and charging use only the selected
    service; exceptions from the body propagate after charging. The supplied effort and clock
    readers must be total and non-mutating. *)
let dispatch t ready ~effort ~now f =
  match choose t ready with
  | None -> None
  | Some kind ->
      let before = effort kind and started = now () in
      Fun.protect
        ~finally:(fun () ->
          charge t kind ~effort:(effort kind - before) ~seconds:(now () -. started))
        (fun () -> Some (f kind))

(** Diagnostic observations only. Each stream keeps its initial prefix, not a ring or an unbounded
    history. The sequence clock joins the four streams; it is unrelated to search scheduling. No
    timer is sampled here, although recording has a finite elapsed cost in its caller. *)
module Trace = struct
  let capacity = 256

  type stream = { mutable total : int; counts : int array; prefix : int array array }
  type t = { mutable total : int; control : stream; lane : stream; action : stream; gc : stream }
  type action = Given | Process | Pending | Revisit | Complete | Yield
  type origin = Manual | Ordinary | Producer
  type edge = Begin | End
  type snapshot = { total : int; dropped : int; counts : int array; events : int array array }

  let stream tags = { total = 0; counts = Array.make tags 0; prefix = Array.make capacity [||] }

  let create () =
    { total = 0; control = stream 2; lane = stream 2; action = stream 6; gc = stream 6 }

  let snapshot (stream : stream) =
    let retained = min capacity stream.total in
    {
      total = stream.total;
      dropped = stream.total - retained;
      counts = Array.copy stream.counts;
      events = Array.init retained (fun i -> Array.copy stream.prefix.(i));
    }

  let record (t : t) (stream : stream) tag a b c d e f =
    let sequence = t.total and position = stream.total in
    stream.counts.(tag) <- stream.counts.(tag) + 1;
    stream.total <- position + 1;
    t.total <- sequence + 1;
    if position < capacity then stream.prefix.(position) <- [| sequence; tag; a; b; c; d; e; f |]

  let mask index ready = List.fold_left (fun bits kind -> bits lor (1 lsl index kind)) 0 ready

  let control_select t ~turn ~ready ~selected ~given ~pending ~generated =
    record t t.control 0 turn (mask Control.index ready) (Control.index selected) given pending
      generated

  let control_observe t ~turn ~selected ~gain ~cost ~generated ~stored =
    record t t.control 1 turn (Control.index selected) gain cost generated stored

  let lane_select t ~turn ~ready ~selected ~batch ~demand_runs ~continue_runs =
    let index = Directions.Schedule.index in
    record t t.lane 0 turn (mask index ready) (index selected) batch demand_runs continue_runs

  let lane_charge t ~turn ~selected ~work ~batch ~generated ~attempts =
    record t t.lane 1 turn (Directions.Schedule.index selected) work batch generated attempts

  let action_index = function
    | Given -> 0
    | Process -> 1
    | Pending -> 2
    | Revisit -> 3
    | Complete -> 4
    | Yield -> 5

  let action t kind ~id ~generation ~control_turn ~lane_turn ~producer_turn ~pending =
    record t t.action (action_index kind) id generation control_turn lane_turn producer_turn pending

  let origin_index = function Manual -> 0 | Ordinary -> 1 | Producer -> 2

  let gc t edge ~origin ~control_turn ~producer_turn ~stored ~retained ~pending =
    let origin = origin_index origin in
    let tag = (2 * origin) + match edge with Begin -> 0 | End -> 1 in
    record t t.gc tag origin control_turn producer_turn stored retained pending

  let json (t : t) =
    let buffer = Buffer.create 1024 in
    let array values =
      Buffer.add_char buffer '[';
      Array.iteri
        (fun i value ->
          if i > 0 then Buffer.add_char buffer ',';
          Buffer.add_string buffer (string_of_int value))
        values;
      Buffer.add_char buffer ']'
    in
    let stream name (s : stream) =
      Printf.bprintf buffer ",\"%s\":{\"total\":%d,\"dropped\":%d,\"counts\":" name s.total
        (max 0 (s.total - capacity));
      array s.counts;
      Buffer.add_string buffer ",\"events\":[";
      for i = 0 to min capacity s.total - 1 do
        if i > 0 then Buffer.add_char buffer ',';
        array s.prefix.(i)
      done;
      Buffer.add_string buffer "]}"
    in
    Printf.bprintf buffer "{\"capacity\":%d,\"total\":%d" capacity t.total;
    stream "control" t.control;
    stream "lane" t.lane;
    stream "action" t.action;
    stream "gc" t.gc;
    Buffer.add_char buffer '}';
    Buffer.contents buffer
end
