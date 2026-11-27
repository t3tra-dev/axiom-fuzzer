(* Read-only observation against an independently checked witness. The witness
   never supplies axioms, priorities, or inference choices to the search. *)
open Axiom_fuzzer
open Wire

let rule_name = function
  | Input _ -> "input"
  | Resolve _ -> "resolve"
  | Factor _ -> "factor"
  | Equality_resolve _ -> "equality_resolve"
  | Equality_factor _ -> "equality_factor"
  | Paramodulate _ -> "paramodulate"
  | Component _ -> "component"

(* A diagnostic probe is run after the measured search. It neither supplies
   premises nor changes search priorities. Failure within its bounds is unknown. *)
type occurrence = {
  step : step;
  support : int list;
  mutable stage : string;
  mutable history : string list;
  mutable active : bool;
  mutable retained : bool;
  mutable choice : int list option;
}

let probe rule target parents ~ordered ~selection =
  let calc = Calculus.create ~ordered ~selection (Term.create ()) in
  List.iter (fun o -> Tbl.Int.replace calc.selected o.step.id o.choice) parents;
  let exception Limit in
  let exception Found in
  let deadline = Telemetry.now () +. 0.1 and attempts = ref 0 in
  calc.guard <- (fun () -> if Telemetry.now () >= deadline then raise Limit);
  let emit clause inferred =
    if
      rule_name inferred = rule_name rule && Variant_index.variants (Clause.normalize clause) target
    then raise Found
  in
  let run cursor =
    Seq.iter
      (fun f ->
        incr attempts;
        if !attempts > 4096 then raise Limit;
        f emit)
      cursor
  in
  let result =
    try
      (match (rule, parents) with
      | Resolve _, [ p; q ] -> run (Calculus.resolve_cursor calc p.step q.step)
      | Paramodulate _, [ p; q ] -> run (Calculus.paramodulate_cursor calc p.step q.step)
      | (Factor _ | Equality_resolve _), [ p ] -> Calculus.unary calc p.step emit
      | Equality_factor _, [ p ] -> run (Calculus.equality_factor_cursor calc p.step)
      | _ -> raise Limit);
      "not_found"
    with
    | Found -> "found"
    | Limit -> "probe_limit"
  in
  (result, calc.attempts, calc.ordering_rejected)

let diagnose path engine witness occurrences arrivals events =
  let out = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out out)
    (fun () ->
      output_string out "kind,witness_step,rule,state,parents,attempts,ordering_rejected,detail\n";
      let write xs = output_string out (Metrics_csv.row (List.map Metrics_csv.quote xs)) in
      let reached id =
        List.exists
          (fun stage -> Hashtbl.mem arrivals (id, stage, false))
          [ "derived"; "retained"; "active"; "goal" ]
      in
      let candidates id =
        Option.value ~default:[] (Hashtbl.find_opt occurrences id)
        |> List.filter (fun o -> o.support = [])
        |> List.sort (fun a b ->
            compare
              (not a.active, not a.retained, a.step.id < 0)
              (not b.active, not b.retained, b.step.id < 0))
      in
      let first = ref None in
      List.iter
        (fun (s : step) ->
          List.iter
            (fun o ->
              write
                [
                  "clause";
                  string_of_int s.id;
                  rule_name s.rule;
                  o.stage;
                  string_of_int o.step.id;
                  "";
                  "";
                  Printf.sprintf "active=%b retained=%b conditional=%b" o.active o.retained
                    (o.support <> []);
                ])
            (candidates s.id);
          match s.rule with
          | Input _ -> ()
          | _ ->
              let ids = Wire.parents s.rule in
              let parents = List.filter_map (fun id -> List.nth_opt (candidates id) 0) ids in
              let status, attempts, rejected, detail =
                if reached s.id then ("reached", 0, 0, "")
                else if List.length parents <> List.length ids then
                  ("parent_not_observed", 0, 0, "bounded alpha-variant observation")
                else
                  let actual, a, r =
                    probe s.rule s.clause parents ~ordered:engine.Engine.config.ordered
                      ~selection:true
                  in
                  let lifecycle =
                    String.concat ";"
                      (List.map
                         (fun o ->
                           Printf.sprintf "%d:%s" o.step.id (String.concat "/" (List.rev o.history)))
                         parents)
                  in
                  if actual = "found" then
                    ( (if List.exists (fun o -> (not o.retained) && not o.active) parents then
                         "premise_inactive"
                       else if List.exists (fun o -> not o.active) parents then
                         "ordinary_premise_not_active"
                       else "eligible_not_observed"),
                      a,
                      r,
                      lifecycle )
                  else if actual = "probe_limit" then (actual, a, r, lifecycle)
                  else
                    let maximal, _, _ =
                      probe s.rule s.clause parents ~ordered:engine.config.ordered ~selection:false
                    in
                    if maximal = "found" then ("literal_selection", a, r, lifecycle)
                    else if maximal = "probe_limit" then (maximal, a, r, lifecycle)
                    else
                      let unrestricted, _, _ =
                        probe s.rule s.clause parents ~ordered:false ~selection:false
                      in
                      ( (if unrestricted = "found" then "ordering" else unrestricted),
                        a,
                        r,
                        lifecycle )
              in
              if (not (reached s.id)) && !first = None && List.for_all reached ids then
                first := Some (s.id, status);
              write
                [
                  "edge";
                  string_of_int s.id;
                  rule_name s.rule;
                  status;
                  String.concat ";" (List.map string_of_int ids);
                  string_of_int attempts;
                  string_of_int rejected;
                  detail;
                ])
        witness.steps;
      Hashtbl.to_seq events |> List.of_seq |> List.sort compare
      |> List.iter (fun ((id, phase), n) ->
          write
            [
              "attempts";
              string_of_int id;
              "";
              phase;
              "";
              string_of_int n;
              "";
              "same witness-parent tuple; not necessarily the witness pivot";
            ]);
      Option.iter
        (fun (id, status) ->
          Printf.eprintf "First missing witness edge: %d (%s); diagnostic probes are bounded\n" id
            status)
        !first)

let () =
  let problem = ref ""
  and witness = ref ""
  and output = ref ""
  and diagnostics = ref ""
  and seconds = ref 10. in
  Arg.parse
    [
      ("--problem", Arg.Set_string problem, "FILE Fixed FOF/CNF input (includes expanded)");
      ("--witness", Arg.Set_string witness, "FILE Checked clausal proof to observe");
      ("--seconds", Arg.Set_float seconds, "N Heuristic search deadline");
      ( "--diagnostics",
        Arg.Set_string diagnostics,
        "FILE Lifecycle and first missing proof edge (CSV)" );
      ("--certificate", Arg.Set_string output, "FILE Save a newly discovered checked proof");
    ]
    (fun _ -> raise (Arg.Bad "unexpected argument"))
    "progress_bench";
  if !problem = "" || !witness = "" then invalid_arg "--problem and --witness are required";
  let theory = Tptp.load !problem and witness = Certificate_io.read !witness in
  (match Kernel.check theory witness with Ok _ -> () | Error e -> failwith e);
  if witness.avatar <> None || witness.natural <> None then
    invalid_arg "progress observation currently requires an unconditional clausal witness";
  let targets = Hashtbl.create 32 and arrivals = Hashtbl.create 64 in
  List.iter
    (fun (s : step) ->
      let key = Variant_index.key s.clause in
      Hashtbl.replace targets key (s :: Option.value ~default:[] (Hashtbl.find_opt targets key)))
    witness.steps;
  let occurrences = Hashtbl.create 32
  and by_actual = Hashtbl.create 64
  and events = Hashtbl.create 32 in
  let state = ref None in
  print_endline "witness_step,rule,literals,stage,conditional,found_step,seconds,given";
  let observe stage support (s : step) =
    let e = Option.get !state in
    Option.value ~default:[] (Hashtbl.find_opt targets (Variant_index.key s.clause))
    |> List.iter (fun (wanted : step) ->
        if Variant_index.variants wanted.clause s.clause then (
          let arrival = List.mem stage [ "derived"; "retained"; "active"; "goal" ] in
          let conditional = support <> [] in
          let key = (wanted.id, stage, conditional) in
          if arrival && not (Hashtbl.mem arrivals key) then (
            Hashtbl.add arrivals key ();
            Printf.printf "%d,%s,%d,%s,%b,%d,%.9f,%d\n%!" wanted.id (rule_name wanted.rule)
              (List.length wanted.clause) stage conditional s.id (Engine.elapsed e) e.metrics.given);
          if !diagnostics <> "" then
            let previous = Option.value ~default:[] (Hashtbl.find_opt occurrences wanted.id) in
            let entry = List.find_opt (fun o -> o.step.id = s.id) previous in
            let entry =
              match entry with
              | Some _ -> entry
              | None when arrival && List.length previous < 8 ->
                  let o =
                    {
                      step = s;
                      support;
                      stage;
                      history = [ stage ];
                      active = false;
                      retained = false;
                      choice = Calculus.selected e.calculus s;
                    }
                  in
                  Hashtbl.replace occurrences wanted.id (o :: previous);
                  Hashtbl.replace by_actual s.id
                    (wanted.id :: Option.value ~default:[] (Hashtbl.find_opt by_actual s.id));
                  Some o
              | _ -> None
            in
            Option.iter
              (fun o ->
                if not (List.mem stage o.history) then o.history <- stage :: o.history;
                if s.id < 0 || not (String.starts_with ~prefix:"goal_" stage) then o.stage <- stage;
                o.choice <- (if s.id < 0 then None else Calculus.selected e.calculus s);
                if stage = "active" then o.active <- true;
                if stage = "retained" || stage = "goal" then o.retained <- true;
                if
                  List.mem stage
                    [
                      "inactive";
                      "retired";
                      "locked";
                      "reduced";
                      "goal_forgotten";
                      "goal_evicted";
                      "goal_invalidated";
                    ]
                then (
                  o.active <- false;
                  o.retained <- false))
              entry))
  in
  let on_inference stage rule =
    let parents = Wire.parents rule in
    List.iter
      (fun (wanted : step) ->
        let expected = Wire.parents wanted.rule in
        if
          expected <> []
          && List.length parents = List.length expected
          && List.for_all2
               (fun actual expected ->
                 List.mem expected (Option.value ~default:[] (Hashtbl.find_opt by_actual actual)))
               parents expected
        then
          let key = (wanted.id, stage) in
          Hashtbl.replace events key (1 + Option.value ~default:0 (Hashtbl.find_opt events key)))
      witness.steps
  in
  let engine =
    Engine.create ~on_clause:observe
      ?on_inference:(if !diagnostics = "" then None else Some on_inference)
      {
        Engine.default_config with
        cnf_mode = witness.cnf_mode;
        limits =
          {
            seconds = !seconds;
            max_given = 1000000;
            max_generated = 10000000;
            max_retained = 1000000;
          };
      }
  in
  state := Some engine;
  List.iter (Engine.add_axiom engine) (Theory.fixed theory);
  Engine.finish engine;
  List.iter
    (fun (s : step) ->
      if
        not
          (List.exists
             (fun stage -> Hashtbl.mem arrivals (s.id, stage, false))
             [ "derived"; "retained"; "active"; "goal" ])
      then
        Printf.printf "%d,%s,%d,missing,false,,,\n" s.id (rule_name s.rule) (List.length s.clause))
    witness.steps;
  if !diagnostics <> "" then diagnose !diagnostics engine witness occurrences arrivals events;
  match Engine.certificate engine ~theory:(Theory.name theory) with
  | None ->
      Printf.eprintf "UNKNOWN: %s (heuristic only; observation costs included)\n"
        (Engine.reason engine)
  | Some certificate ->
      (match Kernel.check theory certificate with Ok _ -> () | Error e -> failwith e);
      if !output <> "" then Certificate_io.write !output certificate;
      Printf.eprintf
        "UNSAT: newly discovered proof checked (heuristic only; observation costs included)\n"
