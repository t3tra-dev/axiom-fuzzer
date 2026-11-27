(* Compare identical atomic candidate coverage, independent of proof-search
   scheduling and instance budgets. Full scan is the former implementation. *)
open Axiom_fuzzer
open Wire

let clauses = ref 1000
and runs = ref 5
and shape = ref "schema"

let () =
  Arg.parse
    [
      ("--clauses", Arg.Set_int clauses, "N Active clauses");
      ("--runs", Arg.Set_int runs, "N Repetitions");
      ("--shape", Arg.Symbol ([ "schema"; "distinct" ], fun s -> shape := s), "SHAPE Clause family");
    ]
    (fun _ -> raise (Arg.Bad "unexpected argument"))
    "guidance_bench";
  if !clauses < 1 || !runs < 1 then invalid_arg "benchmark sizes must be positive";
  let signature =
    Signature.make
      ~functions:
        (if !shape = "schema" then [] else List.init !clauses (fun i -> ("a" ^ string_of_int i, 0)))
      ~predicates:[ ("p", 2) ]
  in
  let steps =
    List.init !clauses (fun id ->
        {
          id;
          rule = Input (id, 0);
          clause =
            (if !shape = "schema" then
               [
                 { positive = true; atom = P ("p", [ V (0, 0); V (0, 0) ]) };
                 { positive = false; atom = P ("p", [ V (0, 0); Fn (Skolem (id, 0), []) ]) };
               ]
             else
               [
                 {
                   positive = true;
                   atom = P ("p", [ V (0, 0); Fn (Original ("a" ^ string_of_int id), []) ]);
                 };
               ]);
        })
  in
  let measured mode =
    Gc.full_major ();
    let arena = Source.create signature in
    let state =
      Guided.create
        ~config:{ Guided.default_config with capacity = 4 * !clauses; clauses_per_cycle = 4 }
        arena
    in
    let active = ref [] and formulas = Hashtbl.create (2 * !clauses) and visited = ref 0 in
    let collect f = Hashtbl.replace formulas f () in
    let drain () =
      let rec loop () =
        match Guided.take state with
        | None -> ()
        | Some f ->
            collect f;
            loop ()
      in
      loop ()
    in
    let flush () =
      match mode with
      | "scan" ->
          visited := !visited + List.length !active;
          List.iter collect (Guided.candidates arena (List.rev !active))
      | _ ->
          Guided.pump state;
          drain ()
    in
    let allocated = Telemetry.allocated_words () and started = Telemetry.now () in
    List.iteri
      (fun i step ->
        if mode = "scan" then active := step :: !active else Guided.observe state step;
        if (i + 1) mod 4 = 0 then flush ())
      steps;
    if !clauses mod 4 <> 0 then flush ();
    let seconds = Telemetry.now () -. started
    and allocated = Telemetry.allocated_words () -. allocated in
    let outputs =
      Hashtbl.to_seq_keys formulas |> List.of_seq
      |> List.map (Wire.export arena)
      |> List.sort compare
    in
    (outputs, seconds, allocated, if mode = "scan" then !visited else state.metrics.processed)
  in
  print_endline "shape,mode,run,clauses,clause_visits,formulas,seconds,allocated_words";
  for run = 0 to !runs - 1 do
    let order = if run mod 2 = 0 then [ "scan"; "incremental" ] else [ "incremental"; "scan" ] in
    let outcomes =
      List.map
        (fun mode ->
          let outputs, seconds, allocated, visits = measured mode in
          Printf.printf "%s,%s,%d,%d,%d,%d,%.9f,%.0f\n%!" !shape mode run !clauses visits
            (List.length outputs) seconds allocated;
          outputs)
        order
    in
    if List.hd outcomes <> List.nth outcomes 1 then failwith "guidance candidate coverage differs"
  done
