open Axiom_fuzzer
open Axiom_cli

let main () =
  let name = ref "naive" and problem = ref "" and output = ref "" and rocq = ref "" in
  let max_stage = ref 2 and unbounded = ref false in
  Arg.parse
    [
      ( "--theory",
        Arg.Set_string name,
        Printf.sprintf "NAME Built-in theory: %s (default naive)" (String.concat ", " Theory.names)
      );
      ("--problem", Arg.Set_string problem, "FILE Original TPTP problem");
      ("--max-stage", Arg.Set_int max_stage, "N Last finite stage (default 2)");
      ( "--unbounded",
        Arg.Set unbounded,
        "Keep increasing the stage until success or a machine resource limit" );
      ("--output", Arg.Set_string output, "FILE Accepted certificate");
      ("--rocq", Arg.Set_string rocq, "FILE Export a checked Source refutation");
      Cli.version_option "axiom-reference";
    ]
    (fun _ -> raise (Arg.Bad "unexpected argument"))
    "axiom-reference [options]";
  if !max_stage < 0 then invalid_arg "negative maximum stage";
  let theory = if !problem = "" then Theory.create !name else Tptp.load !problem in
  let rec search n =
    Printf.printf "reference_stage=%d\n%!" n;
    match Natural.search theory n with
    | Some certificate -> (
        match Kernel.check theory certificate with
        | Error e -> failwith ("reference replay: " ^ e)
        | Ok report ->
            if !output <> "" then
              Cli.writing !output (fun () -> Certificate_io.write !output certificate);
            (if !rocq <> "" then
               match Kernel.rocq_document theory certificate with
               | Ok text -> Cli.write_file !rocq text
               | Error e -> failwith e);
            Printf.printf "VERIFIED: axioms=%d steps=%d\n" report.axioms report.steps)
    | None ->
        if (not !unbounded) && n >= !max_stage then
          print_endline "UNKNOWN: finite reference stage limit"
        else if n = max_int then print_endline "UNKNOWN: reference machine integer limit"
        else search (n + 1)
  in
  search 0

(* A machine resource limit ends the search without an answer: UNKNOWN, as every other
   unanswered search. *)
let () =
  Cli.run (fun () ->
      try main ()
      with Stack_overflow | Out_of_memory ->
        print_endline "UNKNOWN: reference machine resource limit")
