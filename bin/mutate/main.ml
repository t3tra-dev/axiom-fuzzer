open Axiom_fuzzer
open Axiom_cli

let main () =
  let theory = ref "zf" and problem = ref "" and directory = ref "" in
  let count = ref 16 and observations = ref 4 and seconds = ref 1. in
  Arg.parse
    [
      ("--theory", Arg.Set_string theory, "NAME Theory to observe (default zf)");
      ("--problem", Arg.Set_string problem, "FILE Finite original TPTP problem");
      ( "--output-dir",
        Arg.Set_string directory,
        "DIR New directory for mutant problems and certificates" );
      ("--mutations", Arg.Set_int count, "N Maximum mutants (default 16)");
      ( "--observations",
        Arg.Set_int observations,
        "N Finite observation stages per schema (default 4)" );
      ("--seconds", Arg.Set_float seconds, "N Search time per mutant (default 1)");
      Cli.version_option "axiom-mutate";
    ]
    (fun _ -> raise (Arg.Bad "unexpected argument"))
    "axiom-mutate [options] --output-dir DIR";
  if
    !directory = "" || !count < 0 || !observations < 0
    || (not (Float.is_finite !seconds))
    || !seconds < 0.
  then invalid_arg "output directory and finite nonnegative budgets are required";
  let original = if !problem = "" then Theory.create !theory else Tptp.load !problem in
  let snapshot = Mutation.snapshot ~observations:!observations original in
  Unix.mkdir !directory 0o755;
  Cli.write_file (Filename.concat !directory "original.p") (Tptp.problem snapshot);
  let config =
    {
      Scheduler.default_config with
      reference = false;
      max_instances = 0;
      (* One engine per mutant, as before the CLI's single-worker share. *)
      slices = Some Slices.off;
      engine =
        (* Per-mutant searches use finite caps (Engine.attempt_limits) and no memory budget. *)
        {
          Engine.default_config with
          limits = { Engine.attempt_limits with seconds = !seconds };
          budget = Engine.no_budget;
        };
    }
  in
  let rec run i stream =
    if i < !count then
      match stream () with
      | Seq.Nil -> ()
      | Seq.Cons (mutant, rest) ->
          let stem = Filename.concat !directory (Printf.sprintf "mutant-%04d" i) in
          Cli.write_file (stem ^ ".p") mutant.Mutation.problem;
          let variant = Tptp.parse mutant.problem in
          let result = Scheduler.run config variant in
          Option.iter
            (fun cert ->
              let path = stem ^ ".cert" in
              Cli.writing path (fun () -> Certificate_io.write path cert))
            result.certificate;
          Printf.printf "%s axiom=%d operator=%s path=%s result=%s\n%!" stem mutant.axiom_id
            mutant.change.operator
            (String.concat "." (List.map string_of_int mutant.change.path))
            (if Option.is_some result.certificate then "UNSAT" else "UNKNOWN");
          run (i + 1) rest
  in
  run 0 (Mutation.theories snapshot)

let () = Cli.run main
