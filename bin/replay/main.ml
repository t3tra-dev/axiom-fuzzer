open Axiom_fuzzer
open Axiom_cli

let main () =
  let path = ref "" and expected = ref "" and problem = ref "" and rocq = ref "" in
  Arg.parse
    [
      ("--theory", Arg.Set_string expected, "NAME Require this theory manifest");
      ( "--problem",
        Arg.Set_string problem,
        "FILE Expected original TPTP problem (required for imported theories)" );
      ("--rocq", Arg.Set_string rocq, "FILE Export a Rocq Source refutation");
      Cli.version_option "axiom-replay";
    ]
    (fun p -> if !path <> "" then raise (Arg.Bad "one certificate required") else path := p)
    "axiom-replay [options] FILE";
  if !path = "" then invalid_arg "certificate file required";
  let cert = Certificate_io.read !path in
  if !expected <> "" && !problem <> "" then invalid_arg "use either --theory or --problem";
  if cert.theory = "tptp" && !problem = "" then
    invalid_arg "--problem is required: certificate inputs are not their own authority";
  let theory =
    if !problem <> "" then Tptp.load !problem
    else Theory.create (if !expected = "" then cert.theory else !expected)
  in
  match Kernel.check theory cert with
  | Error e ->
      prerr_endline ("REJECTED: " ^ e);
      exit Cli.rejected
  | Ok r ->
      (if !rocq <> "" then
         match Kernel.rocq_document theory cert with
         | Ok text -> Cli.write_file !rocq text
         | Error e -> failwith e);
      Printf.printf "VERIFIED: theory=%s axioms=%d steps=%d replay_seconds=%.6f\n" cert.theory
        r.axioms r.steps r.seconds

let () = Cli.run main
