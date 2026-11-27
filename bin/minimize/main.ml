open Axiom_fuzzer
open Axiom_cli

let main () =
  let path = ref "" and output = ref "" and seconds = ref 2. and problem = ref "" in
  let shrink_limit = ref 32 in
  Arg.parse
    [
      ("--output", Arg.Set_string output, "FILE Output certificate");
      ( "--seconds",
        Arg.Set_float seconds,
        "N Budget per axiom deletion, condition shrinking phase, or natural reduction (default 2)"
      );
      ("--problem", Arg.Set_string problem, "FILE Expected original TPTP problem");
      ( "--shrink-conditions",
        Arg.Set_int shrink_limit,
        "N Maximum condition shrink attempts (default 32)" );
      Cli.version_option "axiom-minimize";
    ]
    (fun p -> if !path <> "" then raise (Arg.Bad "one certificate required") else path := p)
    "axiom-minimize FILE --output FILE";
  if !path = "" || !output = "" then invalid_arg "input and --output are required";
  let cert = Certificate_io.read !path in
  if cert.theory = "tptp" && !problem = "" then
    invalid_arg "--problem is required for imported theories";
  let theory = if !problem = "" then Theory.create cert.theory else Tptp.load !problem in
  let config =
    (* Per-attempt searches use finite caps (Engine.attempt_limits) and no memory budget. *)
    {
      Engine.default_config with
      limits = { Engine.attempt_limits with seconds = !seconds };
      budget = Engine.no_budget;
    }
  in
  let result = Minimizer.run ~shrink_limit:!shrink_limit ~config theory cert in
  Cli.writing !output (fun () -> Certificate_io.write !output result.certificate);
  let before_steps, before_axioms = Proof.statistics cert
  and after_steps, after_axioms = Proof.statistics result.certificate in
  Printf.printf "VERIFIED: axioms=%d -> %d steps=%d -> %d reduction_attempts=%d inconclusive=%d\n"
    before_axioms after_axioms before_steps after_steps result.attempts result.inconclusive

let () = Cli.run main
