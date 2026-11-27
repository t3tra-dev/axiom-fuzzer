(* Conventions shared by the five command-line tools (docs/cli.md): the version, the exit
   statuses and the error format.

   Exit statuses: 0 when the tool did its job, whatever the answer (UNSAT and UNKNOWN for
   axiom-fuzz and axiom-reference); 1 when axiom-replay rejects a certificate; 2 for a usage or
   input error, printed as one "Error: ..." line on standard error (OCaml's Arg module also exits
   with 2 on an unknown option). *)

open Axiom_fuzzer

(* The release, as in axiom-fuzzer.opam (tests/regression/cli_test.py compares them). *)
let version = "0.1.0"
let rejected = 1

(** The [--version] option of the tool [name]. *)
let version_option name =
  ( "--version",
    Arg.Unit
      (fun () ->
        Printf.printf "%s %s\n" name version;
        exit 0),
    " Print the version and exit" )

let error message =
  prerr_endline ("Error: " ^ message);
  exit 2

(** Runs [write], which writes the file [path] through a temporary file beside it that it then
    renames (Sexp.write_file, Certificate_io.write). A failure's Sys_error names the temporary file,
    or no file when the rename fails; the error raised instead names [path]. *)
let writing path write =
  try write ()
  with Sys_error e ->
    let marker = Sexp.temp_suffix ^ ": " in
    let m = String.length marker in
    let rec reason i =
      if i + m > String.length e then e
      else if String.sub e i m = marker then String.sub e (i + m) (String.length e - i - m)
      else reason (i + 1)
    in
    raise (Sys_error (path ^ ": " ^ reason 0))

(** [Sexp.write_file] whose error names [path]. *)
let write_file path text = writing path (fun () -> Sexp.write_file path text)

(** Runs [main]; an error of the input or of the usage becomes one "Error: ..." line on standard
    error and exit status 2. *)
let run main =
  try main () with
  | Unix.Unix_error (e, op, path) ->
      error
        (Printf.sprintf "%s%s: %s" op (if path = "" then "" else " " ^ path) (Unix.error_message e))
  | Invalid_argument e | Failure e | Sys_error e | Sexp.Error e | Tptp.Error e -> error e

(** [reason] without the schema probe lane's counters (" [lane: ...]"), which only --stats prints.
*)
let without_lane_counters reason =
  let marker = " [lane: " in
  let m = String.length marker in
  let rec find s i =
    if i + m > String.length s then None
    else if String.sub s i m = marker then Some i
    else find s (i + 1)
  in
  let rec strip s =
    match find s 0 with
    | None -> s
    | Some i -> (
        match String.index_from_opt s i ']' with
        | None -> String.sub s 0 i
        | Some j -> strip (String.sub s 0 i ^ String.sub s (j + 1) (String.length s - j - 1)))
  in
  strip reason
