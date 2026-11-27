type t = Atom of string | List of t list

exception Error of string

(* Largest file [read_file] reads and largest text [parse] accepts by default: 32 MiB. It bounds
   what an input, certificate or checkpoint can make a reader allocate; nesting is bounded
   separately (512 levels). *)
let max_file_bytes = 32 * 1024 * 1024
let atom s = Atom s
let list xs = List xs

let rec output ~char ~string = function
  | Atom s ->
      char '"';
      String.iter
        (function
          | '\\' -> string "\\\\"
          | '"' -> string "\\\""
          | '\n' -> string "\\n"
          | '\r' -> string "\\r"
          | '\t' -> string "\\t"
          | c -> char c)
        s;
      char '"'
  | List xs ->
      char '(';
      List.iteri
        (fun i x ->
          if i > 0 then char ' ';
          output ~char ~string x)
        xs;
      char ')'

let to_string x =
  let buffer = Buffer.create 256 in
  output ~char:(Buffer.add_char buffer) ~string:(Buffer.add_string buffer) x;
  Buffer.contents buffer

let parse ?(max_bytes = max_file_bytes) text =
  let n = String.length text in
  if n > max_bytes then raise (Error "certificate size limit");
  let i = ref 0 in
  let rec white () =
    if !i < n then
      match text.[!i] with
      | ' ' | '\n' | '\r' | '\t' ->
          incr i;
          white ()
      | _ -> ()
  in
  let rec value depth =
    if depth > 512 then raise (Error "S-expression depth limit");
    white ();
    if !i = n then raise (Error "unexpected end of input");
    match text.[!i] with
    | '(' ->
        incr i;
        let rec items acc =
          white ();
          if !i = n then raise (Error "unclosed list");
          if text.[!i] = ')' then (
            incr i;
            List (List.rev acc))
          else
            let x = value (depth + 1) in
            items (x :: acc)
        in
        items []
    | ')' -> raise (Error "unexpected closing parenthesis")
    | '"' ->
        incr i;
        let b = Buffer.create 32 in
        let rec chars () =
          if !i = n then raise (Error "unclosed string");
          let c = text.[!i] in
          incr i;
          if c = '"' then Atom (Buffer.contents b)
          else if c = '\\' then (
            if !i = n then raise (Error "unfinished escape");
            let c =
              match text.[!i] with
              | 'n' -> '\n'
              | 'r' -> '\r'
              | 't' -> '\t'
              | '\\' -> '\\'
              | '"' -> '"'
              | _ -> raise (Error "invalid escape")
            in
            incr i;
            Buffer.add_char b c;
            chars ())
          else (
            Buffer.add_char b c;
            chars ())
        in
        chars ()
    | _ ->
        let start = !i in
        while !i < n && not (List.mem text.[!i] [ '('; ')'; ' '; '\n'; '\r'; '\t' ]) do
          incr i
        done;
        Atom (String.sub text start (!i - start))
  in
  let result = value 0 in
  white ();
  if !i <> n then raise (Error "trailing input");
  result

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () ->
      let n = in_channel_length ic in
      if n > max_file_bytes then raise (Error "file size limit");
      really_input_string ic n)

(* Temporary files carry the writer's process ID, so that whoever reaps a writer killed by a
   signal (the portfolio supervisor, for its reference process) can remove what it left. *)
let temp_prefix pid = Printf.sprintf ".axiom-fuzzer-%d-" pid
let temp_suffix = ".tmp"

(* Removes the temporary files that process [pid] left in [dir]; returns how many. *)
let remove_temp_files ~dir pid =
  let prefix = temp_prefix pid in
  match Sys.readdir dir with
  | exception Sys_error _ -> 0
  | names ->
      Array.fold_left
        (fun n name ->
          if String.starts_with ~prefix name && String.ends_with ~suffix:temp_suffix name then
            match Sys.remove (Filename.concat dir name) with
            | () -> n + 1
            | exception Sys_error _ -> n
          else n)
        0 names

(* The process ID in the name of one of our temporary files; [None] for any other name
   (including the older names without a process ID). *)
let temp_owner name =
  let prefix = ".axiom-fuzzer-" in
  if String.starts_with ~prefix name && String.ends_with ~suffix:temp_suffix name then
    let rest = String.sub name (String.length prefix) (String.length name - String.length prefix) in
    match String.index_opt rest '-' with
    | Some i -> int_of_string_opt (String.sub rest 0 i)
    | None -> None
  else None

(* Removes the temporary files in [dir] whose writer no longer exists (for instance a reference
   killed while saving whose supervisor was killed before it could reap it); returns how many.
   The file of a live process, or of a process ID that is in use again, is kept. *)
let remove_stale_temp_files ~dir =
  let alive pid =
    match Unix.kill pid 0 with
    | () -> true
    | exception Unix.Unix_error (Unix.ESRCH, _, _) -> false
    | exception Unix.Unix_error _ -> true
  in
  match Sys.readdir dir with
  | exception Sys_error _ -> 0
  | names ->
      Array.fold_left
        (fun n name ->
          match temp_owner name with
          | Some pid when pid > 0 && not (alive pid) -> (
              match Sys.remove (Filename.concat dir name) with
              | () -> n + 1
              | exception Sys_error _ -> n)
          | _ -> n)
        0 names

let write_file_with path write =
  (* Write beside the target, then rename: interruption never leaves half a proof. *)
  let dir = Filename.dirname path in
  let temp, oc = Filename.open_temp_file ~temp_dir:dir (temp_prefix (Unix.getpid ())) temp_suffix in
  Fun.protect
    ~finally:(fun () ->
      close_out_noerr oc;
      if Sys.file_exists temp then Sys.remove temp)
    (fun () ->
      write oc;
      output_char oc '\n';
      close_out oc;
      Sys.rename temp path)

let write_file path text = write_file_with path (fun oc -> output_string oc text)
