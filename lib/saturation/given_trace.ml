open Wire
(** The selection trace of lean workers (Engine.given_trace), an evaluation diagnostic: one line per
    selection, written by the worker process that selects, so that a port's given clauses can be
    compared with E's effective given clauses (E's -l1 output). It never changes the search. *)

let symbol = function Original f -> f | Skolem (a, i) -> Printf.sprintf "sk%d_%d" a i

(* E-like text: variables X<scope>_<index>, equations "s = t" / "s != t", negation "~". *)
let clause (c : clause) =
  let b = Buffer.create 128 in
  let rec term = function
    | V (s, i) -> Printf.bprintf b "X%d_%d" s i
    | Fn (f, []) -> Buffer.add_string b (symbol f)
    | Fn (f, ts) ->
        Buffer.add_string b (symbol f);
        arguments ts
  and arguments ts =
    Buffer.add_char b '(';
    List.iteri
      (fun i x ->
        if i > 0 then Buffer.add_char b ',';
        term x)
      ts;
    Buffer.add_char b ')'
  in
  let predicate name ts =
    Buffer.add_string b name;
    if ts <> [] then arguments ts
  in
  List.iteri
    (fun i (l : literal) ->
      if i > 0 then Buffer.add_string b " | ";
      match l.atom with
      | E (x, y) ->
          term x;
          Buffer.add_string b (if l.positive then " = " else " != ");
          term y
      | P (p, ts) ->
          if not l.positive then Buffer.add_char b '~';
          predicate p ts
      | D ((a, i), ts) ->
          if not l.positive then Buffer.add_char b '~';
          predicate (Printf.sprintf "def%d_%d" a i) ts)
    c;
  if c = [] then Buffer.add_string b "$false";
  Buffer.contents b

(* A writer for AXIOM_MEASURE_GIVEN_TRACE=<prefix>: every process that writes appends to its own
   file <prefix>.<pid>, opened at its first line (so a forked worker never shares the
   supervisor's channel), and flushes every line (a worker may end by _exit). *)
let writer prefix =
  let channel = ref None in
  fun line ->
    let pid = Unix.getpid () in
    let oc =
      match !channel with
      | Some (owner, oc) when owner = pid -> oc
      | _ ->
          let oc =
            open_out_gen
              [ Open_wronly; Open_append; Open_creat ]
              0o644
              (prefix ^ "." ^ string_of_int pid)
          in
          channel := Some (pid, oc);
          oc
    in
    output_string oc line;
    flush oc
