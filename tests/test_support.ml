open Axiom_fuzzer

let check b message = if not b then failwith message
let equal a b message = check (a = b) message

(* Establish an ordinary-inference fixture without depending on how many
   initial or goal jobs the scheduler chooses first. *)
let select_given (engine : Engine.t) id =
  check (Tbl.Int.mem engine.passive.live id) "fixture selected a non-passive premise";
  Passive.invalidate engine.passive id;
  Engine.protect (fun () -> Engine.select_given engine id)

let rejects f =
  try
    f ();
    false
  with Invalid_argument _ | Sexp.Error _ | Tptp.Error _ -> true

let run tests =
  Printexc.record_backtrace true;
  let failed = ref 0 in
  List.iter
    (fun (name, test) ->
      try
        test ();
        Printf.printf "ok  %s\n%!" name
      with e ->
        incr failed;
        Printf.eprintf "FAIL %s: %s\n%s\n%!" name (Printexc.to_string e) (Printexc.get_backtrace ()))
    tests;
  Printf.printf "%d tests, %d failures\n%!" (List.length tests) !failed;
  if !failed <> 0 then exit 1

let config =
  {
    Scheduler.default_config with
    reference = false;
    max_size = 2;
    max_instances = 32;
    guided = false;
    max_guided_instances = 32;
    guidance = { Guided.default_config with compounds = false; constraints = false };
    (* Suites built on this configuration test one engine per worker. *)
    slices = Some Slices.off;
    engine =
      {
        Engine.default_config with
        avatar = false;
        clause_weight = Passive.Size;
        lookahead = 0;
        ordered = false;
        demodulation = false;
        backward_demodulation = false;
        backward_subsumption = false;
        variants = false;
        limits = { Engine.seconds = 3.; max_given = 150; max_generated = 5000; max_retained = 3000 };
      };
  }

let prove ?(config = config) name =
  let t = Theory.create name in
  let r = Scheduler.run config t in
  match r.certificate with Some c -> (t, c, r) | None -> failwith (name ^ ": " ^ r.reason)

let positive atom : Wire.literal = { positive = true; atom }
let negative atom : Wire.literal = { positive = false; atom }
let v i = Wire.V (0, i)
let constant s = Wire.Fn (Wire.Original s, [])
let p ts = Wire.P ("p", ts)

(* Files of the TPTP Problem Library, verbatim: tests/fixtures/tptp keeps the TPTP layout
   (Problems/DOMAIN/, Axioms/), so that paths and include directives are relative to it, and its
   manifest.json records each file's release and SHA-256. A test reads a file at run time and
   selects or renames its formulas in code; the repository holds no modified TPTP text. A test
   stanza that reads them depends on (source_tree ../fixtures/tptp) and runs one directory below
   tests/. *)
let tptp_fixtures = "../fixtures/tptp"

(* The annotated formulas of the TPTP file [path], in order, each as its name and its tokens (from
   the language word to the closing "."). An include directive stands for the formulas of the
   included file. *)
let rec tptp_formulas path =
  let tokens = Tptp.lex (Sexp.read_file (Filename.concat tptp_fixtures path)) in
  let n = Array.length tokens in
  let unexpected () = failwith (path ^ ": unexpected TPTP statement") in
  (* The "." that ends the statement whose parenthesis depth is [depth] at token [j]. *)
  let rec stop j depth =
    if j >= n then unexpected ()
    else
      match tokens.(j) with
      | Tptp.Op "(" -> stop (j + 1) (depth + 1)
      | Tptp.Op ")" when depth = 1 ->
          if j + 1 < n && tokens.(j + 1) = Tptp.Op "." then j + 1 else unexpected ()
      | Tptp.Op ")" -> stop (j + 1) (depth - 1)
      | _ -> stop (j + 1) depth
  in
  let rec statements i =
    if i >= n then []
    else
      let j = stop i 0 in
      let statement = Array.to_list (Array.sub tokens i (j - i + 1)) in
      let rest = statements (j + 1) in
      match statement with
      | [ Tptp.Name "include"; Tptp.Op "("; Tptp.Quoted included; Tptp.Op ")"; Tptp.Op "." ] ->
          tptp_formulas included @ rest
      | Tptp.Name ("cnf" | "fof") :: Tptp.Op "(" :: (Tptp.Name name | Tptp.Number name) :: _ ->
          (name, statement) :: rest
      | _ -> unexpected ()
  in
  statements 0

(* TPTP text of the formulas of the file [path], include directives expanded: all of them in their
   order, or the ones that [only] names, in its order. [rename] gives a formula the name a test
   uses for it. *)
let tptp_problem ?only ?(rename = []) path =
  let formulas = tptp_formulas path in
  let selected =
    match only with
    | None -> formulas
    | Some names ->
        List.map
          (fun name ->
            match List.assoc_opt name formulas with
            | Some statement -> (name, statement)
            | None -> failwith (path ^ ": no formula " ^ name))
          names
  in
  List.iter
    (fun (name, _) ->
      if not (List.mem_assoc name selected) then failwith (path ^ ": no formula " ^ name))
    rename;
  let text (name, statement) =
    let statement =
      match (List.assoc_opt name rename, statement) with
      | Some name, language :: parenthesis :: _ :: rest ->
          language :: parenthesis :: Tptp.Name name :: rest
      | _ -> statement
    in
    String.concat " "
      (List.map
         (function
           | Tptp.Name s | Tptp.Variable s | Tptp.Number s | Tptp.Op s -> s
           | Tptp.Quoted s -> Tptp.quote s)
         statement)
  in
  String.concat "\n" (List.map text selected)

(* Independent two-element semantics for schema regression witnesses. *)
let sets_model member formula =
  let term env = function
    | Wire.B i -> List.nth env i
    | _ -> failwith "unexpected term in set-model witness"
  in
  let rec eval env = function
    | Wire.Top -> true
    | Bot -> false
    | Pred ("member", [ x; y ]) -> member (term env x) (term env y)
    | Pred _ -> failwith "unexpected predicate in set-model witness"
    | Eq (x, y) -> term env x = term env y
    | Neg f -> not (eval env f)
    | Conj fs -> List.for_all (eval env) fs
    | Disj fs -> List.exists (eval env) fs
    | All f -> List.for_all (fun x -> eval (x :: env) f) [ 0; 1 ]
    | Ex f -> List.exists (fun x -> eval (x :: env) f) [ 0; 1 ]
  in
  eval [] formula
