open Axiom_fuzzer
open Test_support
open Wire

let rec legacy_text = function
  | Sexp.Atom s ->
      "\""
      ^ String.concat ""
          (List.init (String.length s) (fun i ->
               match s.[i] with
               | '\\' -> "\\\\"
               | '"' -> "\\\""
               | '\n' -> "\\n"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | c -> String.make 1 c))
      ^ "\""
  | List xs -> "(" ^ String.concat " " (List.map legacy_text xs) ^ ")"

(* The preceding wire-format encoder is retained only as a compatibility oracle. *)
let legacy_certificate (c : certificate) =
  let open Certificate_io in
  let open Sexp in
  legacy_text
    (match c.natural with
    | Some proof -> tag "axiom-fuzzer" [ Atom c.theory; tag "natural" [ code proof ] ]
    | None ->
        tag "axiom-fuzzer"
          ([
             Atom c.theory;
             tag "cnf" [ Atom (cnf_mode_name c.cnf_mode) ];
             List (List.map axiom c.axioms);
             List
               (List.map
                  (fun (s : step) -> List [ number s.id; clause s.clause; rule s.rule ])
                  c.steps);
             number c.root;
           ]
          @ List.map avatar (Option.to_list c.avatar)))

let with_temp f =
  let path = Filename.temp_file "axiom-proof-output-" ".cert" in
  Fun.protect
    ~finally:(fun () ->
      List.iter (fun p -> if Sys.file_exists p then Sys.remove p) [ path; path ^ ".lock" ])
    (fun () -> f path)

(* Metrics cells may contain quoted commas and doubled quote characters. *)
let csv_fields text =
  let buffer = Buffer.create 64 and fields = ref [] in
  let push () =
    fields := Buffer.contents buffer :: !fields;
    Buffer.clear buffer
  in
  let finish () =
    push ();
    List.rev !fields
  in
  let length = String.length text in
  let rec start i = if i < length && text.[i] = '"' then quoted (i + 1) else plain i
  and plain i =
    if i = length then finish ()
    else
      match text.[i] with
      | ',' ->
          push ();
          start (i + 1)
      | '"' -> invalid_arg "quote inside unquoted CSV field"
      | c ->
          Buffer.add_char buffer c;
          plain (i + 1)
  and quoted i =
    if i = length then invalid_arg "unterminated CSV field"
    else if text.[i] = '"' then
      if i + 1 < length && text.[i + 1] = '"' then (
        Buffer.add_char buffer '"';
        quoted (i + 2))
      else closed (i + 1)
    else (
      Buffer.add_char buffer text.[i];
      quoted (i + 1))
  and closed i =
    if i = length then finish ()
    else if text.[i] = ',' then (
      push ();
      start (i + 1))
    else invalid_arg "characters after quoted CSV field"
  in
  start 0

let axiom id =
  { axiom_id = id; name = "a" ^ string_of_int id; origin = Imported "test"; formula = Bot }

let empty : certificate =
  {
    natural = None;
    avatar = None;
    cnf_mode = Hybrid;
    theory = "codec\000\"\\\r\n\t日本語";
    axioms = [ axiom 0 ];
    steps = [ { id = 0; clause = []; rule = Input (0, 0) } ];
    root = 0;
  }

let all_rules () =
  let x = V (3, 4) and f = Fn (Original "f\"\\\n", [ V (5, 6) ]) in
  let sigma = [ ((3, 4), f) ] in
  let clause =
    [
      { positive = true; atom = P ("p\000\t", [ x; Fn (Skolem (2, 3), []) ]) };
      { positive = false; atom = E (x, f) };
      { positive = true; atom = D ((2, 1), [ f ]) };
    ]
  in
  {
    empty with
    axioms =
      [
        { (axiom 0) with origin = Fixed "fixed\""; formula = Top };
        {
          (axiom 1) with
          origin = Instance (Separation, Pred ("schema", [ F 0 ]));
          formula = All (Ex (Neg (Conj [ Eq (B 0, App ("g", [ F 1 ])); Disj [ Top; Bot ] ])));
        };
        {
          (axiom 2) with
          origin = Registered_instance ("registered", "r", "payload\n");
          formula = Pred ("p", [ App ("f", []) ]);
        };
      ];
    steps =
      List.mapi
        (fun id rule -> { id; clause; rule })
        [
          Input (0, 0);
          Component 0;
          Resolve (0, 1, 1, 2, sigma);
          Factor (2, 0, 1, sigma);
          Equality_resolve (3, 1, sigma);
          Equality_factor (4, 0, true, 1, false, sigma);
          Paramodulate (5, 0, false, 2, 1, [ 0; 2; 1 ], sigma);
        ];
    root = 6;
  }

let equivalent c =
  let expected = legacy_certificate c in
  equal (Certificate_io.encode c) expected "canonical certificate bytes changed";
  equal (Certificate_io.decode expected) c "certificate roundtrip changed";
  with_temp (fun path ->
      Certificate_io.write path c;
      equal (Sexp.read_file path) (expected ^ "\n") "channel writer changed bytes";
      equal (Certificate_io.read path) c "channel writer changed decoded certificate")

let tests =
  [
    ( "certificate streaming preserves every rule and escaped symbol",
      fun () -> equivalent (all_rules ()) );
    ( "certificate streaming preserves Natural and AVATAR branches",
      fun () ->
        equivalent
          {
            empty with
            natural = Some (Pair (Number 2, Pair (Number 0, Number 3)));
            axioms = [];
            steps = [];
          };
        let c = all_rules () in
        equivalent
          {
            c with
            avatar =
              Some
                {
                  components = [ (List.hd c.steps).clause; [] ];
                  splits = [ (0, [ 0; 1 ]); (5, []) ];
                  boolean_steps =
                    [
                      { boolean_id = 0; boolean_clause = [ 1; -2 ]; boolean_rule = Split 0 };
                      { boolean_id = 1; boolean_clause = [ -1 ]; boolean_rule = Conflict 6 };
                      {
                        boolean_id = 9;
                        boolean_clause = [];
                        boolean_rule = Boolean_resolve (0, 0, 1);
                      };
                    ];
                  boolean_root = 9;
                };
          } );
    ( "large flat certificates and S-expressions serialize without prefix copies",
      fun () ->
        let c =
          {
            empty with
            steps = List.init 20000 (fun i -> { id = i; clause = []; rule = Input (0, i) });
          }
        in
        equivalent c;
        let x = Sexp.List (List.init 100000 (fun _ -> Sexp.Atom "x")) in
        equal (Sexp.parse (Sexp.to_string x)) x "large flat list changed" );
    ( "plain extraction slices a sparse shared DAG once and keeps axiom order",
      fun () ->
        let proof = Proof.create () in
        let add rule = Proof.add proof [] rule in
        ignore (add (Input (2, 0)));
        ignore (add (Input (3, 0)));
        ignore (add (Input (1, 0)));
        ignore (add (Resolve (0, 0, 2, 0, [])));
        ignore (add (Resolve (3, 0, 0, 0, [])));
        ignore (add (Input (3, 0)));
        ignore (Proof.reclaim proof [ 4; 5 ]);
        let c =
          Proof.extract proof ~theory:"sparse" ~axioms:[ axiom 1; axiom 2; axiom 3 ] ~root:4
        in
        equal (List.map (fun (s : step) -> s.id) c.steps) [ 0; 2; 3; 4 ] "wrong ancestor DAG";
        equal (List.map (fun (a : axiom) -> a.axiom_id) c.axioms) [ 1; 2 ] "axiom order changed";
        equal (Proof.prune c) c "extract and prune disagree" );
    ( "plain extraction tolerates long dependency chains and preserves missing-parent failure",
      fun () ->
        let proof = Proof.create () in
        ignore (Proof.add proof [] (Input (0, 0)));
        for id = 1 to 100000 do
          ignore (Proof.add proof [] (Resolve (id - 1, 0, 0, 0, [])))
        done;
        let c = Proof.extract proof ~theory:"structural-chain" ~axioms:[ axiom 0 ] ~root:100000 in
        equal (List.length c.steps) 100001 "dependency chain lost ancestors";
        let dangling = Proof.create () in
        ignore (Proof.add dangling [] (Resolve (2, 0, 3, 0, [])));
        check
          (try
             ignore (Proof.extract dangling ~theory:"dangling" ~axioms:[] ~root:0);
             false
           with Not_found -> true)
          "missing ancestor was silently accepted" );
    ( "used axioms retain definitions and Skolems referenced by AVATAR components",
      fun () ->
        let c =
          {
            empty with
            axioms = [ axiom 9; axiom 3; axiom 0; axiom 2 ];
            avatar =
              Some
                {
                  components =
                    [ [ { positive = true; atom = D ((2, 0), [ Fn (Skolem (3, 0), []) ]) } ] ];
                  splits = [];
                  boolean_steps = [];
                  boolean_root = 0;
                };
          }
        in
        equal
          (List.map (fun (a : axiom) -> a.axiom_id) (Proof.used_axioms c))
          [ 3; 0; 2 ] "auxiliary source axiom was dropped" );
    ( "failed streaming writes retain the previous complete file",
      fun () ->
        with_temp (fun path ->
            Sexp.write_file path "original";
            (try
               Sexp.write_file_with path (fun oc ->
                   output_string oc "incomplete";
                   failwith "writer interruption")
             with Failure _ -> ());
            equal (Sexp.read_file path) "original\n" "partial file replaced prior output") );
    ( "worker metrics reuse the verified certificate after proof storage is released",
      fun () ->
        let theory = Tptp.parse "cnf(yes,axiom,p(a)). cnf(no,axiom,~p(a))." in
        let r = Scheduler.run { config with reference = false } theory in
        let cert = Option.get r.certificate in
        let w = List.hd r.workers in
        check (w.certificate == r.certificate) "worker copied or re-extracted its certificate";
        check (Result.is_ok (Kernel.check theory cert)) "fixture proof rejected";
        let before = Metrics_csv.values w in
        ignore (Proof.reclaim r.engine.proof []);
        let after = Metrics_csv.values w in
        let field name values = List.assoc name (List.combine Metrics_csv.header values) in
        check (w.certificate == r.certificate) "verified snapshot lost after proof reclamation";
        check
          (Result.is_ok (Kernel.check theory (Option.get w.certificate)))
          "retained worker snapshot no longer replays";
        equal (field "proof_steps" before) (field "proof_steps" after) "proof count changed" );
    ( "different workers retain their own proof despite overlapping numeric IDs",
      fun () ->
        let left = Tptp.parse "cnf(yes,axiom,p(a)). cnf(no,axiom,~p(a))." in
        let right =
          Tptp.parse
            "cnf(pp,axiom,(p(a)|q(a))). cnf(np,axiom,(~p(a)|q(a))). cnf(pn,axiom,(p(a)|~q(a))). \
             cnf(nn,axiom,(~p(a)|~q(a)))."
        in
        let r0 = Scheduler.run_search ~worker_id:0 config left
        and r1 = Scheduler.run_search ~worker_id:1 config right in
        let c0 = Option.get r0.certificate and c1 = Option.get r1.certificate in
        check (c0.root <> c1.root) "fixture proofs should differ";
        let w0 = List.hd r0.workers and w1 = List.hd r1.workers in
        check
          (w0.certificate == r0.certificate && w1.certificate == r1.certificate)
          "worker certificate mixed with another worker";
        let combined = { r0 with workers = [ w0; w1 ] } in
        equal
          (csv_fields "\"comma,inside\",\"quote\"\"inside\",,tail,")
          [ "comma,inside"; "quote\"inside"; ""; "tail"; "" ]
          "quoted CSV fields were decoded incorrectly";
        let rows =
          String.split_on_char '\n' (Metrics_csv.workers combined) |> List.map csv_fields
        in
        equal (List.hd rows) Metrics_csv.worker_header "serialized CSV header changed";
        List.iter2
          (fun (w : Scheduler.worker_metrics) values ->
            equal (List.length values)
              (List.length Metrics_csv.worker_header)
              "serialized worker CSV row width differs from header";
            let fields = List.combine Metrics_csv.worker_header values in
            let expected = fst (Proof.statistics (Option.get w.certificate)) in
            equal (List.assoc "proof_steps" fields) (string_of_int expected)
              "another worker's proof affected metrics")
          [ w0; w1 ] (List.tl rows) );
    ( "reference winner does not become a heuristic worker certificate",
      fun () ->
        with_temp (fun checkpoint ->
            let theory = Tptp.parse "fof(bottom,axiom,$false)." in
            let module N = Natural_checker in
            let cert =
              Natural.certificate theory
                (N.certificate_code
                   {
                     assumptions = [ Pair (Number 0, N.permission_code (FixedPermission 0)) ];
                     deduction = Assume 0;
                   })
            in
            check (Result.is_ok (Kernel.check theory cert)) "reference fixture rejected";
            let n = Certificate_io.number in
            Sexp.write_file checkpoint
              (Sexp.to_string
                 (List
                    [
                      Atom "certified-frontier";
                      Reference.manifest theory;
                      n 0;
                      List [];
                      n 0;
                      Atom (Certificate_io.encode cert);
                    ]));
            let r =
              Scheduler.run
                {
                  config with
                  reference = true;
                  reference_config =
                    { Reference.default_config with checkpoint = Some checkpoint; max_trials = 0 };
                  engine =
                    { config.engine with limits = { config.engine.limits with max_generated = 0 } };
                }
                theory
            in
            equal r.certificate (Some cert) "reference proof lost";
            equal r.worker_id (-1) "reference winner incorrectly numbered";
            let w = List.hd r.workers in
            equal w.certificate None "reference certificate attributed to heuristic worker";
            ignore (Metrics_csv.summary ~output_seconds:0. r);
            ignore (Metrics_csv.workers r)) );
  ]

let () = run tests
