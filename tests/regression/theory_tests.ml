open Axiom_fuzzer
open Test_support
open Wire

let signature = Signature.make ~functions:[ ("z", 0); ("s", 1) ] ~predicates:[ ("p", 1) ]
let rec numeral n = if n = 0 then App ("z", []) else App ("s", [ numeral (n - 1) ])

(* An integer-parameter schema: P(s^n(z)). Validation recognizes the term
   independently, rather than rebuilding it with the generator. *)
let family ?(name = "numerals") ?(revision = "1") ?guide
    ?(enumerate =
      fun _ bounds ->
        match bounds with
        | None -> Seq.ints 0
        | Some (b : Theory.Schema.bounds) -> List.init b.max_size Fun.id |> List.to_seq)
    ?(expand = fun a n -> Source.pred a "p" [ Wire.import_term a (numeral n) ]) () =
  Theory.Schema.create ?guide ~name ~revision ~encode:string_of_int
    ~decode:(fun data ->
      Option.bind (int_of_string_opt data) (fun n -> if n < 0 then None else Some n))
    ~enumerate ~expand
    ~check:(fun _ n formula ->
      let rec term k = function
        | App ("z", []) -> k = 0
        | App ("s", [ t ]) when k > 0 -> term (k - 1) t
        | _ -> false
      in
      match formula with Pred ("p", [ t ]) -> term n t | _ -> false)
    ()

let base ?(contradiction = false) () =
  Theory.custom ~name:"custom-numerals" signature
    (if contradiction then [ ("counterexample", Neg (Pred ("p", [ numeral 2 ]))) ] else [])

let theory ?(contradiction = false) schema = Theory.register_schema (base ~contradiction ()) schema

let prove_custom ?(cfg = { config with max_size = 3 }) schema =
  let t = theory ~contradiction:true schema in
  let result = Scheduler.run cfg t in
  let cert = match result.certificate with Some c -> c | None -> failwith result.reason in
  check (Result.is_ok (Kernel.check (Theory.copy t) cert)) "custom refutation failed replay";
  (t, cert, result)

module Source_kernel = Kernel_checker.Kernel (struct
  type function_name = string
  type predicate_name = string

  let leb a b = Stdlib.compare a b <= 0
  let equal a b = a = b
end)

let source_fixture () =
  let t =
    Theory.custom ~name:"source-kernel"
      (Signature.make ~functions:[] ~predicates:[])
      [ ("bottom", Bot) ]
  in
  let a = List.hd (Theory.fixed t) in
  let input = { Kernel_checker.original_axiom = a; cnf_hint = DistributiveEvidence } in
  let cert =
    {
      Kernel_checker.certificate_theory = Theory.name t;
      certificate_axioms = [ input ];
      numeric_inputs = [ [] ];
      numeric_proof = [ (Rocq_checker.Input 0, []) ];
    }
  in
  (t, input, cert)

let accepts manifest cert =
  Source_kernel.check
    (fun () -> true)
    max_int 100000
    (fun _ -> 0)
    (fun _ -> None)
    (fun _ -> None)
    manifest cert

let enumerated_atom = Pred ("predicate_0", [ App ("constant_0", []) ])

let enumerated_step = function
  | 2 -> Some enumerated_atom
  | 7 -> Some (Neg enumerated_atom)
  | n when n mod 4 = 3 -> Some (Pred ("predicate_" ^ string_of_int n, []))
  | _ -> None

let enumerated ?(revision = "current") ?(step = enumerated_step) () =
  Theory.of_enumerator ~name:"enumerated-example" ~revision ~step

let prove_enumerated () =
  let t = enumerated () in
  let result = Scheduler.run { config with max_size = 8; reference = false } t in
  let cert = match result.certificate with Some c -> c | None -> failwith result.reason in
  (t, cert)

let natural_enumerated () =
  let module N = Natural_checker in
  let t = enumerated () in
  let premise n f =
    Wire_types.Pair
      ( Number 0,
        N.permission_code
          (N.RegisteredPermission (N.enumeration_name, "current", N.index_text n, f)) )
  in
  let proof =
    N.certificate_code
      {
        assumptions = [ premise 2 enumerated_atom; premise 7 (Neg enumerated_atom) ];
        deduction = N.ImplicationElimination (N.Assume 1, N.Assume 0);
      }
  in
  (t, Natural.certificate t proof)

let tests =
  [
    ( "enumerator observations retain quiet stages and admit new symbols",
      fun () ->
        let t = enumerated () in
        check (Signature.is_unrestricted (Source.signature (Theory.arena t))) "finite vocabulary";
        let schema = List.hd (Theory.schemas t) in
        let slots =
          Theory.enumerate t ~bounds:{ max_size = 8; parameters = 0 } schema
          |> Seq.map Option.is_some |> List.of_seq
        in
        equal slots [ false; false; true; true; false; false; false; true ] "quiet steps filtered";
        let a = Theory.instantiate_enumerated t ~id:42 1000003 in
        check (Theory.validate_axiom t a) "new vocabulary rejected";
        equal a.formula (Pred ("predicate_1000003", [])) "wrong enumeration index";
        List.iter
          (fun n ->
            check
              (rejects (fun () -> ignore (Theory.instantiate_enumerated t ~id:0 n)))
              "quiet or negative index accepted")
          [ -1; 0; 6 ] );
    ( "enumerated axioms search and replay with finite index witnesses",
      fun () ->
        let t, cert = prove_enumerated () in
        check (Result.is_ok (Kernel.check (Theory.copy t) cert)) "enumerated proof rejected";
        equal (Certificate_io.decode (Certificate_io.encode cert)) cert "enumerated cert codec";
        check
          (Result.is_error (Kernel.check (enumerated ~step:(fun _ -> None) ()) cert))
          "certificate supplied its own enumerated axiom";
        check
          (Result.is_error (Kernel.check (enumerated ~revision:"changed" ()) cert))
          "enumeration revision ignored";
        let bad =
          {
            cert with
            axioms =
              List.map
                (fun (a : axiom) ->
                  {
                    a with
                    origin =
                      Registered_instance
                        (Natural_checker.enumeration_name, "current", Natural_checker.index_text 6);
                  })
                cert.axioms;
          }
        in
        check (Result.is_error (Kernel.check t bad)) "forged enumeration index" );
    ( "enumeration index codec rejects overflow and noncanonical witnesses",
      fun () ->
        let module N = Natural_checker in
        List.iter
          (fun n -> equal (N.index_value (N.index_text n)) (Some n) "index codec")
          [ 0; 1; 2; 127; 128; 65536; max_int ];
        let t = enumerated () in
        let ax = Theory.instantiate_enumerated t ~id:0 2 in
        List.iter
          (fun data ->
            check
              (not
                 (Theory.validate_axiom t
                    { ax with origin = Registered_instance (N.enumeration_name, "current", data) }))
              "invalid index accepted")
          [ "0"; "010"; "2"; "-1"; String.make Sys.int_size '1' ] );
    ( "empty enumerations yield slots to other schemas and reference search",
      fun () ->
        let t = enumerated ~step:(fun _ -> None) () in
        let result = Scheduler.run { config with max_size = 4; reference = false } t in
        check (Option.is_none result.certificate) "empty theory refuted";
        let r = Reference.run { Reference.default_config with seconds = 3.; max_trials = 32 } t in
        equal r.tested 32 "quiet steps blocked the reference";
        check (r.script_tested > 0 && r.byte_tested > 0) "reference lane starved";
        let other =
          Theory.Schema.create ~name:"bottom" ~revision:"current"
            ~encode:(fun () -> "unit")
            ~decode:(function "unit" -> Some () | _ -> None)
            ~enumerate:(fun _ _ -> Seq.return ())
            ~expand:(fun a () -> Source.falsity a)
            ~check:(fun _ () f -> f = Bot)
            ()
        in
        let result =
          Scheduler.run
            { config with max_size = 4; reference = false }
            (Theory.register_schema t other)
        in
        check (Option.is_some result.certificate) "quiet stream starved productive schema" );
    ( "enumerated malformed output and signature mismatch are rejected",
      fun () ->
        List.iter
          (fun f ->
            let t = enumerated ~step:(fun _ -> Some f) () in
            check
              (rejects (fun () -> ignore (Theory.instantiate_enumerated t ~id:0 0)))
              "malformed enumerated axiom accepted")
          [
            Pred ("open", [ B 0 ]);
            Pred ("free", [ F 0 ]);
            All (Pred ("negative", [ B (-1) ]));
            Conj [ Bot; Pred ("hidden", [ B 3 ]) ];
          ];
        let t, cert = prove_enumerated () in
        let strict = { (Theory.manifest t) with unrestricted_signature = false } in
        check
          (not (Source_checker.validate_axiom max_int strict (List.hd cert.axioms)))
          "finite signature bypassed" );
    ( "enumerated natural proofs share authority and Source export",
      fun () ->
        let t, cert = natural_enumerated () in
        check (Result.is_ok (Kernel.check t cert)) "natural enumerated proof rejected";
        check (Result.is_ok (Kernel.rocq_document t cert)) "natural enumerated export failed";
        check
          (Result.is_error (Kernel.check (enumerated ~step:(fun _ -> None) ()) cert))
          "natural proof trusted an emitted axiom";
        equal
          (List.map (fun (a : axiom) -> a.formula) (Natural.premises t (Option.get cert.natural)))
          [ enumerated_atom; Neg enumerated_atom ]
          "export lost the original finite premises" );
    ( "enumeration checkpoints preserve quiet-stage positions and signature mode",
      fun () ->
        let t = enumerated ~step:(fun _ -> None) () in
        let first = Reference.create t in
        for _ = 1 to 32 do
          ignore (Reference.step first)
        done;
        let saved = Reference.checkpoint_text first in
        let resumed = Reference.create (Theory.copy t) in
        Reference.restore resumed saved;
        for _ = 1 to 32 do
          ignore (Reference.step first);
          ignore (Reference.step resumed)
        done;
        equal (Reference.checkpoint_text first)
          (Reference.checkpoint_text resumed)
          "quiet-stage cursor";
        equal first.level resumed.level "enumeration level after resume";
        check
          (rejects (fun () ->
               Reference.restore
                 (Reference.create (enumerated ~revision:"changed" ~step:(fun _ -> None) ()))
                 saved))
          "checkpoint accepted a changed enumeration";
        let finite =
          Theory.custom ~name:"universe" (Signature.make ~functions:[] ~predicates:[]) []
        in
        let countable = Theory.custom ~name:"universe" Signature.unrestricted [] in
        check (Reference.manifest finite <> Reference.manifest countable) "signature mode omitted"
    );
    ( "countable signature distinguishes symbol arities",
      fun () ->
        let c = App ("f", []) and fc = App ("f", [ App ("f", []) ]) in
        let t =
          Theory.of_enumerator ~name:"arities" ~revision:"current" ~step:(function
            | 0 -> Some (Eq (c, fc))
            | 1 -> Some (Neg (Eq (c, fc)))
            | _ -> None)
        in
        let result = Scheduler.run { config with max_size = 2; reference = false } t in
        let cert = match result.certificate with Some c -> c | None -> failwith result.reason in
        check (Result.is_ok (Kernel.check t cert)) "same name with different arities rejected" );
    ( "end-to-end kernel checks theory authority before accepting a Source refutation",
      fun () ->
        let t, input, cert = source_fixture () in
        let manifest = Theory.manifest t in
        check (accepts manifest cert) "valid Source proof rejected";
        check
          (not (accepts manifest { cert with certificate_theory = "other" }))
          "theory name ignored";
        check
          (not (accepts { manifest with fixed_axioms = [] } cert))
          "proof supplied its own fixed axiom";
        let registered =
          {
            input with
            original_axiom =
              { input.original_axiom with origin = Registered_instance ("custom", "r", "x") };
          }
        in
        let cert = { cert with certificate_axioms = [ registered ] } in
        let allowing =
          {
            manifest with
            allowed_schemas = [ Registered ("custom", "r") ];
            registered_check = (fun _ _ data f -> data = "x" && f = Bot);
          }
        in
        check (accepts allowing cert) "registered axiom rejected";
        check
          (not (accepts { allowing with allowed_schemas = [] } cert))
          "registry permission bypassed";
        check
          (not (accepts { allowing with registered_check = (fun _ _ _ _ -> false) } cert))
          "registry check bypassed" );
    ( "end-to-end kernel reconstructs Source clauses and checks the whole derivation",
      fun () ->
        let t, input, cert = source_fixture () in
        let manifest = Theory.manifest t in
        let truth = { input.original_axiom with formula = Top } in
        let truth_input = { input with original_axiom = truth } in
        check
          (not
             (accepts
                { manifest with fixed_axioms = [ truth ] }
                { cert with certificate_axioms = [ truth_input ] }))
          "numeric empty clause trusted over true Source";
        check
          (not
             (accepts manifest
                { cert with numeric_inputs = [ [ (true, Rocq_checker.Pred (0, [])) ] ] }))
          "input encoding bypassed";
        check (not (accepts manifest { cert with numeric_proof = [] })) "empty proof accepted";
        check
          (not (accepts manifest { cert with numeric_proof = [ (Rocq_checker.Input 1, []) ] }))
          "invalid proof parent accepted";
        check
          (not
             (accepts manifest
                { cert with certificate_axioms = [ input; input ]; numeric_inputs = [ []; [] ] }))
          "duplicate axiom namespace accepted";
        let bad =
          { input with cnf_hint = DefinitionalEvidence ([], Source_checker.DAux (true, 0, [])) }
        in
        check
          (not (accepts manifest { cert with certificate_axioms = [ bad ] }))
          "unjustified CNF hint accepted" );
    ( "Source authority checks raw scope and signature before simplifying",
      fun () ->
        let t, input, _ = source_fixture () in
        List.iter
          (fun formula ->
            check
              (not (Theory.validate_axiom t { input.original_axiom with formula }))
              "malformed branch hidden by false")
          [
            Conj [ Bot; Eq (B (-1), B (-1)) ];
            Conj [ Bot; Eq (B 0, B 0) ];
            Conj [ Bot; Eq (F 0, F 0) ];
            Conj [ Bot; Pred ("unknown", []) ];
            Conj [ Bot; Eq (App ("unknown", []), App ("unknown", [])) ];
          ];
        check
          (Theory.validate_axiom t { input.original_axiom with formula = Neg (Neg Bot) })
          "valid Boolean equivalence rejected" );
    ( "copied input manifests share immutable data but isolate Source handles",
      fun () ->
        let original = Tptp.parse "cnf(a,axiom,p(X))." in
        let left = Theory.copy original and right = Theory.copy original in
        let initial = Source.counts (Theory.arena original) in
        check (Theory.manifest left == Theory.manifest original) "copy rebuilt the manifest";
        check (Theory.fixed right == Theory.fixed original) "copy rebuilt fixed axioms";
        check
          (Source.signature (Theory.arena left) == Source.signature (Theory.arena right))
          "copy rebuilt the signature";
        let formula = (List.hd (Theory.fixed original)).formula in
        let local = Wire.import (Theory.arena left) formula in
        equal (Wire.export (Theory.arena left) local) formula "copy changed the imported axiom";
        check
          (rejects (fun () -> ignore (Source.view (Theory.arena right) local)))
          "copied theories share Source handles";
        equal (Source.counts (Theory.arena right)) (0, 0) "copy shares mutable arena storage";
        equal (Source.counts (Theory.arena original)) initial "worker mutated the input arena" );
    ( "preserved arenas keep normalization order and remain independently mutable",
      fun () ->
        let imported =
          Tptp.parse
            "fof(a,axiom,![X]:((p(f(X)) & $true) => ?[Y]:(q(X,Y) | X=f(Y)))).\nfof(b,axiom,$false)."
        in
        List.iter
          (fun original ->
            let a = Theory.arena original in
            let initial = Source.counts a in
            let copied = Theory.copy ~preserve_arena:true original in
            let b = Theory.arena copied in
            check (Theory.manifest copied == Theory.manifest original) "manifest was rebuilt";
            equal (Source.counts b) initial "arena population was discarded";
            List.iter
              (fun (axiom : Wire.axiom) ->
                let left = Wire.import a axiom.formula and right = Wire.import b axiom.formula in
                equal (Wire.export a left) (Wire.export b right) "normalization order changed";
                equal (Source.counts a) (Source.counts b) "copied hash-cons IDs drifted";
                check (rejects (fun () -> ignore (Source.view b left))) "source handle was shared";
                check (rejects (fun () -> ignore (Source.view a right))) "copied handle was shared")
              (Theory.fixed original);
            let before = Source.counts a in
            ignore (Source.free b 1000000);
            equal (Source.counts a) before "copy mutated original arena";
            let before = Source.counts b in
            ignore (Source.free a 1000001);
            equal (Source.counts b) before "original mutated copied arena")
          [ Theory.create "zf"; imported ] );
    ( "Source axiom validation is independent of arena allocation",
      fun () ->
        let t = Theory.create "naive" in
        let a = Theory.arena t in
        let phi = Source.not_ a (Source.member a (Source.free a 0) (Source.free a 0)) in
        let ax = Theory.instantiate t ~id:20 Comprehension phi in
        let fresh = Theory.copy t in
        let counts = Source.counts (Theory.arena fresh) in
        for _ = 1 to 100 do
          check (Theory.validate_axiom fresh ax) "raw Source schema rejected"
        done;
        equal (Source.counts (Theory.arena fresh)) counts "validation allocated arena handles" );
    ( "custom and built-in schemas share fair input slots without shadowing",
      fun () ->
        let s =
          Theory.Schema.create ~name:"truth" ~revision:"1"
            ~encode:(fun () -> "")
            ~decode:(fun s -> if s = "" then Some () else None)
            ~enumerate:(fun _ _ -> Seq.return ())
            ~expand:(fun a () -> Source.truth a)
            ~check:(fun _ () f -> f = Top)
            ()
        in
        let t = Theory.register_schema (Theory.create "zf") s in
        let state = Reference.create t in
        Reference.ensure_inputs ~guard:(fun () -> ()) state;
        let instances = List.filter (fun a -> Wire.is_instance a.origin) state.axioms in
        equal (List.length instances) 3 "a schema missed its first input slot";
        check (List.for_all (Theory.validate_axiom t) instances) "mixed registry instance rejected";
        state.stage <- 2;
        Reference.ensure_inputs ~guard:(fun () -> ()) state;
        equal (List.length state.axioms)
          (List.length (Theory.fixed t) + 5)
          "finite custom stream prevented built-in progress" );
    ( "invalid parameter codecs fail before producing an instance",
      fun () ->
        let s =
          Theory.Schema.create ~name:"broken-codec" ~revision:"1" ~encode:string_of_int
            ~decode:(fun _ -> Some 1)
            ~enumerate:(fun _ _ -> Seq.return 0)
            ~expand:(fun a _ -> Source.truth a)
            ~check:(fun _ _ _ -> true)
            ()
        in
        let t = Theory.register_schema (base ()) s in
        check
          (rejects (fun () -> ignore (Theory.instantiate_schema t ~id:0 s 0)))
          "generation accepted noncanonical codec";
        check
          (rejects (fun () -> ignore (Theory.enumerate t (Theory.Schema.key s) ())))
          "enumeration accepted noncanonical codec";
        check
          (rejects (fun () ->
               ignore
                 (Theory.enumerate t ~bounds:{ max_size = -1; parameters = 0 } (Theory.Schema.key s)
                    ())))
          "negative bound accepted" );
    ( "schema registration is local, immutable and revision-bound",
      fun () ->
        let s = family () in
        let original = base () in
        let t = Theory.register_schema original s in
        equal (Theory.schemas original) [] "registration mutated the original manifest";
        equal (Theory.schemas t) [ Theory.Schema.key s ] "registered key missing";
        let ax = Theory.instantiate_schema t ~id:7 s 2 in
        check (Theory.validate_axiom t ax) "registered instance rejected";
        check (Theory.validate_axiom (Theory.copy t) ax) "instance depends on an arena";
        check (not (Theory.validate_axiom original ax)) "unregistered instance accepted";
        check
          (not (Theory.validate_axiom (theory (family ~revision:"2" ())) ax))
          "wrong revision accepted";
        check (rejects (fun () -> ignore (Theory.register_schema t s))) "duplicate name accepted";
        check
          (rejects (fun () -> ignore (Theory.register_schema t (family ~revision:"2" ()))))
          "two revisions shadow one another";
        List.iter
          (fun name ->
            check
              (rejects (fun () -> ignore (Theory.register_schema original (family ~name ()))))
              "reserved/empty schema name accepted")
          [ ""; "separation"; "replacement" ];
        check (rejects (fun () -> ignore (family ~revision:"" ()))) "empty revision accepted";
        check
          (rejects (fun () -> ignore (Theory.instantiate_schema original ~id:0 s 0)))
          "unregistered generation allowed" );
    ( "registered provenance rejects tampering and noncanonical parameters",
      fun () ->
        let s = family () in
        let t = theory s in
        let ax = Theory.instantiate_schema t ~id:7 s 2 in
        List.iter
          (fun bad -> check (not (Theory.validate_axiom t bad)) "tampered instance accepted")
          [
            { ax with axiom_id = -1 };
            { ax with name = "numerals_8" };
            { ax with formula = Bot };
            { ax with formula = Top };
            { ax with formula = Pred ("q", [ numeral 2 ]) };
            { ax with formula = Pred ("p", [ F 0 ]) };
            { ax with formula = Conj [ Bot; Pred ("p", [ B 0 ]) ] };
            { ax with origin = Registered_instance ("numerals", "2", "2") };
            { ax with origin = Registered_instance ("unknown", "1", "2") };
            { ax with origin = Registered_instance ("numerals", "1", "3") };
            { ax with origin = Registered_instance ("numerals", "1", "02") };
            { ax with origin = Registered_instance ("numerals", "1", "-1") };
            { ax with origin = Registered_instance ("numerals", "1", "invalid") };
            { ax with origin = Instance (Theory.Schema.key s, Top) };
          ] );
    ( "schema check does not call or trust the search expansion",
      fun () ->
        let calls = ref 0 in
        let s =
          family
            ~expand:(fun a _ ->
              incr calls;
              Source.falsity a)
            ()
        in
        let t = theory s in
        let wrong = Theory.instantiate_schema t ~id:0 s 2 in
        check (not (Theory.validate_axiom t wrong)) "buggy expansion trusted";
        equal !calls 1 "checker reran the generator";
        let correct = { wrong with formula = Pred ("p", [ numeral 2 ]) } in
        check (Theory.validate_axiom t correct) "independent correct axiom rejected";
        equal !calls 1 "checker called expansion on a valid axiom" );
    ( "registered parameters support multiple formulas and typed codecs",
      fun () ->
        let encode (f, g) =
          Sexp.to_string (Sexp.List [ Certificate_io.source f; Certificate_io.source g ])
        in
        let decode text =
          try
            match Sexp.parse text with
            | Sexp.List [ f; g ] ->
                Some (Certificate_io.decode_source f, Certificate_io.decode_source g)
            | _ -> None
          with Sexp.Error _ -> None
        in
        let s =
          Theory.Schema.create ~name:"pair" ~revision:"1" ~encode ~decode
            ~enumerate:(fun _ _ -> Seq.return (Top, Bot))
            ~expand:(fun a (f, g) -> Source.and_ a [ Wire.import a f; Wire.import a g ])
            ~check:(fun _ (f, g) result ->
              (* This finite example admits only constant formulas. *)
              let constant = function Top -> Some true | Bot -> Some false | _ -> None in
              match (constant f, constant g, constant result) with
              | Some x, Some y, Some z -> z = (x && y)
              | _ -> false)
            ()
        in
        let t = Theory.register_schema (base ()) s in
        List.iter
          (fun (f, g) ->
            let ax = Theory.instantiate_schema t ~id:3 s (f, g) in
            check (Theory.validate_axiom t ax) "tuple parameter did not validate")
          [ (Top, Top); (Top, Bot); (Bot, Top); (Bot, Bot) ];
        let bad = Theory.instantiate_schema t ~id:3 s (Pred ("p", [ numeral 0 ]), Top) in
        check (not (Theory.validate_axiom t bad)) "parameter side condition ignored" );
    ( "registered generation rejects open, foreign and out-of-signature formulas",
      fun () ->
        let foreign = Source.create signature in
        List.iter
          (fun expand ->
            let s = family ~expand () in
            let t = theory s in
            check
              (rejects (fun () -> ignore (Theory.instantiate_schema t ~id:0 s 0)))
              "invalid expansion accepted")
          [
            (fun a _ -> Source.pred a "p" [ Source.free a 0 ]);
            (fun _ _ -> Source.truth foreign);
            (fun a _ -> Source.pred a "unknown" []);
          ] );
    ( "ordinary search and replay handle custom schemas in every CNF mode",
      fun () ->
        List.iter
          (fun cnf_mode ->
            let cfg = { config with max_size = 3; engine = { config.engine with cnf_mode } } in
            let t, cert, result = prove_custom ~cfg (family ()) in
            equal (List.hd result.workers).used_instances 1
              "custom axiom omitted from instance metrics";
            let text = Certificate_io.encode cert in
            equal (Certificate_io.decode text) cert "custom certificate roundtrip failed";
            check
              (Result.is_ok (Kernel.check t (Certificate_io.decode text)))
              "decoded proof rejected";
            check (String.length (Tptp.tstp cert) > 0) "custom TSTP export failed";
            check (Result.is_ok (Kernel.rocq_document t cert)) "custom numeric Rocq export failed";
            let small = Minimizer.run ~config:cfg.engine t cert in
            check
              (Result.is_ok (Kernel.check t small.certificate))
              "custom minimization broke replay")
          [ Distributive; Definitional; Hybrid ] );
    ( "named schema authority is required for certificate replay",
      fun () ->
        let _, cert, _ = prove_custom (family ()) in
        check
          (Result.is_error (Kernel.check (base ~contradiction:true ()) cert))
          "certificate supplied its own authority";
        check
          (Result.is_error
             (Kernel.check (theory ~contradiction:true (family ~revision:"2" ())) cert))
          "proof replay ignored revision" );
    ( "finite and empty registered streams do not stop reference proof enumeration",
      fun () ->
        let empty = family ~name:"empty" ~enumerate:(fun _ _ -> Seq.empty) () in
        let finite = family ~enumerate:(fun _ _ -> List.to_seq [ 0; 1; 2 ]) () in
        let t = theory ~contradiction:true finite |> fun t -> Theory.register_schema t empty in
        let r =
          Reference.run { Reference.default_config with seconds = 3.; max_trials = 10000 } t
        in
        let c = match r.certificate with Some c -> c | None -> failwith r.reason in
        check (Result.is_ok (Kernel.check t c)) "reference custom proof rejected";
        let saved = Reference.create t in
        saved.witness <- Some c;
        let restored = Reference.create (Theory.copy t) in
        Reference.restore restored (Reference.checkpoint_text saved);
        equal restored.witness (Some c) "checkpoint lost registered-schema witness";
        check (r.script_tested > 0 && r.byte_tested > 0) "reference lane starved" );
    ( "checkpoint binds revisions, registration order and deterministic custom streams",
      fun () ->
        let s = family () and other = family ~name:"second" () in
        let t = theory s |> fun t -> Theory.register_schema t other in
        let first = Reference.create t in
        for _ = 1 to 50 do
          ignore (Reference.step first)
        done;
        let saved = Reference.checkpoint_text first in
        let resumed = Reference.create (Theory.copy t) in
        Reference.restore resumed saved;
        for _ = 1 to 50 do
          ignore (Reference.step first);
          ignore (Reference.step resumed)
        done;
        equal (Reference.checkpoint_text first)
          (Reference.checkpoint_text resumed)
          "custom cursor drifted";
        equal first.axioms resumed.axioms "custom input corpus changed after resume";
        List.iter
          (fun changed ->
            check
              (rejects (fun () -> Reference.restore (Reference.create changed) saved))
              "changed registry accepted saved cursor")
          [
            Theory.register_schema (theory (family ~revision:"2" ())) other;
            Theory.register_schema (theory other) s;
            theory s;
          ] );
    ( "registered schemas keep worker arenas separate and support explicit guidance",
      fun () ->
        let s = family () in
        let t = theory ~contradiction:true s in
        let r =
          Scheduler.portfolio ~workers:3 { config with max_size = 3 } (fun () -> Theory.copy t)
        in
        check (Option.is_some r.certificate) "portfolio did not use registered schemas";
        let guided = family ~guide:(fun _ _ -> Some 2) () in
        let cfg = { config with max_instances = 0; guided = true; max_guided_instances = 2 } in
        let _, _, r = prove_custom ~cfg guided in
        check ((List.hd r.workers).guided_used > 0) "custom guidance did not contribute";
        check
          (List.for_all (fun (trace : Scheduler.trace) -> trace.generator = Guided) r.traces)
          "guidance consumed exhaustive slots" );
  ]

let () =
  match Array.to_list Sys.argv with
  | [ _; "--export-rocq"; path ] -> (
      let t, cert, _ = prove_custom (family ~name:"図式\000\"*)" ()) in
      match Kernel.rocq_document t cert with
      | Ok text -> Sexp.write_file path text
      | Error e -> failwith e)
  | [ _; (("--export-enumerated" | "--export-enumerated-natural") as mode); path ] -> (
      let t, cert =
        if mode = "--export-enumerated" then prove_enumerated () else natural_enumerated ()
      in
      match Kernel.rocq_document t cert with
      | Ok text -> Sexp.write_file path text
      | Error e -> failwith e)
  | [ _ ] -> run tests
  | _ -> invalid_arg "theory_tests [--export-rocq FILE]"
