open Axiom_fuzzer
open Test_support

let guard () = ()
let normalize = List.sort_uniq Int.compare

let make variables =
  let solver = Boolean.create () in
  for expected = 0 to variables - 1 do
    equal (Boolean.new_variable solver) expected "variable IDs are not consecutive"
  done;
  solver

let input solver index clause = Boolean.add_clause solver ~origin:(Boolean.Split index) clause

let satisfies model clauses =
  List.for_all
    (List.exists (fun lit -> if lit > 0 then model.(lit - 1) else not model.(-lit - 1)))
    clauses

let brute variables clauses =
  let rec search mask =
    if mask = 1 lsl variables then false
    else
      let model = Array.init variables (fun v -> mask land (1 lsl v) <> 0) in
      satisfies model clauses || search (mask + 1)
  in
  search 0

(** This checker only reads the public proof. In particular it does not call the solver's
    normalization, resolution, propagation, or analysis helpers. *)
let check_proof solver inputs unsat =
  let proof = Boolean.proof solver in
  equal (Boolean.proof_size solver) (Array.length proof.nodes) "proof size disagrees with DAG";
  let leaves = ref 0 in
  Array.iteri
    (fun index (node : Boolean.proof_node) ->
      equal node.id index "proof ID is not its array position";
      equal node.clause (normalize node.clause) "noncanonical proof clause";
      match node.rule with
      | Boolean.Input origin ->
          let input_index = match origin with Boolean.Split i -> i | Boolean.Conflict i -> i in
          check (input_index >= 0 && input_index < List.length inputs) "unknown input origin";
          equal node.clause (normalize (List.nth inputs input_index)) "input leaf changed";
          incr leaves
      | Boolean.Resolution { left; right; pivot } ->
          check (left >= 0 && right >= 0 && left < index && right < index) "cyclic proof";
          check (pivot > 0) "invalid resolution pivot";
          let a = proof.nodes.(left).clause and b = proof.nodes.(right).clause in
          check
            ((List.mem pivot a && List.mem (-pivot) b) || (List.mem (-pivot) a && List.mem pivot b))
            "resolution lacks complementary pivots";
          let expected = normalize (List.filter (fun lit -> abs lit <> pivot) (a @ b)) in
          equal node.clause expected "resolution silently changed the resolvent")
    proof.nodes;
  equal !leaves (List.length inputs) "an input proof leaf was lost";
  match (unsat, proof.root) with
  | true, Some root ->
      check (root >= 0 && root < Array.length proof.nodes) "unknown proof root";
      equal proof.nodes.(root).clause [] "unsat root is not empty"
  | false, None -> ()
  | _ -> failwith "proof root and solve result disagree"

let verify solver variables clauses =
  let expected = brute variables clauses in
  match Boolean.solve solver ~guard with
  | Boolean.Sat model ->
      check expected "solver returned SAT for an unsatisfiable CNF";
      equal (Array.length model) variables "model has the wrong variable count";
      check (satisfies model clauses) "returned assignment does not satisfy the inputs";
      check_proof solver clauses false
  | Boolean.Unsat ->
      check (not expected) "solver returned UNSAT for a satisfiable CNF";
      check_proof solver clauses true

let instance variables clauses =
  let solver = make variables in
  List.iteri (fun i clause -> ignore (input solver i clause)) clauses;
  verify solver variables clauses;
  solver

let random_clause random variables max_width =
  if variables = 0 then []
  else
    List.init
      (Random.State.int random (max_width + 1))
      (fun _ ->
        let lit = 1 + Random.State.int random variables in
        if Random.State.bool random then lit else -lit)

exception Cancelled of int

let tests =
  [
    ( "Boolean room reserved at creation changes no result, proof or statistic",
      fun () ->
        let rng = Random.State.make [| 59 |] in
        for _ = 1 to 300 do
          let n = 1 + Random.State.int rng 12 in
          let clauses =
            List.init (Random.State.int rng 40) (fun _ ->
                List.init (Random.State.int rng 4) (fun _ ->
                    let v = 1 + Random.State.int rng n in
                    if Random.State.bool rng then v else -v))
          in
          let run solver =
            for _ = 1 to n do
              ignore (Boolean.new_variable solver)
            done;
            (* Solve after every few inputs, so learned clauses and phases carry over. *)
            let results =
              List.mapi
                (fun i c ->
                  ignore (input solver i c);
                  if i mod 5 = 4 then Some (Boolean.solve solver ~guard) else None)
                clauses
            in
            (results, Boolean.solve solver ~guard, Boolean.proof solver, Boolean.statistics solver)
          in
          let plain = run (Boolean.create ())
          and roomy =
            run
              (Boolean.create ~variables:(Random.State.int rng 40) ~nodes:(Random.State.int rng 90)
                 ~clauses:(Random.State.int rng 90) ())
          in
          equal plain roomy "reserved room changed the solver"
        done );
    ( "Boolean empty problem, empty clause, opposite units, and root implication conflict",
      fun () ->
        List.iter
          (fun (variables, clauses) -> ignore (instance variables clauses))
          [
            (0, []);
            (0, [ [] ]);
            (4, []);
            (2, [ [ 1 ]; [ -1 ] ]);
            (3, [ [ 1 ]; [ -1; 2 ]; [ -2; 3 ]; [ -3 ] ]);
            (3, [ [ 1 ]; [ 1 ]; [ -1; 2 ]; [ -2; 3 ] ]);
          ] );
    ( "Boolean input leaves preserve tautologies, origins, and duplicate normalization",
      fun () ->
        let solver = make 2 in
        let clauses = [ [ 1; -1; 2; 1 ]; [ 2; 2 ]; [ -2; -2 ] ] in
        equal (input solver 0 (List.nth clauses 0)) 0 "first leaf ID changed";
        equal
          (Boolean.add_clause solver ~origin:(Boolean.Conflict 1) (List.nth clauses 1))
          1 "second leaf ID changed";
        let before = Boolean.proof solver in
        equal before.nodes.(1).rule (Boolean.Input (Boolean.Conflict 1)) "FO origin lost";
        verify solver 2 (List.filteri (fun i _ -> i < 2) clauses);
        ignore (input solver 2 (List.nth clauses 2));
        verify solver 2 clauses );
    ( "Boolean rejects zero and unallocated literals without changing proof state",
      fun () ->
        let solver = make 2 in
        List.iter
          (fun clause ->
            check (rejects (fun () -> ignore (input solver 0 clause))) "invalid literal accepted")
          [ [ 0 ]; [ 3 ]; [ -3 ]; [ min_int ]; [ 1; 0 ] ];
        equal (Array.length (Boolean.proof solver).nodes) 0 "invalid input left a proof leaf";
        verify solver 2 [] );
    ( "Boolean first-UIP learning jumps over an unrelated decision",
      fun () ->
        let solver = instance 5 [ [ 1; 3; 4 ]; [ 1; 3; -4 ]; [ 2; 5 ] ] in
        let stats = Boolean.statistics solver in
        check (stats.learned_clauses > 0) "conflict did not produce a learned clause";
        check (stats.nonchronological_backjumps > 0) "unrelated decision was not skipped" );
    ( "Boolean variable capacity growth preserves watches and previously learned reasons",
      fun () ->
        let clauses = [ [ 1; 3; 4 ]; [ 1; 3; -4 ]; [ 2; 5 ] ] in
        let solver = instance 5 clauses in
        let learned = (Boolean.statistics solver).learned_clauses in
        for v = 5 to 33 do
          equal (Boolean.new_variable solver) v "variable capacity growth changed IDs"
        done;
        ignore (input solver 3 [ 34 ]);
        let clauses = clauses @ [ [ 34 ] ] in
        (match Boolean.solve solver ~guard with
        | Boolean.Unsat -> failwith "variable growth made a satisfiable CNF unsatisfiable"
        | Boolean.Sat model ->
            equal (Array.length model) 34 "capacity leaked into model size";
            check (satisfies model clauses) "variable growth lost a clause");
        check ((Boolean.statistics solver).learned_clauses >= learned) "learned state was reset";
        check_proof solver clauses false;
        ignore (input solver 4 [ -34 ]);
        equal (Boolean.solve solver ~guard) Boolean.Unsat "new opposite unit was ignored";
        check_proof solver (clauses @ [ [ -34 ] ]) true );
    ( "Boolean pigeonhole refutations use independently checked learned resolution chains",
      fun () ->
        let pigeons = 5 and holes = 4 in
        let lit pigeon hole = 1 + (pigeon * holes) + hole in
        let clauses = ref (List.init pigeons (fun p -> List.init holes (lit p))) in
        for h = 0 to holes - 1 do
          for p = 0 to pigeons - 1 do
            for q = p + 1 to pigeons - 1 do
              clauses := [ -lit p h; -lit q h ] :: !clauses
            done
          done
        done;
        let solver = make (pigeons * holes) in
        List.iteri (fun i cl -> ignore (input solver i cl)) !clauses;
        equal (Boolean.solve solver ~guard) Boolean.Unsat "pigeonhole instance was satisfiable";
        check
          ((Boolean.statistics solver).learned_clauses > 1)
          "multi-conflict learning was not exercised";
        check_proof solver !clauses true );
    ( "Boolean all CNFs over two variables agree with exhaustive assignments",
      fun () ->
        let clauses =
          Array.init 9 (fun code ->
              let literal digit v = if digit = 0 then [] else [ (if digit = 1 then v else -v) ] in
              literal (code mod 3) 1 @ literal (code / 3) 2)
        in
        for mask = 0 to (1 lsl Array.length clauses) - 1 do
          let selected = ref [] in
          Array.iteri
            (fun i cl -> if mask land (1 lsl i) <> 0 then selected := cl :: !selected)
            clauses;
          ignore (instance 2 !selected)
        done );
    ( "Boolean random small CNFs and every resolution step agree with independent checks",
      fun () ->
        let random = Random.State.make [| 0x415641; 0x4344434c |] in
        for trial = 0 to 5999 do
          let variables = if trial mod 13 = 0 then 0 else 1 + Random.State.int random 7 in
          let count = Random.State.int random 35 in
          let clauses =
            List.init count (fun _ ->
                if trial mod 3 = 0 then random_clause random variables 5
                else if variables = 0 then []
                else
                  List.init
                    (2 + Random.State.int random 2)
                    (fun _ ->
                      let lit = 1 + Random.State.int random variables in
                      if Random.State.bool random then lit else -lit))
          in
          ignore (instance variables clauses)
        done );
    ( "Boolean incremental additions, variable growth, and repeated solve preserve learned clauses",
      fun () ->
        let random = Random.State.make [| 0x494e43 |] in
        for _ = 0 to 499 do
          let solver = make 1 in
          let variables = ref 1 and clauses = ref [] in
          for step = 0 to 11 do
            if !variables < 7 && step mod 2 = 0 then (
              equal (Boolean.new_variable solver) !variables "incremental variable ID changed";
              incr variables);
            let clause = random_clause random !variables 5 in
            ignore (input solver (List.length !clauses) clause);
            clauses := !clauses @ [ clause ];
            verify solver !variables !clauses;
            if step mod 3 = 0 then verify solver !variables !clauses
          done
        done );
    ( "Boolean cancellation at every guard boundary allows sound retry and later input",
      fun () ->
        let clauses =
          [
            [ 1; 3; 4 ];
            [ 1; 3; -4 ];
            [ 2; 5 ];
            [ -1; 6; 7 ];
            [ -6; 7 ];
            [ 1; -3; 6 ];
            [ -4; -5; -7 ];
          ]
        in
        let probe = make 7 in
        List.iteri (fun i cl -> ignore (input probe i cl)) clauses;
        let calls = ref 0 in
        ignore (Boolean.solve probe ~guard:(fun () -> incr calls));
        for stop = 1 to !calls do
          let solver = make 7 in
          List.iteri (fun i cl -> ignore (input solver i cl)) clauses;
          let count = ref 0 in
          let raised =
            try
              ignore
                (Boolean.solve solver ~guard:(fun () ->
                     incr count;
                     if !count = stop then raise (Cancelled stop)));
              false
            with Cancelled payload ->
              equal payload stop "guard exception payload changed";
              true
          in
          check raised "guard exception swallowed";
          verify solver 7 clauses;
          ignore (input solver (List.length clauses) []);
          verify solver 7 (clauses @ [ [] ])
        done );
    ( "Boolean cancellation during root proof construction can be retried",
      fun () ->
        let clauses = [ [ 1 ]; [ -1; 2 ]; [ -2; 3 ]; [ -3; 4 ]; [ -4 ] ] in
        for stop = 1 to 70 do
          let solver = make 4 in
          List.iteri (fun i cl -> ignore (input solver i cl)) clauses;
          let count = ref 0 in
          (try
             ignore
               (Boolean.solve solver ~guard:(fun () ->
                    incr count;
                    if !count = stop then raise (Cancelled stop)))
           with Cancelled _ -> ());
          verify solver 4 clauses
        done );
    ( "Boolean interrupted watch repair tolerates another cancellation and a new clause",
      fun () ->
        let clauses = [ [ 1; 2; 3 ]; [ -1; 4 ]; [ -2; 5 ]; [ -3; -4; -5 ] ] in
        let solver = make 5 in
        List.iteri (fun i cl -> ignore (input solver i cl)) clauses;
        List.iter
          (fun limit ->
            let calls = ref 0 in
            try
              ignore
                (Boolean.solve solver ~guard:(fun () ->
                     incr calls;
                     if !calls = limit then raise (Cancelled limit)))
            with Cancelled _ -> ())
          [ 8; 3; 2; 4 ];
        ignore (input solver 4 [ -1 ]);
        verify solver 5 (clauses @ [ [ -1 ] ]) );
    ( "Boolean decides by the activity heap as by the reference scan, guard calls included",
      fun () ->
        (* Random incremental histories (variables added in bursts, past 256 so the scan polls
           its guard more than once, clauses of 0-5 literals, solves after a few inputs) run on a
           solver deciding by the heap and on one deciding by the scan (Boolean.scan_best). Every
           guard call is counted, and some solves are cancelled at the same call in both. Results,
           proofs, statistics and guard counts must be equal; a large starting increment makes the
           activities rescale (and the heap be rebuilt) often. *)
        let rng = Random.State.make [| 11; 19; 2026 |] in
        let rescaled = ref 0 and cancelled = ref 0 and decisions = ref 0 in
        let conflicts = ref 0 in
        for round = 1 to 300 do
          let heap = Boolean.create () and scan = Boolean.create () in
          scan.reference <- true;
          let n = ref 0 and inputs = ref 0 in
          let grow k =
            for _ = 1 to k do
              equal (Boolean.new_variable heap) (Boolean.new_variable scan) "variable ids differ";
              incr n
            done
          in
          grow (20 + Random.State.int rng 20);
          for step = 1 to 300 do
            if Random.State.int rng 30 = 0 then grow (Random.State.int rng 100);
            (* Mostly three literals over a window of 12 variables: dense enough for conflicts;
               now and then a wider clause or a unit. *)
            let base = Random.State.int rng (max 1 (!n - 12)) in
            let width =
              match Random.State.int rng 200 with 0 -> 1 | 1 | 2 | 3 | 4 | 5 -> 5 | _ -> 3
            in
            let clause =
              List.init width (fun _ ->
                  let v = 1 + base + Random.State.int rng (min 12 !n) in
                  if Random.State.bool rng then v else -v)
            in
            let i = !inputs in
            incr inputs;
            equal (input heap i clause) (input scan i clause) "leaf ids differ";
            if step mod 8 = 0 then (
              if round mod 3 = 0 then (
                heap.increment <- Float.max heap.increment 6e99;
                scan.increment <- Float.max scan.increment 6e99);
              let stop = if Random.State.int rng 3 = 0 then 1 + Random.State.int rng 400 else -1 in
              let solve solver =
                let calls = ref 0 in
                let before = solver.Boolean.increment in
                let result =
                  try
                    Some
                      (Boolean.solve solver ~guard:(fun () ->
                           incr calls;
                           if !calls = stop then raise (Cancelled stop)))
                  with Cancelled _ -> None
                in
                (result, !calls, solver.Boolean.increment < before)
              in
              let a, ca, ra = solve heap and b, cb, _ = solve scan in
              equal a b "the heap's solve differs from the scan's";
              equal ca cb "the heap's guard calls differ from the scan's";
              if ra then incr rescaled;
              if a = None then incr cancelled;
              equal (Boolean.proof heap) (Boolean.proof scan) "proofs differ";
              equal (Boolean.statistics heap) (Boolean.statistics scan) "statistics differ")
          done;
          decisions := !decisions + (Boolean.statistics heap).decisions;
          conflicts := !conflicts + (Boolean.statistics heap).conflicts
        done;
        check (!rescaled > 20) "the activities rescaled too rarely";
        check (!cancelled > 200) "too few cancelled solves";
        check (!decisions > 50000 && !conflicts > 300) "too few decisions or conflicts" );
    ( "Boolean identical incremental histories produce identical models and proofs",
      fun () ->
        let a = make 5 and b = make 5 in
        List.iteri
          (fun i clause ->
            equal (input a i clause) (input b i clause) "nondeterministic leaf ID";
            equal (Boolean.solve a ~guard) (Boolean.solve b ~guard) "nondeterministic model";
            equal (Boolean.proof a) (Boolean.proof b) "nondeterministic proof")
          [ [ 1; 3; 4 ]; [ 1; 3; -4 ]; [ 2; 5 ]; [ -1 ]; [ -3 ]; [ 4; -4 ] ] );
  ]

let () = run tests
