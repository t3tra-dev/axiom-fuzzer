open Axiom_fuzzer
open Test_support
open Wire

exception Cancelled

type fixture = {
  theory : Theory.t;
  proof : Proof.t;
  ordinary : Calculus.t;
  transfer : Goal_transfer.t;
  live : (int, int) Hashtbl.t;
  mutable virtual_id : int;
  mutable emitted : step list;
}

let guard () = ()
let never _ = false
let literal name positive terms = { positive; atom = P (name, terms) }
let pos name terms = literal name true terms
let neg name terms = literal name false terms
let f name terms = Fn (Original name, terms)
let a = constant "a"
let x = V (0, 0)

let prepare ?(ordered = false) text =
  let theory = Tptp.parse text and proof = Proof.create () in
  let live = Hashtbl.create 16 in
  List.iter
    (fun axiom ->
      Clausify.run ~mode:Distributive axiom
      |> List.iteri (fun i clause ->
          let step = Proof.add proof (Clause.normalize clause) (Input (axiom.axiom_id, i)) in
          Hashtbl.add live step.id (step.id + 1)))
    (Theory.fixed theory);
  let ordinary = Calculus.create ~ordered (Term.create ()) in
  {
    theory;
    proof;
    ordinary;
    transfer = Goal_transfer.create ~calculus:ordinary ();
    live;
    virtual_id = -1;
    emitted = [];
  }

let alive h (id, generation) = Hashtbl.find_opt h.live id = Some generation
let ticket h id = (id, Hashtbl.find h.live id)

let leaf ?(support = []) h id : Goal.recipe =
  let step = Proof.get h.proof id in
  { step; raw = step.clause; parents = []; leaves = [ ticket h id ]; support; height = 0 }

let derive h parents wanted inference : Goal.recipe =
  let results = ref [] in
  inference (fun raw rule -> results := (raw, rule) :: !results);
  let raw, rule =
    List.find (fun (raw, _) -> Clause.normalize raw = Clause.normalize wanted) !results
  in
  let id = h.virtual_id in
  h.virtual_id <- id - 1;
  {
    step = { id; clause = Clause.normalize raw; rule };
    raw;
    parents;
    leaves = List.fold_left (fun acc (p : Goal.recipe) -> Goal.union acc p.leaves) [] parents;
    support = List.fold_left (fun acc (p : Goal.recipe) -> Goal.union acc p.support) [] parents;
    height = 1 + List.fold_left (fun acc (p : Goal.recipe) -> max acc p.height) 0 parents;
  }

let resolve h (p : Goal.recipe) (q : Goal.recipe) wanted =
  let calculus = Calculus.create ~selection:false (Term.create ()) in
  derive h [ p; q ] wanted (Calculus.resolve calculus p.step q.step)

let offer h p = Goal_transfer.offer h.transfer ~guard ~alive:(alive h) ~blocked:never p

let request ?previous ?(support = []) h id =
  Goal_transfer.request h.transfer ?previous ~support (ticket h id) (Proof.get h.proof id)

let start_request ?support h id = ignore (request ?support h id)
let record h raw rule = Proof.add h.proof (Clause.normalize raw) rule

let emit ?(accept = true) ?kind h ~recorded ~accepted raw rule =
  let clause = Clause.normalize raw in
  if not (List.exists (fun (step : step) -> step.clause = clause) h.emitted) then (
    let step = record h raw rule in
    recorded step;
    h.emitted <- step :: h.emitted;
    if accept then
      accepted
        (Option.value
           ~default:
             (if clause = [] then Goal_transfer.Unconditional_empty else Goal_transfer.Retained)
           kind)
        step)

let advance ?(attempts = 1) ?(guard = guard) ?(blocked = never) ?record:recording ?emit:emitting h =
  Goal_transfer.advance ~attempts h.transfer ~guard ~alive:(alive h) ~blocked
    ~record:(Option.value ~default:(record h) recording)
    ~emit:(Option.value ~default:(emit h) emitting)

let drain ?(blocked = never) ?record ?emit h =
  let left = ref 2000 in
  while Goal_transfer.has_work h.transfer && !left > 0 do
    decr left;
    advance ~blocked ?record ?emit h
  done;
  check (!left > 0) "consumer fixture did not quiesce"

let next_pending h =
  let pending () =
    Tbl.Int.fold
      (fun _ (q : Goal_transfer.request) yes -> yes || q.pending <> [])
      h.transfer.requests false
  in
  let left = ref 100 in
  while (not (pending ())) && !left > 0 do
    decr left;
    advance h
  done;
  check (pending ()) "fixture produced no pending request result"

let ordinary_resolve h (p : step) q =
  let result = ref None in
  Calculus.resolve h.ordinary p (Proof.get h.proof q) (fun raw rule ->
      if !result = None then result := Some (record h raw rule));
  Option.get !result

let check_certificate h root =
  let certificate =
    Proof.extract ~cnf_mode:Distributive h.proof ~theory:(Theory.name h.theory)
      ~axioms:(Theory.fixed h.theory) ~root
  in
  (match Kernel.check h.theory certificate with Ok _ -> () | Error e -> failwith e);
  let wrong = Tptp.parse "cnf(unrelated,axiom,unrelated(a))." in
  check (Result.is_error (Kernel.check wrong certificate)) "wrong original input accepted";
  certificate

let resolution_text =
  "cnf(seed,axiom,(p(X)|q(X)|k(X))). cnf(nk,axiom,~k(X)). cnf(consumer,axiom,(~p(a)|r(a)|s(a))). \
   cnf(nq,axiom,~q(a)). cnf(nr,axiom,~r(a)). cnf(ns,axiom,~s(a))."

let resolution_fixture () =
  let h = prepare resolution_text in
  let p = resolve h (leaf h 0) (leaf h 1) [ pos "p" [ x ]; pos "q" [ x ] ] in
  (h, p)

let shared_fixture () =
  let h =
    prepare
      "cnf(seed,axiom,(p(X)|~p(f(X))|k)). cnf(nk,axiom,~k). cnf(consumer,axiom,~p(a)). \
       cnf(last,axiom,p(f(f(a))))."
  in
  let p = resolve h (leaf h 0) (leaf h 1) [ pos "p" [ x ]; neg "p" [ f "f" [ x ] ] ] in
  let q = resolve h p p [ pos "p" [ x ]; neg "p" [ f "f" [ f "f" [ x ] ] ] ] in
  (h, q)

let tests =
  [
    ( "an offered recipe without an ordinary consumer records no proof",
      fun () ->
        let h, p = resolution_fixture () in
        let before = Proof.length h.proof in
        offer h p;
        drain h;
        equal (Proof.length h.proof) before "private offer materialized without a consumer";
        equal h.transfer.metrics.ancestor_recorded 0 "private offer claimed a record";
        equal (Tbl.Int.length h.transfer.offers) 1 "live unmatched recipe was discarded" );
    ( "Resolve keeps both residual clauses and produces checked ordinary ancestry",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        drain h;
        start_request h 2;
        drain h;
        let result = List.hd h.emitted in
        equal result.clause
          (Clause.normalize [ pos "q" [ a ]; pos "r" [ a ]; pos "s" [ a ] ])
          "resolution lost a residual or shared substitution";
        equal h.transfer.metrics.accepted 1 "accepted consumption was not observed";
        equal h.transfer.metrics.feedback 0 "accepted consumption created priority feedback";
        equal h.ordinary.attempts 0 "private work charged the ordinary calculus";
        let root = List.fold_left (ordinary_resolve h) result [ 3; 4; 5 ] in
        equal root.clause [] "fixture did not close";
        let cert = check_certificate h root.id in
        Tbl.Int.iter
          (fun id () ->
            check (id >= 0) "virtual ID claimed as ordinary provenance";
            check
              (List.exists (fun (s : step) -> s.id = id) cert.steps)
              "materialized ID absent from final proof")
          h.transfer.ancestor_ids;
        List.iter
          (fun (s : step) ->
            check (List.for_all (( <= ) 0) (Wire.parents s.rule)) "virtual rule parent escaped")
          cert.steps );
    ( "Paramodulate from the virtual equality preserves both remainders",
      fun () ->
        let h =
          prepare
            "cnf(seed,axiom,(f(X)=g(X)|k(X)|r(X))). cnf(nk,axiom,~k(X)). \
             cnf(consumer,axiom,(p(f(a))|s(a))). cnf(np,axiom,~p(g(a))). cnf(nr,axiom,~r(a)). \
             cnf(ns,axiom,~s(a))."
        in
        let p =
          resolve h (leaf h 0) (leaf h 1) [ positive (E (f "f" [ x ], f "g" [ x ])); pos "r" [ x ] ]
        in
        offer h p;
        start_request h 2;
        drain h;
        let result =
          List.find
            (fun (s : step) ->
              s.clause = Clause.normalize [ pos "p" [ f "g" [ a ] ]; pos "r" [ a ]; pos "s" [ a ] ])
            h.emitted
        in
        check (h.transfer.metrics.outgoing_attempts > 0) "outgoing equality was not attempted";
        let root = List.fold_left (ordinary_resolve h) result [ 3; 4; 5 ] in
        ignore (check_certificate h root.id) );
    ( "Paramodulate from the ordinary equality substitutes every virtual residual",
      fun () ->
        let h =
          prepare
            "cnf(seed,axiom,(p(f(X))|k(X)|r(X))). cnf(nk,axiom,~k(X)). \
             cnf(consumer,axiom,(f(a)=g(a)|s(a))). cnf(np,axiom,~p(g(a))). cnf(nr,axiom,~r(a)). \
             cnf(ns,axiom,~s(a))."
        in
        let p = resolve h (leaf h 0) (leaf h 1) [ pos "p" [ f "f" [ x ] ]; pos "r" [ x ] ] in
        offer h p;
        start_request h 2;
        drain h;
        let result =
          List.find
            (fun (s : step) ->
              s.clause = Clause.normalize [ pos "p" [ f "g" [ a ] ]; pos "r" [ a ]; pos "s" [ a ] ])
            h.emitted
        in
        check (h.transfer.metrics.incoming_attempts > 0) "incoming equality was not attempted";
        let root = List.fold_left (ordinary_resolve h) result [ 3; 4; 5 ] in
        ignore (check_certificate h root.id) );
    ( "shared virtual ancestors materialize once with actual IDs",
      fun () ->
        let h, p = shared_fixture () in
        offer h p;
        start_request h 2;
        drain h;
        equal h.transfer.metrics.ancestor_recorded 2 "shared virtual DAG was copied twice";
        let root = ordinary_resolve h (List.hd h.emitted) 3 in
        ignore (check_certificate h root.id) );
    ( "unification preserves repeated variables and rejects occurs cycles",
      fun () ->
        let h =
          prepare "cnf(seed,axiom,(p(X,X)|k)). cnf(nk,axiom,~k). cnf(bad,axiom,~p(Y,f(Y)))."
        in
        let p = resolve h (leaf h 0) (leaf h 1) [ pos "p" [ x; x ] ] in
        offer h p;
        start_request h 2;
        drain h;
        equal h.transfer.metrics.conclusions 0 "occurs cycle generated a conclusion";
        equal h.transfer.metrics.ancestor_recorded 0 "failed unification recorded a recipe";
        equal (Unify.mark h.transfer.calculus.unifier) 0 "unifier trail escaped" );
    ( "ordinary selected literals apply when changed work opens a fresh request",
      fun () ->
        let h =
          prepare ~ordered:true
            "cnf(seed,axiom,(p(X)|k)). cnf(nk,axiom,~k). cnf(consumer,axiom,(~p(a)|~z(a)))."
        in
        let p = resolve h (leaf h 0) (leaf h 1) [ pos "p" [ x ] ] in
        let c = Proof.get h.proof 2 in
        let p_position = Option.get (List.find_index (( = ) (neg "p" [ a ])) c.clause) in
        let z_position = Option.get (List.find_index (( = ) (neg "z" [ a ])) c.clause) in
        Tbl.Int.replace h.ordinary.selected 2 (Some [ z_position ]);
        offer h p;
        start_request h 2;
        drain h;
        equal h.transfer.metrics.ancestor_recorded 0 "unselected consumer literal was used";
        Tbl.Int.replace h.ordinary.selected 2 (Some [ p_position ]);
        Goal_transfer.selection_changed h.transfer 2;
        start_request h 2;
        drain h;
        equal (List.hd h.emitted).clause [ neg "z" [ a ] ] "changed selection was never retried" );
    ( "a blocked support union cannot materialize even individually live premises",
      fun () ->
        let h, plain = resolution_fixture () in
        let p = { plain with Goal.support = [ 1 ] } in
        offer h p;
        start_request ~support:[ 2 ] h 2;
        drain ~blocked:(fun support -> List.mem 1 support && List.mem 2 support) h;
        equal h.transfer.metrics.ancestor_recorded 0 "incompatible support recorded a proof";
        equal h.transfer.metrics.accepted 0 "incompatible support was accepted" );
    ( "conditional empty acceptance is separate from ordinary root acceptance",
      fun () ->
        let h = prepare "cnf(seed,axiom,(p(X)|k)). cnf(nk,axiom,~k). cnf(consumer,axiom,~p(a))." in
        let p = resolve h (leaf ~support:[ 3 ] h 0) (leaf h 1) [ pos "p" [ x ] ] in
        offer h p;
        start_request h 2;
        drain ~emit:(emit ~kind:Goal_transfer.Conditional_empty h) h;
        equal h.transfer.metrics.conditional 1 "conditional empty acceptance was lost";
        equal h.transfer.metrics.unconditional 0 "conditional proof became an ordinary root";
        equal h.transfer.metrics.accepted 1 "conditional accepted consumption was not observed";
        equal h.transfer.metrics.feedback 0 "conditional acceptance created priority feedback" );
    ( "filtered duplicates have no direct record, acceptance or feedback",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        start_request h 2;
        drain ~emit:(fun ~recorded:_ ~accepted:_ _ _ -> ()) h;
        check (h.transfer.metrics.emit_calls > 0) "fixture never reached admission";
        equal h.transfer.metrics.direct_recorded 0 "filtered duplicate claimed direct record";
        equal h.transfer.metrics.accepted 0 "filtered duplicate claimed acceptance";
        equal h.transfer.metrics.feedback 0 "filtered duplicate requested premises" );
    ( "recorded but unaccepted results are not reported as consumed",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        start_request h 2;
        drain ~emit:(emit ~accept:false h) h;
        equal h.transfer.metrics.direct_recorded 1 "direct record fact was lost";
        equal h.transfer.metrics.accepted 0 "direct record was treated as admission";
        equal h.transfer.metrics.feedback 0 "unaccepted record created feedback" );
    ( "a stale ordinary leaf prevents reconstruction and collection expires its offer",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        start_request h 2;
        next_pending h;
        Hashtbl.remove h.live 0;
        Goal_transfer.remove h.transfer 0;
        drain h;
        equal h.transfer.metrics.ancestor_recorded 0 "expired leaf was reconstructed";
        check (h.transfer.metrics.stale_results > 0) "stale pending result was not diagnosed";
        Goal_transfer.collect h.transfer ~alive:(alive h);
        equal (Tbl.Int.length h.transfer.offers) 0 "stale offer survived collection" );
    ( "reactivated consumer generations reject the old pending result and retry",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        start_request h 2;
        next_pending h;
        Goal_transfer.remove h.transfer 2;
        Hashtbl.replace h.live 2 100;
        start_request h 2;
        advance h;
        equal h.transfer.metrics.ancestor_recorded 0 "old consumer ticket reconstructed a proof";
        drain h;
        equal h.transfer.metrics.accepted 1 "reactivated consumer did not receive fresh work";
        equal h.transfer.request_metrics.invalidated 1 "old request was not invalidated" );
    ( "cancellation preserves a reconstructed prefix and resumes without duplicate records",
      fun () ->
        let h, p = shared_fixture () in
        offer h p;
        start_request h 2;
        let calls = ref 0 in
        let recording raw rule =
          incr calls;
          if !calls = 2 then raise Cancelled else record h raw rule
        in
        (try
           drain ~record:recording h;
           failwith "fixture did not cancel"
         with Cancelled -> ());
        equal h.transfer.metrics.ancestor_recorded 1 "cancelled reconstruction lost its prefix";
        equal (Unify.mark h.transfer.calculus.unifier) 0 "cancelled reconstruction retained a trail";
        drain h;
        equal h.transfer.metrics.ancestor_recorded 2 "resume duplicated a surviving ancestor";
        let root = ordinary_resolve h (List.hd h.emitted) 3 in
        ignore (check_certificate h root.id) );
    ( "collection reclaims cancelled intermediates and retry rebuilds from live leaves",
      fun () ->
        let h, p = shared_fixture () in
        offer h p;
        start_request h 2;
        let calls = ref 0 in
        let recording raw rule =
          incr calls;
          if !calls = 2 then raise Cancelled else record h raw rule
        in
        (try
           drain ~record:recording h;
           failwith "fixture did not cancel"
         with Cancelled -> ());
        let old = Tbl.Int.to_seq_keys h.transfer.ancestor_ids |> List.of_seq |> List.hd in
        Goal_transfer.collect h.transfer ~alive:(alive h);
        let roots = Hashtbl.to_seq_keys h.live |> List.of_seq in
        check (Proof.reclaim h.proof roots > 0) "private store pinned a cancelled intermediate";
        check
          (try
             ignore (Proof.get h.proof old);
             false
           with Not_found -> true)
          "old actual ID survived fixture GC";
        drain h;
        equal h.transfer.metrics.ancestor_recorded 3 "retry reused a reclaimed actual ID";
        let root = ordinary_resolve h (List.hd h.emitted) 3 in
        ignore (check_certificate h root.id) );
    ( "accepted callback before Stop preserves one acceptance and is not replayed",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        start_request h 2;
        let emitting ~recorded ~accepted raw rule =
          emit h ~recorded ~accepted raw rule;
          raise Cancelled
        in
        (try
           drain ~emit:emitting h;
           failwith "fixture did not stop"
         with Cancelled -> ());
        equal h.transfer.metrics.accepted 1 "accepted callback was rolled back after Stop";
        drain h;
        equal h.transfer.metrics.emit_calls 1 "spent accepted result was emitted again";
        equal h.transfer.metrics.accepted 1 "accepted result was counted again";
        equal h.transfer.metrics.feedback 0 "accepted result created priority feedback" );
    ( "live distinct offers have no independent capacity cutoff and duplicates merge",
      fun () ->
        let h, p = resolution_fixture () in
        for i = 1 to 600 do
          let clause = [ pos ("unmatched" ^ string_of_int i) [] ] in
          let proof = { p with Goal.step = { p.step with id = -i; clause }; raw = clause } in
          offer h proof
        done;
        equal (Tbl.Int.length h.transfer.offers) 600 "live recipes were evicted by capacity";
        let same = Tbl.Int.find h.transfer.offers (-1) in
        offer h { same.proof with step = { same.proof.step with id = -601 } };
        equal (Tbl.Int.length h.transfer.offers) 600 "equal clause/support was duplicated";
        equal h.transfer.metrics.merged 1 "merge was not observed";
        equal h.transfer.metrics.ancestor_recorded 0
          "capacity fixture materialized an unchecked recipe" );
    ( "a completed short work still consumes its sealed recipe frontier",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        let token = request h 2 in
        Goal_transfer.complete_request h.transfer token;
        equal h.transfer.request_metrics.sealed 1 "ordinary completion did not seal";
        equal h.transfer.request_metrics.drained 0 "ordinary completion prematurely closed";
        equal (Goal_transfer.consumer_count h.transfer) 1 "response debt disappeared";
        drain h;
        let result = List.hd h.emitted in
        equal result.clause
          (Clause.normalize [ pos "q" [ a ]; pos "r" [ a ]; pos "s" [ a ] ])
          "requested resolution lost residuals or reversed its positions";
        equal h.transfer.request_metrics.drained 1 "finite response debt did not close";
        equal (Goal_transfer.consumer_count h.transfer) 0 "drained request remained live";
        let root = List.fold_left (ordinary_resolve h) result [ 3; 4; 5 ] in
        ignore (check_certificate h root.id) );
    ( "only selected work opens a request; retained clauses are not consumers",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        check (not (Goal_transfer.has_work h.transfer)) "unrequested offer scheduled consumption";
        equal (Goal_transfer.consumer_count h.transfer) 0 "retained inputs became consumers";
        equal h.transfer.metrics.ancestor_recorded 0 "an unrequested recipe was materialized";
        start_request h 2;
        check (Goal_transfer.has_work h.transfer) "selected work did not schedule consumption";
        equal (Goal_transfer.consumer_count h.transfer) 1 "selected work did not open a request" );
    ( "pending work wakes on a late recipe without reopening its token",
      fun () ->
        let h, p = resolution_fixture () in
        let token = request h 2 in
        drain h;
        equal (Goal_transfer.consumer_count h.transfer) 1 "open ordinary continuation was closed";
        check (not (Goal_transfer.has_work h.transfer)) "empty request remained runnable";
        equal (request ~previous:token h 2) token "ordinary resume made a new request";
        offer h p;
        drain h;
        equal h.transfer.metrics.accepted 1 "late recipe did not reach the pending request";
        Goal_transfer.complete_request h.transfer token;
        drain h;
        equal h.transfer.request_metrics.opened 1 "pending wake duplicated a work request";
        equal h.transfer.request_metrics.drained 1 "completed pending work did not close" );
    ( "a sealed request excludes later recipes and never reopens on retention alone",
      fun () ->
        let h, p = resolution_fixture () in
        let token = request h 2 in
        Goal_transfer.complete_request h.transfer token;
        offer h p;
        drain h;
        equal h.transfer.metrics.accepted 0 "post-seal recipe entered the finite debt";
        equal h.transfer.metrics.ancestor_recorded 0 "post-seal recipe was materialized";
        equal (Goal_transfer.consumer_count h.transfer) 0 "sealed empty debt did not close";
        let later_recipe = resolve h p (leaf h 3) [ pos "p" [ a ] ] in
        offer h later_recipe;
        drain h;
        equal h.transfer.metrics.accepted 0 "new offer resurrected completed work";
        let later = request h 2 in
        check (later <> token) "new ordinary work reused a closed token";
        Goal_transfer.complete_request h.transfer later;
        drain h;
        check (h.transfer.metrics.accepted > 0) "new ordinary selection could not use the recipe" );
    ( "same-owner work tokens have independent seals and late arrivals",
      fun () ->
        let h, p = resolution_fixture () in
        let first = request h 2 and second = request h 2 in
        check (first <> second) "owner ticket conflated independent ordinary work";
        Goal_transfer.complete_request h.transfer first;
        offer h p;
        drain h;
        equal h.transfer.request_metrics.drained 1 "sealed first work remained open";
        equal (Goal_transfer.consumer_count h.transfer) 1 "first close removed the second work";
        equal h.transfer.metrics.accepted 1 "second work did not consume its late offer";
        Goal_transfer.complete_request h.transfer first;
        equal (Goal_transfer.consumer_count h.transfer) 1 "old completion closed another token";
        Goal_transfer.complete_request h.transfer second;
        drain h;
        equal h.transfer.request_metrics.drained 2 "second work did not independently close" );
    ( "a re-added private posting after sealing cannot cross the frontier",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        let token = request h 2 in
        Goal_transfer.complete_request h.transfer token;
        (* Adversarial index maintenance: the same virtual ID now denotes a
           newer posting generation, while the old cursor frontier is sealed. *)
        Index.add h.transfer.recipe_index p.step;
        Equality_index.add h.transfer.recipe_equality p.step;
        drain h;
        equal h.transfer.metrics.accepted 0 "new posting generation crossed the seal";
        equal h.transfer.request_metrics.drained 1 "excluded postings prevented finite close" );
    ( "ordinary ID zero is valid and request IDs remain a separate namespace",
      fun () ->
        let h = prepare "cnf(consumer,axiom,~p(a)). cnf(seed,axiom,(p(X)|k)). cnf(nk,axiom,~k)." in
        let p = resolve h (leaf h 1) (leaf h 2) [ pos "p" [ x ] ] in
        offer h p;
        let token = request h 0 in
        Goal_transfer.complete_request h.transfer token;
        equal (Goal_transfer.request_counts h.transfer) (0, 1) "sealed gauge was not draining";
        drain h;
        equal h.transfer.metrics.accepted 1 "ordinary ID zero was rejected";
        equal (Goal_transfer.request_counts h.transfer) (0, 0) "drained request remained in gauges";
        let root = List.find (fun (s : step) -> s.clause = []) h.emitted in
        ignore (check_certificate h root.id) );
    ( "retiring an owner discards pending response before reconstruction",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        let token = request h 2 in
        next_pending h;
        Goal_transfer.remove h.transfer 2;
        Goal_transfer.complete_request h.transfer token;
        drain h;
        equal h.transfer.metrics.ancestor_recorded 0 "retired request reconstructed ancestors";
        equal h.transfer.metrics.accepted 0 "retired pending response was accepted";
        equal h.transfer.request_metrics.invalidated 1 "retirement was not observed" );
    ( "selection changes invalidate old work until an ordinary resume reopens it",
      fun () ->
        let h =
          prepare ~ordered:true
            "cnf(seed,axiom,(p(X)|k)). cnf(nk,axiom,~k). cnf(consumer,axiom,(~p(a)|~z(a)))."
        in
        let p = resolve h (leaf h 0) (leaf h 1) [ pos "p" [ x ] ] in
        let c = Proof.get h.proof 2 in
        let pi = Option.get (List.find_index (( = ) (neg "p" [ a ])) c.clause) in
        let zi = Option.get (List.find_index (( = ) (neg "z" [ a ])) c.clause) in
        Tbl.Int.replace h.ordinary.selected 2 (Some [ pi ]);
        offer h p;
        let old = request h 2 in
        next_pending h;
        Tbl.Int.replace h.ordinary.selected 2 (Some [ zi ]);
        Goal_transfer.selection_changed h.transfer 2;
        drain h;
        equal h.transfer.metrics.ancestor_recorded 0 "old selected-pivot response survived";
        equal (Goal_transfer.consumer_count h.transfer) 0 "selection change reopened work";
        Tbl.Int.replace h.ordinary.selected 2 (Some [ pi ]);
        Goal_transfer.selection_changed h.transfer 2;
        drain h;
        equal h.transfer.metrics.accepted 0 "selection alone reopened work";
        let fresh = request ~previous:old h 2 in
        check (fresh <> old) "ordinary resume retained an invalidated token";
        Goal_transfer.complete_request h.transfer old;
        Goal_transfer.complete_request h.transfer fresh;
        drain h;
        equal h.transfer.metrics.accepted 1 "fresh selected work was not consumed";
        equal h.transfer.request_metrics.drained 1 "old completion damaged the fresh request" );
    ( "consumer acceptance records progress without priority feedback",
      fun () ->
        let h, p = resolution_fixture () in
        offer h p;
        let token = request h 2 in
        Goal_transfer.complete_request h.transfer token;
        drain h;
        equal h.transfer.metrics.accepted 1 "consumption hid actual acceptance";
        equal h.transfer.metrics.feedback 0 "acceptance created priority feedback" );
    ( "requested reconstruction survives cancellation and ordinary collection",
      fun () ->
        let h, p = shared_fixture () in
        offer h p;
        let token = request h 2 in
        Goal_transfer.complete_request h.transfer token;
        let calls = ref 0 in
        let recording raw rule =
          incr calls;
          if !calls = 2 then raise Cancelled else record h raw rule
        in
        (try
           drain ~record:recording h;
           failwith "request reconstruction did not cancel"
         with Cancelled -> ());
        equal h.transfer.metrics.ancestor_recorded 1 "request lost cancelled prefix";
        equal h.transfer.request_metrics.drained 0 "cancelled debt was closed";
        Goal_transfer.collect h.transfer ~alive:(alive h);
        let roots = Hashtbl.to_seq_keys h.live |> List.of_seq in
        check (Proof.reclaim h.proof roots > 0) "request pinned a cancelled intermediate";
        drain h;
        equal h.transfer.metrics.ancestor_recorded 3 "request reused reclaimed proof IDs";
        equal h.transfer.request_metrics.drained 1 "reconstructed debt did not close";
        let root = ordinary_resolve h (List.hd h.emitted) 3 in
        ignore (check_certificate h root.id) );
    ( "requested Paramodulate supports both directions with nonempty residuals",
      fun () ->
        List.iter
          (fun virtual_equality ->
            let text =
              if virtual_equality then
                "cnf(seed,axiom,(f(X)=g(X)|k(X)|r(X))). cnf(nk,axiom,~k(X)). \
                 cnf(consumer,axiom,(p(f(a))|s(a))). cnf(np,axiom,~p(g(a))). cnf(nr,axiom,~r(a)). \
                 cnf(ns,axiom,~s(a))."
              else
                "cnf(seed,axiom,(p(f(X))|k(X)|r(X))). cnf(nk,axiom,~k(X)). \
                 cnf(consumer,axiom,(f(a)=g(a)|s(a))). cnf(np,axiom,~p(g(a))). \
                 cnf(nr,axiom,~r(a)). cnf(ns,axiom,~s(a))."
            in
            let h = prepare text in
            let wanted =
              if virtual_equality then [ positive (E (f "f" [ x ], f "g" [ x ])); pos "r" [ x ] ]
              else [ pos "p" [ f "f" [ x ] ]; pos "r" [ x ] ]
            in
            let p = resolve h (leaf h 0) (leaf h 1) wanted in
            offer h p;
            let token = request h 2 in
            Goal_transfer.complete_request h.transfer token;
            drain h;
            let result =
              List.find
                (fun (s : step) ->
                  s.clause
                  = Clause.normalize [ pos "p" [ f "g" [ a ] ]; pos "r" [ a ]; pos "s" [ a ] ])
                h.emitted
            in
            check
              ((if virtual_equality then h.transfer.metrics.outgoing_attempts
                else h.transfer.metrics.incoming_attempts)
              > 0)
              "requested equality cursor reversed its source and target";
            let root = List.fold_left (ordinary_resolve h) result [ 3; 4; 5 ] in
            ignore (check_certificate h root.id))
          [ true; false ] );
  ]

let () = run tests
