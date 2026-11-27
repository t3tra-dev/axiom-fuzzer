open Axiom_fuzzer
open Test_support
open Wire

let settings =
  {
    Engine.default_config with
    limits = { Engine.seconds = 3.; max_given = 1000; max_generated = 30000; max_retained = 30000 };
  }

let prepare text =
  let theory = Tptp.parse text in
  let engine = Engine.create settings in
  List.iter (Engine.add_axiom engine) (Theory.fixed theory);
  (theory, engine)

let checked theory engine =
  let c = Option.get (Engine.certificate engine ~theory:(Theory.name theory)) in
  (match Kernel.check theory c with Ok _ -> () | Error e -> failwith e);
  c

let plan_step e =
  Engine.protect (fun () ->
      Focus.advance e.Engine.focus
        ~guard:(fun () -> Engine.check_time e)
        ~alive:(Engine.current_ticket e) ~get:(Proof.get e.proof) ~record:(Engine.record e)
        ~emit:(Engine.emit e) ~demand:e.on_demand)

let state engine = engine.Engine.avatar

let conditional text =
  let theory, e = prepare text in
  let a = state e in
  let parents = List.filter (fun (s : step) -> List.length s.clause = 2) (Proof.steps e.proof) in
  List.iter
    (fun parent ->
      Avatar.offer_split a ~guard:(fun () -> ()) parent;
      Engine.protect (fun () -> Engine.split_step e a);
      (* Tests isolate the conditional path; production retains these original clauses. *)
      Engine.deactivate e parent.id)
    parents;
  (theory, e)

let shared_text =
  "cnf(c,axiom,(p(X)|q(Y))). cnf(d,axiom,(p(Y)|r(X))). cnf(n,axiom,~p(a)). cnf(m,axiom,~q(a)). \
   cnf(o,axiom,~r(a))."

let congruent_text = "cnf(e,axiom,(a=b|r)). cnf(n,axiom,(f(a)!=f(b)|r)). cnf(m,axiom,~r)."

(* A tower of nested congruences: a_k = f(a_{k-1}, a_{k-1}), b_k likewise, a_0 = b_0 (in [base],
   [r] makes it conditional), and [goal] relating a_n and b_n. Its forest explanation doubles at
   every level; with shared lemmas it is linear. *)
let tower ?(base = "a0=b0") ~goal n =
  let b = Buffer.create 256 in
  Printf.bprintf b "cnf(e0,axiom,(%s)). " base;
  for k = 1 to n do
    Printf.bprintf b "cnf(ea%d,axiom,a%d=f(a%d,a%d)). cnf(eb%d,axiom,b%d=f(b%d,b%d)). " k k (k - 1)
      (k - 1) k k (k - 1) (k - 1)
  done;
  Buffer.add_string b goal;
  Buffer.contents b

(* Ground units only, kept as written: no rewriting at admission, so the closure sees the tower. *)
let ground_settings explanation =
  {
    settings with
    demodulation = false;
    backward_demodulation = false;
    subsumption = false;
    backward_subsumption = false;
    ground_explanation = explanation;
  }

let ground_refutation explanation text =
  let theory = Tptp.parse text in
  let e = Engine.create (ground_settings explanation) in
  List.iter (Engine.add_axiom e) (Theory.fixed theory);
  Engine.protect (fun () -> Engine.ground_step e);
  (theory, e)

let roundtrip theory cert =
  match Kernel.check theory (Certificate_io.decode (Certificate_io.encode cert)) with
  | Ok _ -> ()
  | Error message -> failwith message

(* A random ground equational problem: unit equations between random terms over three constants,
   a unary and a binary function, and one disequation or a complementary predicate pair. *)
let random_ground seed =
  let state = ref ((seed * 7919) + 17) in
  let next bound =
    state := ((!state * 1103515245) + 12345) land 0x3fffffff;
    !state mod bound
  in
  let rec term depth =
    if depth = 0 || next 3 = 0 then Printf.sprintf "c%d" (next 3)
    else if next 2 = 0 then Printf.sprintf "g(%s)" (term (depth - 1))
    else Printf.sprintf "f(%s,%s)" (term (depth - 1)) (term (depth - 1))
  in
  let units =
    List.init (6 + next 14) (fun i -> Printf.sprintf "cnf(u%d,axiom,%s=%s)." i (term 2) (term 3))
  in
  let goal =
    if next 2 = 0 then Printf.sprintf "cnf(n,negated_conjecture,%s!=%s)." (term 3) (term 3)
    else
      Printf.sprintf "cnf(p,axiom,p(%s,%s)). cnf(n,negated_conjecture,~p(%s,%s))." (term 2) (term 2)
        (term 2) (term 2)
  in
  String.concat " " (units @ [ goal ])

let joint_text =
  "cnf(goal,axiom,(~p(X)|~q(X)|~r(X))). cnf(p,axiom,p(a)). cnf(q,axiom,q(a)). cnf(r,axiom,r(a))."

(* Many active premises make one given produce a long, finite stream. *)
let fanning_fixture ?(max_given = 1000) ?(extra_goals = 0) () =
  let count = 400 in
  let input =
    String.concat " " (List.init count (fun i -> Printf.sprintf "cnf(p%d,axiom,p(a%d))." i i))
    ^ Printf.sprintf " cnf(link,axiom,(~p(X)|q(X))). cnf(goal,axiom,~q(a%d))." (count - 1)
    ^ String.concat " "
        (List.init extra_goals (fun i ->
             Printf.sprintf "cnf(g%d,axiom,(missing%d(X)|other%d(X)))." i i i))
  in
  let theory = Tptp.parse input in
  let engine =
    Engine.create
      {
        settings with
        avatar = false;
        collect_every = 0;
        limits = { settings.limits with max_given };
      }
  in
  let axioms = Theory.fixed theory in
  List.iteri (fun i a -> if i < count then Engine.add_axiom engine a) axioms;
  Engine.finish engine;
  let link = Proof.length engine.proof in
  Engine.add_axiom engine (List.nth axioms count);
  select_given engine link;
  check (not (Queue.is_empty engine.pending)) "fixture did not suspend its fanout";
  List.iteri (fun i a -> if i >= count + 2 then Engine.add_axiom engine a) axioms;
  (theory, engine, List.nth axioms (count + 1))

let pending_fixture count =
  let _, e =
    prepare
      (String.concat " " (List.init count (fun i -> Printf.sprintf "cnf(p%d,axiom,p(a%d))." i i)))
  in
  let steps = Index.all e.retained_index in
  List.iter
    (fun (s : step) ->
      let work : Engine.pending_inference =
        {
          owner = (s.id, Tbl.Int.find e.retained_index.live s.id);
          groups = Seq.empty;
          current = None;
        }
      in
      Queue.add work e.pending)
    steps;
  (e, List.map (fun (s : step) -> s.id) steps)

let tests =
  [
    ( "unfinished joint plans allocate no proof and resume after collection",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(goal,axiom,(~p(X)|~q(X)|~r(X)|~s(X))). cnf(p,axiom,p(a)). cnf(q,axiom,q(a)). \
             cnf(r,axiom,r(a)). cnf(s,axiom,s(a))."
        in
        let e = Engine.create { settings with avatar = false } in
        let axioms = Theory.fixed theory in
        List.iteri (fun i a -> if i < 3 then Engine.add_axiom e a) axioms;
        let generated = e.metrics.generated and stored = Proof.stored e.proof in
        plan_step e;
        equal e.metrics.generated generated "unfinished plan generated proof nodes";
        equal (Proof.stored e.proof) stored "unfinished plan retained a proof";
        equal (Tbl.Pair.length e.focus.saved) 1 "unfinished plan was not saved";
        Engine.collect e;
        List.iteri (fun i a -> if i >= 3 then Engine.add_axiom e a) axioms;
        plan_step e;
        equal e.focus.plan_reused 1 "saved substitutions were not reused";
        equal e.metrics.given 0 "resume depended on ordinary selection";
        Engine.collect e;
        ignore (checked theory e) );
    ( "saved plans cannot use a reclaimed or reactivated premise generation",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(goal,axiom,(~p(X)|~q(X)|~r(X)|~s(X))). cnf(p,axiom,p(a)). cnf(q,axiom,q(a))."
        in
        let e = Engine.create { settings with avatar = false } in
        List.iter (Engine.add_axiom e) (Theory.fixed theory);
        plan_step e;
        equal (Tbl.Pair.length e.focus.saved) 1 "fixture did not save a plan";
        let old = Proof.get e.proof 1 in
        Engine.deactivate e old.id;
        Engine.collect e;
        equal (Tbl.Pair.length e.focus.saved) 0 "invalid recipe survived collection";
        check (e.focus.plan_invalidated > 0) "lost premise was not reported";
        Engine.admit e old;
        plan_step e;
        equal e.focus.plan_reused 0 "old recipe survived premise reactivation";
        equal e.root None "incomplete theory was refuted" );
    ( "cost-aware work sharing preserves selection, continuation and joint probes",
      fun () ->
        let _, e, _ = fanning_fixture ~extra_goals:20 () in
        let given = e.metrics.given and ordinary = e.metrics.inference_ordinary_batches in
        let plans = e.focus.plans and yields = e.metrics.inference_yields in
        for _ = 1 to 128 do
          Engine.infer_step e
        done;
        check (e.metrics.inference_ordinary_batches > ordinary) "ordinary work received no turn";
        check (e.focus.plans > plans) "general expansion displaced every cheap joint probe";
        check (e.metrics.inference_yields > yields) "pending work received no continuation";
        check (e.metrics.given - given >= 3) "joint work displaced fresh clause selection" );
    ( "joint plans close a passive conjunction with checked binary-resolution ancestors",
      fun () ->
        let theory, e = prepare joint_text in
        plan_step e;
        check (e.root <> None) "joint plan did not close its goal";
        check (not e.focus.committing) "stopping at an empty clause leaked admission state";
        equal e.metrics.given 0 "joint plan depended on ordinary clause selection";
        equal e.focus.plan_steps 3 "joint plan did not retain all resolution steps";
        Engine.collect e;
        let c = checked theory e in
        equal (List.length c.axioms) 4 "joint proof lost a premise";
        check
          (List.exists
             (fun (s : step) ->
               match s.rule with Resolve _ -> not (Index.mem e.retained_index s.id) | _ -> false)
             c.steps)
          "proof-only resolution ancestors were not exercised" );
    ( "instantiated joint consequences never retire a universal target",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(goal,axiom,(~p(X)|~q(X)|r(X))). cnf(p,axiom,p(a)). cnf(q,axiom,q(a)). \
             cnf(nr,axiom,~r(a))."
        in
        let e = Engine.create { settings with avatar = false } in
        let axioms = Theory.fixed theory in
        List.iteri (fun i a -> if i < 3 then Engine.add_axiom e a) axioms;
        plan_step e;
        equal e.focus.plan_steps 2 "partial joint consequence was not committed";
        check (Index.mem e.retained_index 0) "a ground instance replaced a universal clause";
        Engine.collect e;
        Engine.add_axiom e (List.nth axioms 3);
        check (e.focus.plan_useful > 0) "a joint unit used by a later closure earned no feedback";
        ignore (checked theory e) );
    ( "new units wake old joint goals across proof collection",
      fun () ->
        let theory =
          Tptp.parse "cnf(goal,axiom,(~p(X)|~q(X))). cnf(p,axiom,p(a)). cnf(q,axiom,q(a))."
        in
        let e = Engine.create { settings with avatar = false } in
        let axioms = Theory.fixed theory in
        List.iteri (fun i a -> if i < 2 then Engine.add_axiom e a) axioms;
        plan_step e;
        equal e.root None "one condition incorrectly closed the goal";
        check (not (Focus.has_work e.focus)) "unsolved goal was busy-looped without new facts";
        Engine.collect e;
        Engine.add_axiom e (List.nth axioms 2);
        check (Focus.has_work e.focus) "new unit failed to wake an old goal";
        plan_step e;
        ignore (checked theory e) );
    ( "joint conflicts carry branch assumptions and do not refute a satisfiable theory",
      fun () ->
        let theory =
          Tptp.parse "cnf(choice,axiom,(p(a)|r)). cnf(goal,axiom,(~p(X)|~q(X))). cnf(q,axiom,q(a))."
        in
        let e = Engine.create { settings with avatar = false } in
        let axioms = Theory.fixed theory in
        Engine.add_axiom e (List.hd axioms);
        Avatar.offer_split e.avatar ~guard:(fun () -> ()) (Proof.get e.proof 0);
        Engine.split_step e e.avatar;
        e.avatar.model <- Array.make (Tbl.Int.length e.avatar.components) true;
        let component =
          Proof.steps e.proof
          |> List.find (fun (s : step) ->
              match (s.rule, s.clause) with
              | Component _, [ { atom = P ("p", _); _ } ] -> true
              | _ -> false)
        in
        Engine.admit e component;
        List.iter (Engine.add_axiom e) (List.tl axioms);
        plan_step e;
        plan_step e;
        equal e.focus.plan_closed 1 "conditional joint conflict was not explored";
        check (e.avatar.conflicts > 0 && e.root = None) "branch conflict became a global refutation";
        check
          (List.exists
             (fun (s : step) -> s.clause = [] && Avatar.dependency e.avatar s.id <> [])
             (Proof.steps e.proof))
          "conditional proof lost support";
        Engine.collect e;
        Engine.finish e;
        equal e.root None "consistent alternative branch was refuted" );
    ( "conditional subsumption resolution preserves the global target",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(choice,axiom,(p(X)|q(X)|r)). cnf(target,axiom,(~p(a)|q(a))). cnf(p,axiom,p(a)). \
             cnf(nq,axiom,~q(a))."
        in
        let e = Engine.create { settings with avatar = false } in
        let axioms = Theory.fixed theory in
        Engine.add_axiom e (List.hd axioms);
        Avatar.offer_split e.avatar ~guard:(fun () -> ()) (Proof.get e.proof 0);
        Engine.split_step e e.avatar;
        (* All components true is a valid model of this one split. Isolate the
           non-ground component so the global parent cannot do the shortening. *)
        e.avatar.model <- Array.make (Tbl.Int.length e.avatar.components) true;
        let component =
          Proof.steps e.proof
          |> List.find (fun (s : step) ->
              match s.rule with Component _ -> List.length s.clause = 2 | _ -> false)
        in
        Engine.admit e component;
        let side = component in
        Engine.activate e side;
        Passive.invalidate e.passive side.id;
        let target = Proof.length e.proof in
        Engine.add_axiom e (List.nth axioms 1);
        check (e.metrics.subsumption_resolved > 0) "conditional contraction was not exercised";
        check (Index.mem e.retained_index target) "conditional consequence hid the global target";
        let shortened =
          List.find
            (fun (s : step) ->
              match s.rule with Resolve (_, _, id, _, _) -> id = target | _ -> false)
            (Proof.steps e.proof)
        in
        check (Avatar.dependency e.avatar shortened.id <> []) "shortening lost its branch condition";
        Engine.collect e;
        List.iter (Engine.add_axiom e) (List.filteri (fun i _ -> i > 1) axioms);
        Engine.finish e;
        ignore (checked theory e) );
    ( "subsumption resolution keeps a replayable proof through retirement and collection",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(side,axiom,(p(X)|q(X))). cnf(target,axiom,(~p(a)|q(a)|r(a))). \
             cnf(nq,axiom,~q(a)). cnf(nr,axiom,~r(a))."
        in
        let e = Engine.create { settings with avatar = false } in
        let axioms = Theory.fixed theory in
        Engine.add_axiom e (List.nth axioms 0);
        select_given e 0;
        let target = Proof.length e.proof in
        Engine.add_axiom e (List.nth axioms 1);
        check
          (e.metrics.subsumption_resolved > 0)
          "multi-literal side premise did not shorten target";
        check (not (Index.mem e.retained_index target)) "old target remained searchable";
        Engine.collect e;
        List.iter (Engine.add_axiom e) (List.filteri (fun i _ -> i > 1) axioms);
        Engine.finish e;
        let certificate = checked theory e in
        check
          (List.exists (fun (s : step) -> s.id = target) certificate.steps)
          "retired resolution parent disappeared" );
    ( "new obligations promote waiting clauses using eligible inference positions",
      fun () ->
        let theory =
          Tptp.parse
            "cnf(waiting,axiom,(~p(a)|q(a))). cnf(blocked,axiom,(~a(a)|~p(a))). \
             cnf(goal,axiom,p(a))."
        in
        let demands = ref [] in
        let e =
          Engine.create ~on_demand:(fun ~guard:_ clause -> demands := clause :: !demands) settings
        in
        List.iter (Engine.add_axiom e) (Theory.fixed theory);
        check (Tbl.Int.mem e.passive.preference 0) "waiting complementary clause was not promoted";
        check (not (Tbl.Int.mem e.passive.preference 1)) "ineligible literal gained preference";
        check
          (List.mem [ negative (p [ constant "a" ]) ] !demands)
          "obligation callback missed polarity";
        Engine.collect e;
        check (Tbl.Int.mem e.passive.preference 0) "collection lost a live preference" );
    ( "pending preference survives interleaved ordinary selection turns",
      fun () ->
        let e, ids = pending_fixture 8 in
        let urgent = List.nth ids 7 in
        (Tbl.Int.find e.focus.entries urgent).credit <- 64;
        let taken =
          List.init 8 (fun turn ->
              (* With a nonempty passive queue, ordinary continuations are
                 dispatched on these odd batch numbers. *)
              e.metrics.inference_ordinary_batches <- (2 * turn) + 1;
              fst (Engine.take_pending e).owner)
        in
        equal taken
          [
            List.nth ids 0;
            List.nth ids 1;
            List.nth ids 2;
            urgent;
            List.nth ids 3;
            List.nth ids 4;
            List.nth ids 5;
            List.nth ids 6;
          ]
          "priority continuation was starved or displaced FIFO turns";
        equal e.pending_resumptions 8 "pending dispatch clock missed live work";
        equal e.focus.preferred_resumes 2 "priority was not applied every fourth resume" );
    ( "pending dispatch clock excludes empty and stale owners",
      fun () ->
        let e, ids = pending_fixture 5 in
        for _ = 1 to 3 do
          ignore (Engine.take_pending e)
        done;
        let stale = Queue.peek e.pending in
        let id = fst stale.owner in
        (* A high score from an obsolete generation must not hide a live owner. *)
        (Tbl.Int.find e.focus.entries id).credit <- 64;
        Index.remove e.retained_index id;
        Index.add e.retained_index (Proof.get e.proof id);
        let live = Engine.take_pending e in
        equal (fst live.owner) (List.nth ids 4) "stale preferred head hid live work";
        equal e.pending_resumptions 4 "live preferred dispatch did not advance the clock";
        equal (Engine.take_pending e).owner stale.owner "FIFO lost the stale entry";
        equal e.pending_resumptions 4 "stale generation consumed a priority slot";
        (try
           ignore (Engine.take_pending e);
           failwith "empty queue returned work"
         with Queue.Empty -> ());
        equal e.pending_resumptions 4 "empty queue consumed a priority slot";
        (* Cancellation after live dispatch does not retroactively refund a turn. *)
        Index.remove e.retained_index (fst live.owner);
        check (Engine.advance_inference ~quantum:1 e live) "retired dispatched work survived";
        equal e.pending_resumptions 4 "post-dispatch cancellation changed the clock";
        equal e.focus.preferred_resumes 1 "stale or empty work counted as preferred" );
    ( "bounded inference yields to clause selection and resumes after collection",
      fun () ->
        let theory, e, goal = fanning_fixture () in
        let work = Queue.peek e.pending in
        let owner, _ = work.owner in
        check (Index.mem e.index owner) "a suspended given was not visible to later givens";
        let given = e.metrics.given in
        for _ = 1 to 128 do
          if e.metrics.given = given then Engine.infer_step e
        done;
        check (e.metrics.given > given) "pending inference monopolized selection";
        check (not (Queue.is_empty e.pending)) "fixture finished before suspended-work collection";
        equal (Unify.mark e.calculus.unifier) 0 "yield retained unifier bindings";
        Engine.collect e;
        Engine.add_axiom e goal;
        Engine.finish e;
        ignore (checked theory e);
        check (e.metrics.inference_yields > 0) "fanout did not yield";
        check (Queue.is_empty e.pending) "finished search retained its continuations" );
    ( "reactivation cannot revive a pending inference from an older generation",
      fun () ->
        let theory, e, goal = fanning_fixture () in
        let old = Queue.peek e.pending in
        let owner, _ = old.owner in
        let premise = Proof.get e.proof owner in
        Engine.deactivate e owner;
        Engine.collect e;
        check (Queue.is_empty e.pending) "collection kept a dead owner continuation";
        Engine.admit e premise;
        check (not (Engine.current_ticket e old.owner)) "reactivation reused its old generation";
        let generated = e.metrics.generated in
        check (Engine.advance_inference ~quantum:1 e old) "stale continuation remained runnable";
        equal e.metrics.generated generated "stale work emitted an inference";
        Engine.add_axiom e goal;
        Engine.finish e;
        ignore (checked theory e) );
    ( "pending partner checks tolerate proof reclamation and cancel obsolete work",
      fun () ->
        let _, e, _ = fanning_fixture () in
        let work = Queue.peek e.pending in
        let owner, _ = work.owner in
        let used = Proof.steps e.proof |> List.concat_map (fun (s : step) -> Wire.parents s.rule) in
        let other =
          Index.all e.index
          |> List.find (fun (s : step) ->
              s.id <> owner && List.length s.clause = 1 && not (List.mem s.id used))
        in
        let abandoned : Engine.pending_inference =
          {
            owner = work.owner;
            current = None;
            groups =
              List.to_seq
                [
                  {
                    Engine.parents = [ (other.id, Tbl.Int.find e.retained_index.live other.id) ];
                    start = (fun () -> failwith "reclaimed premise was evaluated");
                  };
                ];
          }
        in
        Engine.retire e other.id;
        Engine.collect e;
        check
          (try
             ignore (Proof.get e.proof other.id);
             false
           with Not_found -> true)
          "fixture did not reclaim its obsolete premise";
        check
          (Engine.advance_inference ~quantum:4 e abandoned)
          "invalid partner group did not finish";
        check (e.metrics.inference_cancelled > 0) "obsolete work was not counted" );
    ( "already selected work can finish at the given-clause limit",
      fun () ->
        let theory, e, goal = fanning_fixture ~max_given:401 () in
        equal e.metrics.given 401 "fixture did not reach its selection limit";
        Engine.add_axiom e goal;
        Engine.finish e;
        equal e.metrics.given 401 "pending work bypassed the selection limit";
        ignore (checked theory e);
        check (Queue.is_empty e.pending) "finished search retained its continuations" );
    ( "shared component names preserve alpha renaming and distinct variables",
      fun () ->
        let a = Avatar.create () in
        let c x y = [ positive (p [ x; y ]); negative (P ("q", [ y; x ])) ] in
        let first = Avatar.name a (c (v 7) (v 3)) in
        equal (Avatar.name a (List.rev (c (v 1) (v 9)))) first "alpha variant got another name";
        let other = Avatar.name a [ positive (P ("r", [ v 7 ])) ] in
        let xs = Wire.variables (Tbl.Int.find a.components first).clause
        and ys = Wire.variables (Tbl.Int.find a.components other).clause in
        check (List.for_all (fun x -> not (List.mem x ys)) xs) "shared representatives overlap" );
    ( "split and original inference coexist and shared non-ground proofs replay",
      fun () ->
        let theory, e =
          prepare "fof(c,axiom,((![X]:p(X))|(![Y]:q(Y)))). fof(n,axiom,~p(a)). fof(m,axiom,~q(b))."
        in
        let a = state e in
        let parent = List.find (fun (s : step) -> List.length s.clause = 2) (Proof.steps e.proof) in
        Avatar.offer_split a ~guard:(fun () -> ()) parent;
        Engine.protect (fun () -> Engine.split_step e a);
        check (Index.mem e.retained_index parent.id) "splitting removed the original clause";
        (* Isolate the conditional path without changing its logical knowledge. *)
        Engine.deactivate e parent.id;
        Engine.finish e;
        let cert = checked theory e in
        check (cert.avatar <> None) "fixture did not exercise conditional replay";
        match Kernel.check theory (Certificate_io.decode (Certificate_io.encode cert)) with
        | Ok _ -> ()
        | Error message -> failwith message );
    ( "shared components across distinct splits retain checked occurrence renamings",
      fun () ->
        let theory, e = conditional shared_text in
        let a = state e in
        Engine.finish e;
        ignore (checked theory e);
        equal (Tbl.Int.length a.components) 3 "alpha-equivalent component was not shared" );
    ( "ground congruence conflicts retain branch assumptions in the final proof",
      fun () ->
        let theory, e = conditional congruent_text in
        Engine.protect (fun () -> Engine.synchronize e);
        Engine.protect (fun () -> Engine.ground_step e);
        check (e.ground.conflicts > 0) "conditional congruence was not exercised";
        Engine.finish e;
        let cert = checked theory e in
        check (cert.avatar <> None) "branch assumptions were lost" );
    ( "ground congruence explanations expand into checked equality inferences",
      fun () ->
        let theory, e =
          prepare
            "fof(e,axiom,a=b). fof(h,axiom,h(a)=c). fof(p,axiom,p(f(h(b)))). fof(n,axiom,~p(f(c)))."
        in
        Engine.protect (fun () -> Engine.ground_step e);
        ignore (checked theory e);
        check
          (e.ground.conflicts > 0 && e.ground.explanations >= 2)
          "congruence explanation missing" );
    ( "a long final congruence explanation is derived once per pair as shared lemmas",
      fun () ->
        List.iter
          (fun goal ->
            let text = tower ~goal 10 in
            let theory, forest = ground_refutation Ground.Forest text in
            let _, short = ground_refutation Ground.Short text in
            let f = checked theory forest and c = checked theory short in
            let fs = fst (Proof.statistics f) and cs = fst (Proof.statistics c) in
            check (fs > 1000) (Printf.sprintf "the forest explanation has only %d steps" fs);
            check (cs < 80) (Printf.sprintf "the shared explanation has %d steps" cs);
            equal forest.ground.shortened 0 "the forest mode shortened";
            equal short.ground.shortened 1 "the conflict was not shortened";
            equal short.ground.fallbacks 0 "the cheapest explanation fell back";
            check (short.ground.saved > 1000) "the saved steps were not counted";
            roundtrip theory c)
          [
            "cnf(n,negated_conjecture,a10!=b10).";
            "cnf(p,axiom,p(a10,c)). cnf(n,negated_conjecture,~p(b10,c)).";
          ] );
    ( "a cheapest explanation past its work bound keeps the forest explanation",
      fun () ->
        let base = !Ground.short_work_base and per_step = !Ground.short_work_per_step in
        Ground.short_work_base := 0;
        Ground.short_work_per_step := 0;
        Fun.protect
          ~finally:(fun () ->
            Ground.short_work_base := base;
            Ground.short_work_per_step := per_step)
          (fun () ->
            let text = tower ~goal:"cnf(n,negated_conjecture,a10!=b10)." 10 in
            let theory, forest = ground_refutation Ground.Forest text in
            let _, short = ground_refutation Ground.Short text in
            let f = checked theory forest and c = checked theory short in
            equal short.ground.shortened 0 "the conflict was shortened past the bound";
            equal short.ground.fallbacks 1 "the bounded search did not fall back";
            equal
              (fst (Proof.statistics c))
              (fst (Proof.statistics f))
              "the fallback is not the forest explanation";
            roundtrip theory c) );
    ( "a conditional long explanation keeps the forest explanation",
      fun () ->
        let text = tower ~base:"a0=b0|r" ~goal:"cnf(n,axiom,a10!=b10). cnf(m,axiom,~r)." 10 in
        let run explanation =
          let theory = Tptp.parse text in
          let e = Engine.create (ground_settings explanation) in
          List.iter (Engine.add_axiom e) (Theory.fixed theory);
          let a = state e in
          List.iter
            (fun (parent : step) ->
              if List.length parent.clause = 2 then (
                Avatar.offer_split a ~guard:(fun () -> ()) parent;
                Engine.protect (fun () -> Engine.split_step e a);
                Engine.deactivate e parent.id))
            (Proof.steps e.proof);
          Engine.protect (fun () -> Engine.synchronize e);
          Engine.protect (fun () -> Engine.ground_step e);
          check (e.ground.conflicts > 0) "the conditional conflict was not found";
          let explained = (e.ground.shortened, e.ground.explanations) in
          Engine.finish e;
          let cert = checked theory e in
          check (cert.avatar <> None) "the branch assumption was lost";
          roundtrip theory cert;
          explained
        in
        let shortened, short_steps = run Ground.Short and _, forest_steps = run Ground.Forest in
        equal shortened 0 "short changed a conditional conflict";
        equal short_steps forest_steps "the conditional explanation changed" );
    ( "a lemma may rewrite inside its own starting premise",
      fun () ->
        (* h(h(t)) -> h(t) by congruence (h(t) = t inside), then h(t) -> t: the lemma starts from
           h(t) = t and its first rewrite uses that same premise inside it. *)
        let saved = !Ground.short_threshold in
        Ground.short_threshold := 0;
        Fun.protect
          ~finally:(fun () -> Ground.short_threshold := saved)
          (fun () ->
            let text = "cnf(p,axiom,h(t)=t). cnf(n,negated_conjecture,h(h(t))!=t)." in
            let theory, e = ground_refutation Ground.Short text in
            let c = checked theory e in
            equal e.ground.shortened 1 "the conflict was not shortened";
            check
              (List.exists
                 (fun (s : step) ->
                   match s.rule with Paramodulate (p, _, _, q, _, _, _) -> p = q | _ -> false)
                 c.steps)
              "no step paramodulates a premise into itself";
            roundtrip theory c) );
    ( "cheapest explanations of random ground conflicts are checked and never longer",
      fun () ->
        let saved = !Ground.short_threshold in
        Ground.short_threshold := 0;
        Fun.protect
          ~finally:(fun () -> Ground.short_threshold := saved)
          (fun () ->
            let conflicts = ref 0 and shorter = ref 0 in
            for seed = 1 to 400 do
              let text = random_ground seed in
              let theory, forest = ground_refutation Ground.Forest text in
              let _, short = ground_refutation Ground.Short text in
              equal (forest.root <> None) (short.root <> None)
                (Printf.sprintf "seed %d: the explanation changed the outcome" seed);
              if forest.root <> None && forest.ground.conflicts > 0 then (
                incr conflicts;
                let f = checked theory forest and c = checked theory short in
                equal short.ground.fallbacks 0 (Printf.sprintf "seed %d: fallback" seed);
                check
                  (fst (Proof.statistics c) <= fst (Proof.statistics f))
                  (Printf.sprintf "seed %d: the cheapest explanation is longer (%d > %d)" seed
                     (fst (Proof.statistics c))
                     (fst (Proof.statistics f)));
                if fst (Proof.statistics c) < fst (Proof.statistics f) then incr shorter;
                roundtrip theory c)
            done;
            check (!conflicts > 40) (Printf.sprintf "only %d random conflicts" !conflicts);
            check (!shorter > 5) (Printf.sprintf "only %d shorter explanations" !shorter)) );
    ( "congruence cycles are explained with earlier edges only",
      fun () ->
        let theory, e = prepare "fof(e,axiom,f(a)=a). fof(g,axiom,a=b). fof(n,axiom,f(f(b))!=b)." in
        Engine.protect (fun () -> Engine.ground_step e);
        ignore (checked theory e) );
    ( "ground consistency does not invent equalities or predicate meanings",
      fun () ->
        let _, e =
          prepare
            "fof(e,axiom,a=b). fof(h,axiom,f(a)=c). fof(n,axiom,f(b)!=d). fof(p,axiom,p(c)). \
             fof(q,axiom,~p(d))."
        in
        Engine.protect (fun () -> Engine.ground_step e);
        equal e.root None "unrelated constants were identified";
        equal e.ground.conflicts 0 "satisfiable ground set has a conflict" );
    ( "explanation intermediates do not suppress later searchable knowledge",
      fun () ->
        let _, e = prepare "cnf(e,axiom,a=b). cnf(p,axiom,p(a))." in
        let clause = [ positive (p [ Fn (Original "b", []) ]) ] in
        let rule = Paramodulate (0, 0, false, 1, 0, [ 0 ], []) in
        let intermediate = Engine.record e clause rule in
        check
          (not
             (Avatar.duplicate e.avatar ~guard:(fun () -> ()) ~variants:true ~except:(-1) [] clause))
          "proof-only node suppressed a live candidate";
        Engine.emit e clause rule;
        check
          (List.exists (fun (s : step) -> s.clause = clause) (Index.all e.retained_index))
          "derived unit was not admitted";
        Engine.collect e;
        check
          (not (List.exists (fun (s : step) -> s.id = intermediate.id) (Proof.steps e.proof)))
          "unused explanation became a permanent root" );
    ( "operation scheduling explores despite a dominating reward",
      fun () ->
        let t = Control.create () in
        let ready = [ Control.Infer; Split; Ground; Synthesize; Enumerate ] in
        for _ = 1 to 128 do
          let selected = Option.get (Control.choose t ready) in
          Control.observe t selected ~gain:(if selected = Infer then 100000 else 0) ~cost:1
        done;
        Array.iter (fun (a : Control.arm) -> check (a.runs >= 3) "ready operation starved") t.arms
    );
    ( "worker phases explore different queue orders with the same policy",
      fun () ->
        let take phase =
          let q = Passive.create ~phase ~policy:Passive.Mixed ~ratio:10 () in
          Passive.add q 0 1 ~unit_weight:10;
          Passive.add q 1 10 ~unit_weight:1;
          Passive.take q
        in
        equal (take 0) (Some 0) "size queue not selected";
        equal (take 1) (Some 1) "unit queue not selected" );
    ( "global clauses stay searchable under branch simplification",
      fun () ->
        List.iter
          (fun (input, settings) ->
            let theory = Tptp.parse input in
            let engine = Engine.create settings in
            let axioms = Theory.fixed theory in
            Engine.add_axiom engine (List.nth axioms 0);
            Engine.finish engine;
            Engine.add_axiom engine (List.nth axioms 1);
            Engine.finish engine;
            let e = Tbl.Int.find engine.avatar.entries 0 in
            check (e.role = Avatar.Candidate && e.lock = None) "branch hid global knowledge";
            check (Index.mem engine.index 0) "global path disappeared from the active index";
            check (Tbl.Int.length engine.avatar.splits > 0) "fixture never used splitting";
            Engine.collect engine;
            Engine.add_axiom engine (List.nth axioms 2);
            Engine.finish engine;
            let cert = Option.get (Engine.certificate engine ~theory:(Theory.name theory)) in
            check (Result.is_ok (Kernel.check theory cert)) "global refutation failed replay")
          [
            ( "fof(old,axiom,p(a)). fof(choice,axiom,(![X]:(a|p(X)))). fof(no,axiom,~p(a)).",
              { Engine.default_config with cnf_mode = Distributive } );
            ( "fof(old,axiom,p(f(a))). fof(choice,axiom,(![X]:(a|f(X)=X))). fof(no,axiom,~p(f(a))).",
              { Engine.default_config with cnf_mode = Distributive } );
          ] );
    ( "ground complements close immediately without waiting for selection or congruence",
      fun () ->
        let theory = Tptp.parse "fof(p,axiom,p(a)). fof(n,axiom,~p(a))." in
        let engine = Engine.create Engine.default_config in
        List.iter (Engine.add_axiom engine) (Theory.fixed theory);
        equal engine.metrics.given 0 "conflict waited for a given clause";
        equal engine.ground.runs 0 "conflict needed a congruence rebuild";
        equal
          (engine.ground.conflicts + engine.contraction.unit_deleted)
          1 "immediate unit conflict was not counted";
        let certificate = Option.get (Engine.certificate engine ~theory:(Theory.name theory)) in
        check (Result.is_ok (Kernel.check theory certificate)) "immediate conflict failed replay" );
    ( "conflict synthesis abstracts Skolem terms without leaking Source symbols",
      fun () ->
        let arena = Source.create (Signature.make ~functions:[] ~predicates:[ ("p", 2) ]) in
        (* Use a declared predicate; generated symbols are never declared as Source functions. *)
        let guide = Guided.create arena in
        let term = Fn (Skolem (0, 0), []) in
        Guided.feedback guide
          [ { id = 0; clause = [ positive (p [ term; term ]) ]; rule = Component 0 } ];
        check
          (guide.metrics.constrained > 0 || guide.metrics.unique > 0)
          "conflict produced no proposals";
        Hashtbl.iter
          (fun _ (proposal : Guided.proposal) ->
            check
              (Wire.source_scoped ~closed:false (Wire.export arena proposal.formula))
              "proposal escaped Source syntax")
          guide.seen );
    ( "extracted cursor enumerates complete finite stages without materialization",
      fun () ->
        let theory = Tptp.parse "fof(t,axiom,$true)." in
        let module N = Natural_checker in
        let cursor = ref N.initial in
        let rec words alphabet depth =
          if depth = 0 then [ [] ]
          else
            List.concat_map
              (fun x -> List.map (fun xs -> x :: xs) (words alphabet (depth - 1)))
              (List.init alphabet Fun.id)
        in
        for stage = 0 to 3 do
          equal !cursor.level stage "stage skipped";
          let observed = ref [] in
          while !cursor.level = stage do
            (match !cursor.pending with (word, 0) :: _ -> observed := word :: !observed | _ -> ());
            cursor := N.tick (Theory.manifest theory) !cursor;
            equal !cursor.witness None "empty theory was refuted"
          done;
          equal (List.rev !observed)
            (List.concat_map (words (stage + 1)) (List.init (stage + 1) Fun.id))
            "frontier lost a word"
        done );
    ( "extracted cursor accepts only checked natural deductions",
      fun () ->
        let theory = Tptp.parse "fof(f,axiom,$false)." in
        let module N = Natural_checker in
        let code =
          N.certificate_code
            {
              N.assumptions =
                [ Wire_types.Pair (Number 0, N.permission_code (N.FixedPermission 0)) ];
              deduction = N.Assume 0;
            }
        in
        let rec encode = function
          | Wire_types.Number n -> [ 0; n ]
          | Pair (x, y) -> (1 :: encode x) @ encode y
        in
        let word = encode code in
        let cursor =
          {
            N.level = List.fold_left max (List.length word) word;
            pending = [ (word, 0) ];
            witness = None;
          }
        in
        let result = N.tick (Theory.manifest theory) cursor in
        equal result.witness (Some code) "valid finite deduction was not accepted";
        match Kernel.check theory (Natural.certificate theory code) with
        | Ok _ -> ()
        | Error e -> failwith e );
    ( "certified reference keeps its cursor after heuristic work ends",
      fun () ->
        let theory = Tptp.parse "fof(p,axiom,p)." in
        let c = { Reference.default_config with seconds = 2.; max_trials = 137 } in
        let report = Reference.run_certified c theory in
        equal report.trials 137 "certified worker stopped early";
        check (report.stage >= 3) "certified worker did not advance";
        equal report.certificate None "consistent input was refuted" );
  ]

let () =
  match Array.to_list Sys.argv with
  | [ _; "--export-rocq"; directory ] -> (
      List.iter
        (fun (name, text) ->
          let theory, engine = conditional text in
          Engine.protect (fun () -> Engine.synchronize engine);
          Engine.protect (fun () -> Engine.ground_step engine);
          Engine.finish engine;
          match Kernel.rocq_document theory (checked theory engine) with
          | Ok text -> Sexp.write_file (Filename.concat directory name) text
          | Error e -> failwith e)
        [ ("SharedRefutation.v", shared_text); ("CongruentRefutation.v", congruent_text) ];
      let theory, engine = prepare joint_text in
      plan_step engine;
      match Kernel.rocq_document theory (checked theory engine) with
      | Ok text -> Sexp.write_file (Filename.concat directory "JointRefutation.v") text
      | Error e -> failwith e)
  | _ -> run tests
