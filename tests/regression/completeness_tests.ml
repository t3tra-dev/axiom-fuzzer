open Axiom_fuzzer
open Test_support

(* The production heuristic configuration without the reference Domain. Each
   input is a tiny unsatisfiable set on which this search once saturated
   ("bounded formula/clauses exhausted; consistency not established") instead of finding a refutation. *)
let production =
  {
    Scheduler.default_config with
    reference = false;
    engine = { Engine.default_config with limits = { Engine.default_limits with seconds = 5. } };
  }

let refutes name text =
  ( name,
    fun () ->
      let t = Tptp.parse text in
      let r = Scheduler.run production t in
      match r.certificate with
      | None -> failwith ("no refutation: " ^ r.reason)
      | Some c ->
          equal r.proof_source "heuristic:0" "refutation did not come from the heuristic worker";
          check (Result.is_ok (Kernel.check t c)) "refutation failed replay" )

(* One member alone on one worker, under an equivalence rule. *)
let member ?(equivalence = Contraction.Redundant) name text =
  let t = Tptp.parse text in
  let config =
    {
      production with
      portfolio = Strategy.Workers [ Strategy.of_name name ];
      engine = { production.engine with equivalence };
    }
  in
  (t, Scheduler.run config t)

(* A minimal case found by completeness fuzzing (min-binary-h042): k(a) <-> k(X) and p(f(X)) <-> k(h(X))
   are equivalences. The legacy rule rewrote the units p(f(g(b,c))) and ~k(h(a)) with them and
   retired the originals, although a unit is never smaller than the inverse instance that would
   make its deletion redundant; h042 then emptied Passive without a refutation. *)
let binary_h042 =
  "cnf(c0,axiom,(~k(a) | k(X))). cnf(c1,axiom,(k(a) | ~k(X))). cnf(c4,axiom,(~p(f(X)) | k(h(X)))). \
   cnf(c5,axiom,(p(f(X)) | ~k(h(X)))). cnf(c8,axiom,(p(f(g(b,c))))). cnf(c10,axiom,(~k(h(a))))."

let equivalence_tests =
  List.map
    (fun name ->
      ( Printf.sprintf "an equivalence keeps the units %s needs (min-binary-h042)" name,
        fun () ->
          let t, r = member name binary_h042 in
          match r.certificate with
          | None -> failwith ("no refutation: " ^ r.reason)
          | Some c -> check (Result.is_ok (Kernel.check t c)) "refutation failed replay" ))
    [ "production"; "e208"; "calc:e"; "h042" ]
  @ [
      ( "the legacy equivalence rule empties h042's Passive on min-binary-h042",
        fun () ->
          let _, r = member ~equivalence:Contraction.Legacy "h042" binary_h042 in
          check (r.certificate = None) "the legacy rule refuted the audit case";
          check
            (String.starts_with ~prefix:"bounded formula/clauses exhausted" r.reason)
            ("the legacy rule did not exhaust Passive: " ^ r.reason) );
    ]

let tests =
  equivalence_tests
  @ [
      (* X=a | Y=b and c!=d: the factor b=a rewrites the input to X=a | Y=a, whose
       factor X=a was deleted by set subsumption (X=a | Y=a "subsumed" X=a and
       every clause containing an instance of X=a). *)
      refutes "unorientable equations keep their factor (fof)"
        "fof(trivial,axiom,(![X,Y]:(X=a | Y=b))). fof(distinct,axiom,c!=d).";
      refutes "unorientable equations keep their factor (cnf)"
        "cnf(trivial,axiom,(X=a | Y=b)). cnf(distinct,axiom,c!=d).";
      (* Minimized from the differential harness. Both orientations of one
       equation collapsed onto the factor X=d through the symmetric match. *)
      refutes "a symmetric equation pair keeps its factor"
        "cnf(c0,axiom,(X=d | d=X)). cnf(c1,axiom,p(a)). cnf(c2,axiom,~p(d)).";
      refutes "a three-literal equation clause keeps its factor"
        "cnf(c0,axiom,(X=d | Y=X | d=X)). cnf(c1,axiom,(p(a) | p(b))). cnf(c2,axiom,~p(d)).";
      refutes "a nonground factor under a function symbol is kept"
        "cnf(c0,axiom,(X=f(Y) | f(Z)=X)). cnf(c1,axiom,a!=b).";
    ]

let () = run tests
