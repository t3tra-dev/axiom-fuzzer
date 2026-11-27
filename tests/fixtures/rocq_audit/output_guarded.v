(* Known hole in the output: "loop is assumed to be guarded." *)
Unset Guard Checking.
Fixpoint loop (n : nat) : False := loop n.
Set Guard Checking.
Lemma uses_loop : False.
Proof. exact (loop 0). Qed.
Print Assumptions uses_loop.
