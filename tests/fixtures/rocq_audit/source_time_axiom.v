(* Known hole: Time runs the axiom declaration after it. *)
Time Axiom bad : False.
Lemma uses_time : 1 = 2.
Proof. destruct bad. Qed.
