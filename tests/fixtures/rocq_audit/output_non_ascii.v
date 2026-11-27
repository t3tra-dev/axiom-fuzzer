(* Known hole in the output: Rocq prints this axiom as "λ : False". *)
Axiom λ : False.
Lemma uses_unicode : 1 = 2.
Proof. destruct λ. Qed.
Print Assumptions uses_unicode.
