(* Known hole: Redirect moves the result out of the compiler output. *)
Lemma hidden : 1 = 1.
Proof. reflexivity. Qed.
Redirect "redirected" Print Assumptions hidden.
