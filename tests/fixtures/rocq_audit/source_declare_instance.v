(* Known hole: Declare Instance assumes an instance without a definition. *)
Class Bad := { bad_false : False }.
#[local] Declare Instance bad_instance : Bad.
Lemma uses_instance : 1 = 2.
Proof. destruct bad_false. Qed.
