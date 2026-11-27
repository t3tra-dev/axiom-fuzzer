From Stdlib Require Import List String.
Require Import AxiomFuzzer.Source.Standard AxiomFuzzer.Source.Validation
  AxiomFuzzer.Reference.Encoding AxiomFuzzer.Logic.Deduction AxiomFuzzer.Reference.Certificate.
Import ListNotations.
Local Open Scope list_scope.

Definition false_axiom : axiom :=
  {| axiom_id:=0; axiom_name:="false"%string; axiom_origin:=FixedAxiom "false"%string;
     axiom_formula:=AxiomFuzzer.Source.Language.SBot |}.
Definition false_theory : Validation.theory :=
  {| theory_name:="false"%string; unrestricted_signature:=false; function_symbols:=nil; predicate_symbols:=nil;
     fixed_axioms:=cons false_axiom nil; allowed_schemas:=nil;
     registered_check:=fun _ _ _ _ => false |}.
Definition false_certificate := certificate_code
  {| assumptions:=cons (Pair (Number 0) (permission_code (FixedPermission 0))) nil;
     deduction:=Assume 0 |}.
Example false_accepted : direct_check false_theory false_certificate=true.
Proof. vm_compute; reflexivity. Qed.
Example unauthorized_rejected : direct_check
  {| theory_name:="empty"%string; unrestricted_signature:=false; function_symbols:=nil; predicate_symbols:=nil;
     fixed_axioms:=nil; allowed_schemas:=nil; registered_check:=fun _ _ _ _ => false |}
  false_certificate=false.
Proof. vm_compute; reflexivity. Qed.
Theorem false_standard : source_theory false_theory ⊢T Bot.
Proof. apply (@direct_sound false_theory false_certificate), false_accepted. Qed.
Theorem false_eventually_discovered : exists n c, reference_search false_theory n=Some c.
Proof. apply reference_complete, false_standard. Qed.
Example concrete_finite_search :
  Enumeration.search (fun _ => Some tt) (fun _ _ => true) 0=Some tt.
Proof. reflexivity. Qed.
Print Assumptions false_standard.
Print Assumptions false_eventually_discovered.

(* Instantiate the ordering interface with its proved finite-ranking instance
   before auditing the four end-to-end results. *)
Module Ranking.
Definition literals : list (AxiomFuzzer.Wire.Syntax.wire_literal string string) := nil.
End Ranking.
Module Order := AxiomFuzzer.Source.Kernel.RankedOrder Ranking.
Module StandardConnection := AxiomFuzzer.Source.Standard.Connection Order.
Module Complete := AxiomFuzzer.Reference.Certificate.Kernel Order.
Print Assumptions StandardConnection.refutation_is_standard.
Print Assumptions StandardConnection.avatar_check_is_standard.
Print Assumptions Complete.check_iff_standard.
Print Assumptions Complete.accepted_eventually_found.

Require Import AxiomFuzzer.Reference.Theory.
Definition sparse_axioms n : option Validation.formula :=
  if Nat.eqb n 7 then Some Language.SBot else None.
Lemma sparse_well_formed : well_formed sparse_axioms.
Proof.
  intros n f; unfold sparse_axioms; destruct (Nat.eqb n 7); intros E;
    inversion E; reflexivity.
Qed.
Definition sparse_theory := enumerated_manifest "sparse"%string "current"%string sparse_axioms.
Definition sparse_certificate := certificate_code
  {| assumptions:=[Pair (Number 0) (permission_code
       (RegisteredPermission enumeration_name "current"%string (index_text 7) Language.SBot))];
     deduction:=Assume 0 |}.
Example sparse_accepted : direct_check sparse_theory sparse_certificate=true.
Proof. vm_compute; reflexivity. Qed.
Example quiet_stage_rejected : enumerated_check sparse_axioms (index_text 6) Language.SBot=false.
Proof. vm_compute; reflexivity. Qed.
Theorem sparse_refuted : emitted_theory sparse_axioms ⊢T Bot.
Proof. apply (enumeration_check_sound "sparse"%string "current"%string sparse_axioms sparse_certificate),sparse_accepted. Qed.
Theorem sparse_eventually_discovered : exists n c,
  reference_run sparse_theory n=Some c /\ direct_check sparse_theory c=true.
Proof. apply enumeration_eventually_found; [exact sparse_well_formed|exact sparse_refuted]. Qed.
Module Enumerated := Theory.Kernel Order.
Print Assumptions Enumerated.check_iff_enumerated.
