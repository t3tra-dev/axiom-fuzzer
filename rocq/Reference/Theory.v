(* Recursively enumerable Source theories. An observation is total; None is a
   quiet stage. A certificate stores a finite stage, never an axiom oracle. *)
From Stdlib Require Import List String Ascii Bool Arith.PeanoNat Lia.
Require Import AxiomFuzzer.Reference.Certificate AxiomFuzzer.Source.Standard
  AxiomFuzzer.Logic.Deduction AxiomFuzzer.Logic.Completeness.
Import ListNotations.
Local Open Scope list_scope.
Local Set Implicit Arguments.

(* Least-significant bit first, with the empty string representing zero.
   Division halves the value at each recursive call, including after extraction. *)
Fixpoint index_bits fuel n := match fuel,n with
  | S fuel,S _ => String (if n =? 2 * Nat.div2 n then "0"%char else "1"%char)
      (index_bits fuel (Nat.div2 n))
  | _,_ => EmptyString end.
Definition index_text n := index_bits n n.
Fixpoint read_bits text : option nat := match text with
  | EmptyString => Some 0
  | String bit rest => match read_bits rest with
      | Some n => if Ascii.eqb bit "0"%char then Some (2*n)
                  else if Ascii.eqb bit "1"%char then Some (S(2*n)) else None
      | None => None end end.
Definition index_value text := match read_bits text with
  | Some n => if String.eqb (index_text n) text then Some n else None
  | None => None end.
Lemma div2_cases : forall n, n=2*Nat.div2 n \/ n=S(2*Nat.div2 n).
Proof. fix IH 1; intros [|[|n]]; cbn [Nat.div2]; [now left|now right|specialize (IH n); lia]. Qed.
Lemma read_index_bits fuel : forall n, n<=fuel -> read_bits (index_bits fuel n)=Some n.
Proof.
  induction fuel; intros [|n] Bound; try lia; try reflexivity.
  cbn [index_bits].
  destruct (Nat.eqb_spec (S n) (2 * Nat.div2 (S n))) as [E|E]; cbn [read_bits];
    rewrite IHfuel by (apply Nat.div2_decr; lia);
    cbn [Ascii.eqb Bool.eqb]; pose proof (div2_cases (S n)); f_equal; lia.
Qed.
Lemma index_roundtrip n : index_value (index_text n)=Some n.
Proof.
  unfold index_value,index_text at 1. rewrite read_index_bits by lia.
  now rewrite String.eqb_refl.
Qed.

Definition enumeration_name := "enumerated"%string.
Definition enumerated_check (step : nat -> option Validation.formula) data f :=
  match index_value data with
  | Some n => match step n with Some a => Validation.equivalent a f | None => false end
  | None => false end.
Definition enumerated_manifest name revision step : Validation.theory :=
  {| Validation.theory_name:=name; Validation.unrestricted_signature:=true;
     Validation.function_symbols:=[]; Validation.predicate_symbols:=[];
     Validation.fixed_axioms:=[];
     Validation.allowed_schemas:=[Validation.RegisteredSchema enumeration_name revision];
     Validation.registered_check:=fun n r data f =>
       String.eqb n enumeration_name && String.eqb r revision && enumerated_check step data f |}.

(* The intended theory contains exactly emitted sentences and logical equality
   axioms. Boolean equivalences accepted by the implementation are derived below. *)
Definition emitted (step : nat -> option Validation.formula) f := exists n, step n=Some f.
Definition axiom_theory (axioms : Validation.formula -> Prop) a := Standard.equality_theory a \/
  exists f, axioms f /\ a=Standard.source_sentence f.
Definition emitted_theory step := axiom_theory (emitted step).
Definition enumerates (axioms : Validation.formula -> Prop) step :=
  forall f, axioms f <-> emitted step f.
Definition well_formed (step : nat -> option Validation.formula) := forall n f, step n=Some f -> Language.formula_scoped 0 true f=true.
Lemma emitted_closed step a : emitted_theory step a -> Syntax.closed a.
Proof. intros [[f [_ ->]]|[f [_ ->]]]; apply Syntax.close_closed. Qed.

Print Assumptions index_roundtrip.

Section Presentation.
Variable name revision : string.
Variable step : nat -> option Validation.formula.
Local Abbreviation manifest := (enumerated_manifest name revision step).
Lemma emitted_authorized : well_formed step -> forall f, emitted step f -> Validation.authorized manifest f.
Proof.
  intros Formed f [n Output].
  eapply (Validation.AuthorizedRegistered manifest enumeration_name revision (index_text n) f).
  - now left.
  - exact (Formed n f Output).
  - reflexivity.
  - cbn [enumerated_manifest Validation.registered_check]. rewrite !String.eqb_refl; simpl.
    unfold enumerated_check; now rewrite index_roundtrip,Output,Validation.equivalent_refl.
Qed.
Lemma emitted_in_standard : well_formed step -> forall a,
  emitted_theory step a -> Standard.source_theory manifest a.
Proof.
  intros Formed a [Equality|[f [Emitted ->]]]; [now left|].
  right; exists f; split; [now apply emitted_authorized|reflexivity].
Qed.

Lemma authorized_emitted_model {U} (functions : string -> list U -> U) predicates rho :
  (forall a, emitted_theory step a -> Syntax.holds functions predicates rho a) ->
  forall f, Validation.authorized manifest f ->
  Syntax.holds functions predicates rho (Standard.source_sentence f).
Proof.
  intros Model f Allowed.
  assert (Equality : forall a, Standard.equality_theory a -> Syntax.holds functions predicates rho a)
    by (intros a A; apply Model; now left).
  induction Allowed as [ax In|key kind variables fresh phi result In Builtin Signature Expansion|
    n r data f In Scope Signature Checked|a b Allowed IH Equivalent].
  - contradiction.
  - destruct In as [E|[]]; subst key; discriminate.
  - cbn [enumerated_manifest Validation.registered_check] in Checked. apply andb_true_iff in Checked as [_ Checked].
    unfold enumerated_check in Checked.
    destruct (index_value data) as [k|]; [|discriminate].
    destruct (step k) as [a|] eqn:Output; [|discriminate].
    eapply (@Standard.equivalent_sentence U functions predicates rho Equality a f rho Checked).
    apply Model; right; exists a; split; [now exists k|reflexivity].
  - exact (@Standard.equivalent_sentence U functions predicates rho Equality a b rho Equivalent IH).
Qed.

Theorem standard_is_emitted : Standard.source_theory manifest ⊢T Bot -> emitted_theory step ⊢T Bot.
Proof.
  intros [G [Allowed Derivation]]. apply refutation_complete; [apply emitted_closed|].
  intros U functions predicates rho Model.
  apply (Deduction.soundness functions predicates Derivation rho).
  intros a In. pose proof (proj1 (Forall_forall _ _) Allowed a In) as A.
  destruct A as [Equality|[f [Authorized ->]]]; [apply Model; now left|].
  now apply authorized_emitted_model.
Qed.
Theorem emitted_is_standard : well_formed step ->
  emitted_theory step ⊢T Bot -> Standard.source_theory manifest ⊢T Bot.
Proof. intros Formed; apply Deduction.theory_weak; now apply emitted_in_standard. Qed.
Theorem enumeration_check_sound c : direct_check manifest c=true -> emitted_theory step ⊢T Bot.
Proof. intros Checked; apply standard_is_emitted; now apply direct_sound in Checked. Qed.
Theorem enumeration_check_complete : well_formed step ->
  emitted_theory step ⊢T Bot -> exists c, direct_check manifest c=true.
Proof. intros Formed Refuted; apply direct_complete,emitted_is_standard; assumption. Qed.
Theorem enumeration_check_iff : well_formed step ->
  ((exists c, direct_check manifest c=true) <-> emitted_theory step ⊢T Bot).
Proof. intros Formed; split; [intros [c C]; now apply enumeration_check_sound in C|now apply enumeration_check_complete]. Qed.
Theorem enumeration_eventually_found : well_formed step -> emitted_theory step ⊢T Bot ->
  exists n c, reference_run manifest n=Some c /\ direct_check manifest c=true.
Proof.
  intros Formed Refuted. apply emitted_is_standard in Refuted; [|exact Formed].
  destruct (reference_run_complete Refuted) as [n [c Run]].
  exists n,c; split; [exact Run|now apply reference_run_sound in Run].
Qed.
End Presentation.

(* This interface asks for an enumeration of axioms, not decidable membership
   of the axiom set, certificate existence, or fairness of a heuristic engine. *)
Theorem recursively_axiomatized_complete name revision axioms step :
  enumerates axioms step -> well_formed step ->
  (axiom_theory axioms ⊢T Bot <->
   exists n c, reference_run (enumerated_manifest name revision step) n=Some c /\
     direct_check (enumerated_manifest name revision step) c=true).
Proof.
  intros Presents Formed.
  assert (Agree : forall a, axiom_theory axioms a <-> emitted_theory step a).
  { intros a; unfold emitted_theory,axiom_theory; split;
      intros [Eq|[f [Ax ->]]]; try (now left); right; exists f; split; try reflexivity;
      [apply Presents|apply Presents]; assumption. }
  split.
  - intros Refuted; apply enumeration_eventually_found; [exact Formed|].
    eapply Deduction.theory_weak; [|exact Refuted]; intros a A; apply Agree,A.
  - intros [n [c [_ Checked]]]. apply enumeration_check_sound in Checked.
    eapply Deduction.theory_weak; [|exact Checked]; intros a A; apply Agree,A.
Qed.

Module Kernel (Order : AxiomFuzzer.Wire.Refutation.WireOrder
  with Definition function_name := string with Definition predicate_name := string).
Module Checked := Certificate.Kernel Order.
Theorem check_iff_enumerated name revision step visit limit budget encode_variable decode_function decode_predicate :
  well_formed step ->
  ((exists c, Checked.check visit limit budget encode_variable decode_function decode_predicate
      (enumerated_manifest name revision step) c=true) <-> emitted_theory step ⊢T Bot).
Proof.
  intros Formed; rewrite Checked.check_iff_standard; split;
    [apply standard_is_emitted|now apply emitted_is_standard].
Qed.
End Kernel.
Print Assumptions enumeration_check_sound.
Print Assumptions enumeration_check_complete.
Print Assumptions enumeration_eventually_found.
Print Assumptions recursively_axiomatized_complete.
