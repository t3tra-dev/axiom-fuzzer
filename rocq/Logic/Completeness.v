(* A Henkin construction for exactly the first-order calculus in Deduction.v.
   The construction is used in proofs only. Its choices are classical; the
   executable certificate checker and enumerator remain constructive. *)
From Stdlib Require Import List String Arith.PeanoNat Lia Logic.Classical_Prop Logic.ClassicalChoice.
Require Export AxiomFuzzer.Logic.Deduction.
Require Import AxiomFuzzer.Reference.Encoding AxiomFuzzer.Reference.Enumeration.
Import ListNotations.
Local Open Scope list_scope.
Local Set Implicit Arguments.

Lemma consistent_equiv T U : (forall a, T a <-> U a) -> (consistent T <-> consistent U).
Proof.
  intros E; split; intros C D; apply C.
  - eapply theory_weak; [|exact D]; intros a H; apply E,H.
  - eapply theory_weak; [|exact D]; intros a H; apply E,H.
Qed.
Arguments consistent_equiv {T U} _.
Section Henkin.
Variable T : form -> Prop.
Hypothesis T_closed : forall a, T a -> closed a.
Definition assumptions G a := T a \/ In a G.
Lemma assumptions_add G a f : assumptions (a::G) f <-> extend (assumptions G) a f.
Proof. unfold assumptions,extend; simpl; firstorder congruence. Qed.
Lemma assumptions_monotone G D : incl G D -> forall a, assumptions G a -> assumptions D a.
Proof. unfold assumptions; firstorder. Qed.
Lemma assumptions_bound G a : assumptions G a -> bound a<=maximum (map bound G).
Proof.
  intros [A|A]; [rewrite (T_closed A); lia|]. apply maximum_member,in_map,A.
Qed.
Definition processed f G :=
  (In f G \/ In (neg f) G) /\
  (forall a, f=All a -> In f G \/ exists k, In (neg (instantiate (Var k) a)) G).
Lemma processed_monotone f G D : incl G D -> processed f G -> processed f D.
Proof. unfold processed,incl; firstorder. Qed.
Definition step f G D := incl G D /\
  (consistent (assumptions G) -> consistent (assumptions D)) /\ processed f D.
Lemma step_exists f G : exists D, step f G D.
Proof.
  destruct (classic (consistent (extend (assumptions G) f))) as [Positive|Negative].
  - exists (f::G). split; [intros x In; now right|]. split.
    + intros _; apply (consistent_equiv (assumptions_add G f)),Positive.
    + split; [now left; left|intros; now left; left].
  - assert (NegGood : consistent (assumptions G) -> consistent (assumptions (neg f::G))).
    { intros Good; apply (consistent_equiv (assumptions_add G (neg f))). now apply negative_extension. }
    destruct f as [|p ts|a b|a].
    1-3: match type of NegGood with _ -> consistent (assumptions ?D) => exists D end; split; [intros x In; now right|]; split; [exact NegGood|];
      split; [now right; left|intros body E; discriminate].
    set (D:=neg (All a)::G).
    set (k:=Nat.max (maximum (map bound D)) (bound (All a))).
    exists (neg (instantiate (Var k) a)::D). split; [intros x In; right; now right|]. split.
    + intros Good. apply (consistent_equiv (assumptions_add D (neg (instantiate (Var k) a)))).
      apply witness_extension.
      * apply NegGood,Good.
      * right; now left.
      * intros f A; pose proof (assumptions_bound A); unfold k; lia.
      * unfold k; lia.
    + split; [right; right; now left|]. intros b E; inversion E; subst.
      right; exists k; now left.
Qed.
Lemma steps_exist : exists next : form -> list form -> list form, forall f G, step f G (next f G).
Proof.
  destruct (choice (fun (fg : form * list form) D => step (fst fg) (snd fg) D)
    (fun fg => step_exists (fst fg) (snd fg))) as [next Spec].
  exists (fun f G => next (f,G)); intros f G; exact (Spec (f,G)).
Qed.

Section Chosen.
Variable next : form -> list form -> list form.
Hypothesis next_spec : forall f G, step f G (next f G).
Fixpoint process fs G := match fs with [] => G | f::fs => process fs (next f G) end.
Lemma process_includes fs : forall G, incl G (process fs G).
Proof.
  induction fs; intros G; simpl; [apply incl_refl|]. intros x In; apply IHfs.
  exact (proj1 (next_spec a G) x In).
Qed.
Lemma process_consistent fs : forall G, consistent (assumptions G) -> consistent (assumptions (process fs G)).
Proof. induction fs; simpl; intros G Good; [exact Good|]. apply IHfs,(proj1 (proj2 (next_spec a G))),Good. Qed.
Lemma process_covers fs f : In f fs -> forall G, processed f (process fs G).
Proof.
  induction fs as [|a fs IH]; [contradiction|]. intros [<-|In] G; simpl.
  - apply (processed_monotone (process_includes fs (next a G))). exact (proj2 (proj2 (next_spec a G))).
  - now apply IH.
Qed.
Definition syntax_stage n := flat_map (fun w => match Encoding.decode w with
  | Some c => match form_value c with Some f => [f] | None => [] end | None => [] end) (Enumeration.stage n).
Lemma syntax_enumerated f : exists n, In f (syntax_stage n).
Proof.
  destruct (Enumeration.every_word (Encoding.encode (form_code f))) as [n In].
  exists n; unfold syntax_stage; apply in_flat_map. exists (Encoding.encode (form_code f)); split; [exact In|].
  rewrite Encoding.decode_encode,form_roundtrip; now left.
Qed.
Fixpoint stages n := match n with 0 => [] | S n => process (syntax_stage n) (stages n) end.
Lemma stages_step n : incl (stages n) (stages (S n)).
Proof. apply process_includes. Qed.
Lemma stages_monotone n m : n<=m -> incl (stages n) (stages m).
Proof. induction 1; [apply incl_refl|]. intros x In; apply stages_step,IHle,In. Qed.
Hypothesis initial_consistent : consistent T.
Lemma stages_consistent n : consistent (assumptions (stages n)).
Proof.
  induction n; simpl; [|now apply process_consistent].
  apply (consistent_equiv (T:=T)); [unfold assumptions; simpl; tauto|exact initial_consistent].
Qed.
Definition maximal a := exists n, assumptions (stages n) a.
Lemma maximal_contains a : T a -> maximal a.
Proof. intros A; exists 0; now left. Qed.
Lemma maximal_finite G : Forall maximal G -> exists n, Forall (assumptions (stages n)) G.
Proof.
  induction 1 as [|f G [n A] Rest [m B]].
  - exists 0; constructor.
  - exists (Nat.max n m); constructor.
    + eapply assumptions_monotone; [apply stages_monotone,Nat.le_max_l|exact A].
    + eapply Forall_impl; [|exact B]. intros x H; eapply assumptions_monotone;
        [apply stages_monotone,Nat.le_max_r|exact H].
Qed.
Lemma maximal_consistent : consistent maximal.
Proof.
  intros [G [Allowed D]]. destruct (maximal_finite Allowed) as [n A].
  apply (stages_consistent n); exists G; auto.
Qed.
Lemma maximal_decides a : maximal a \/ maximal (neg a).
Proof.
  destruct (syntax_enumerated a) as [n In].
  destruct (proj1 (process_covers (syntax_stage n) a In (stages n))) as [A|A];
    [left|right]; exists (S n); right; exact A.
Qed.
Lemma maximal_witness a : ~maximal (All a) -> exists k, maximal (neg (instantiate (Var k) a)).
Proof.
  intros NotAll. destruct (syntax_enumerated (All a)) as [n In].
  destruct (proj2 (process_covers (syntax_stage n) (All a) In (stages n)) a eq_refl) as [A|[k A]].
  - exfalso; apply NotAll; exists (S n); right; exact A.
  - exists k,(S n); right; exact A.
Qed.
Lemma maximal_closed a : maximal ⊢T a -> maximal a.
Proof.
  intros D. destruct (maximal_decides a) as [A|Negative]; [exact A|].
  exfalso; apply maximal_consistent; eapply theory_imp_elim; [apply theory_ctx,Negative|exact D].
Qed.
Lemma maximal_not_bottom : ~ maximal Bot.
Proof. intros H; apply maximal_consistent,theory_ctx,H. Qed.
Lemma maximal_imp a b : maximal (Imp a b) <-> (maximal a -> maximal b).
Proof.
  split.
  - intros Implication A. apply maximal_closed; eapply theory_imp_elim; apply theory_ctx; eauto.
  - intros H. apply maximal_closed,theory_imp_intro.
    destruct (maximal_decides a) as [A|Negative].
    + apply theory_ctx; left; apply H,A.
    + apply theory_explosion. eapply theory_imp_elim; apply theory_ctx;
        [left; exact Negative|now right].
Qed.
Lemma maximal_all a t : maximal (All a) -> maximal (instantiate t a).
Proof.
  intros A; apply maximal_closed. exists [All a]; split; [now repeat constructor|].
  apply AllE,Ctx; now left.
Qed.
Definition term_predicate p ts := maximal (Atom p ts).
Lemma term_evaluation rho t : eval Fun rho t=subst_term rho t.
Proof. reflexivity.
Qed.
Lemma truth_lemma a : forall rho, holds Fun term_predicate rho a <-> maximal (subst rho a).
Proof.
  induction a; intros rho; simpl.
  - split; [contradiction|apply maximal_not_bottom].
  - unfold term_predicate. assert (E : map (eval Fun rho) arguments=map (subst_term rho) arguments).
    { apply map_ext; intros t; apply term_evaluation. } now rewrite E.
  - rewrite IHa1,IHa2; symmetry; apply maximal_imp.
  - split.
    + intros H. destruct (classic (maximal (All (subst (up rho) a)))) as [A|No]; [exact A|].
      destruct (maximal_witness No) as [k Negative]. exfalso; apply maximal_consistent.
      eapply theory_imp_elim; [apply theory_ctx,Negative|]. apply theory_ctx.
      rewrite instantiate_up. apply IHa,H.
    + intros A t. apply IHa. rewrite <- instantiate_up. apply maximal_all,A.
Qed.
Theorem constructed_model : forall a, T a -> holds Fun term_predicate Var a.
Proof. intros a A; apply truth_lemma; rewrite subst_id; now apply maximal_contains. Qed.
End Chosen.

Theorem model_existence : consistent T -> exists predicates : option string -> list term -> Prop,
  forall a, T a -> holds Fun predicates Var a.
Proof.
  intros Good. destruct steps_exist as [next Spec]. exists (term_predicate next).
  apply constructed_model; assumption.
Qed.
End Henkin.

Theorem refutation_complete T : (forall a, T a -> closed a) ->
  (forall (U : Type) (functions : string -> list U -> U) predicates rho,
    (forall a, T a -> holds functions predicates rho a) -> False) -> T ⊢T Bot.
Proof.
  intros Closed NoModel; apply NNPP; intros Consistent.
  destruct (model_existence Closed Consistent) as [predicates Model].
  exact (NoModel term Fun predicates Var Model).
Qed.
Print Assumptions refutation_complete.
