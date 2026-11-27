(* Standard classical first-order logic, with equality axioms. *)
From Stdlib Require Import List Logic.FunctionalExtensionality Logic.PropExtensionality
  Logic.ProofIrrelevance Logic.ClassicalChoice.
Require Import AxiomFuzzer.Source.Language.
Module Models.
Import ListNotations.

Section RelationalModel.
Context {F P U : Type}.
Variable functions : F -> list U -> U.
Variable predicates : P -> list U -> Prop.
Variable relation : U -> U -> Prop.
Hypothesis reflexive : forall x, relation x x.
Hypothesis symmetric : forall x y, relation x y -> relation y x.
Hypothesis transitive : forall x y z, relation x y -> relation y z -> relation x z.
Hypothesis function_congruence : forall f xs ys, Forall2 relation xs ys -> relation (functions f xs) (functions f ys).
Hypothesis predicate_congruence : forall p xs ys, Forall2 relation xs ys -> (predicates p xs <-> predicates p ys).
Local Abbreviation eval := (source_eval functions).

Fixpoint relational_holds bound free (f : source_formula F P) := match f with
  | STop => True | SBot => False
  | SPred p ts => predicates p (map (eval bound free) ts)
  | SEq x y => relation (eval bound free x) (eval bound free y)
  | SNeg f => ~ relational_holds bound free f
  | SConj fs => (fix all fs := match fs with [] => True | f::fs => relational_holds bound free f /\ all fs end) fs
  | SDisj fs => (fix some fs := match fs with [] => False | f::fs => relational_holds bound free f \/ some fs end) fs
  | SAll f => forall x, relational_holds (push x bound) free f
  | SEx f => exists x, relational_holds (push x bound) free f
  end.

Definition quotient := { c : U -> Prop | exists x, c=relation x }.
Definition inject x : quotient := exist _ (relation x) (ex_intro _ x eq_refl).
Lemma quotient_equal (a b : quotient) : proj1_sig a=proj1_sig b -> a=b.
Proof. destruct a,b; simpl; intros H; subst. f_equal; apply proof_irrelevance. Qed.
Lemma inject_equal x y : inject x=inject y <-> relation x y.
Proof.
  split.
  - intros H. apply (f_equal (@proj1_sig _ _)) in H; simpl in H.
    rewrite H; apply reflexive.
  - intros H. apply quotient_equal; simpl. apply functional_extensionality; intros z.
    apply propositional_extensionality; split; intros R.
    + eapply transitive; [apply symmetric; exact H|exact R].
    + eapply transitive; eauto.
Qed.
Lemma quotient_surjective q : exists x, inject x=q.
Proof. destruct q as [c [x ->]]. exists x; apply quotient_equal; reflexivity. Qed.
Lemma representatives : exists representative : quotient -> U, forall q, inject (representative q)=q.
Proof. exact (choice (fun q x => inject x=q) quotient_surjective). Qed.

Section Chosen.
Variable representative : quotient -> U.
Hypothesis representative_correct : forall q, inject (representative q)=q.
Definition quotient_function f qs := inject (functions f (map representative qs)).
Definition quotient_predicate p qs := predicates p (map representative qs).
Lemma representatives_related xs : Forall2 relation (map representative (map inject xs)) xs.
Proof.
  induction xs; simpl; constructor; [|exact IHxs]. apply inject_equal, representative_correct.
Qed.
Lemma quotient_function_inject f xs : quotient_function f (map inject xs)=inject (functions f xs).
Proof. apply inject_equal, function_congruence, representatives_related. Qed.
Lemma quotient_predicate_inject p xs : quotient_predicate p (map inject xs) <-> predicates p xs.
Proof. apply predicate_congruence, representatives_related. Qed.
Lemma quotient_eval : forall t bound free,
  source_eval quotient_function (fun i => inject (bound i)) (fun i => inject (free i)) t=inject (eval bound free t).
Proof.
  fix IH 1. intros [i|i|f ts] bound free; simpl; try reflexivity.
  rewrite <- quotient_function_inject.
  f_equal. induction ts as [|t ts HT]; simpl; [reflexivity|]. now rewrite IH, HT.
Qed.
Lemma inject_push x bound : (fun i => inject (push x bound i))=push (inject x) (fun i => inject (bound i)).
Proof. apply functional_extensionality; intros [|i]; reflexivity. Qed.
Lemma quotient_holds : forall f bound free,
  source_holds quotient_function quotient_predicate (fun i => inject (bound i)) (fun i => inject (free i)) f <->
  relational_holds bound free f.
Proof.
  fix IH 1. intros [| |p ts|x y|f|fs|fs|f|f] bound free; simpl; try tauto.
  - assert (Args : map (source_eval quotient_function (fun i => inject (bound i)) (fun i => inject (free i))) ts =
        map inject (map (eval bound free) ts)).
    { induction ts as [|t ts HT]; simpl; [reflexivity|]. now rewrite quotient_eval, HT. }
    rewrite Args; apply quotient_predicate_inject.
  - rewrite !quotient_eval; apply inject_equal.
  - now rewrite IH.
  - induction fs as [|f fs HT]; simpl; [tauto|]. now rewrite IH, HT.
  - induction fs as [|f fs HT]; simpl; [tauto|]. now rewrite IH, HT.
  - split; intros H x.
    + apply (IH f (push x bound) free). rewrite inject_push. apply (H (inject x)).
    + destruct (quotient_surjective x) as [y <-]. rewrite <- inject_push. apply (IH f (push y bound) free). exact (H y).
  - split; intros [x H].
    + destruct (quotient_surjective x) as [y <-]. exists y; apply (IH f (push y bound) free); rewrite inject_push; exact H.
    + exists (inject x). rewrite <- inject_push. apply (IH f (push x bound) free); exact H.
Qed.
End Chosen.

Theorem quotient_model (default : U) (axioms : list (source_formula F P)) :
  Forall (relational_holds (fun _ => default) (fun _ => default)) axioms ->
  exists (Q : Type) (d : Q) (f : F -> list Q -> Q) (p : P -> list Q -> Prop),
    Forall (source_holds f p (fun _ => d) (fun _ => d)) axioms.
Proof.
  intros Model. destruct representatives as [representative Correct].
  exists quotient,(inject default),(quotient_function representative),(quotient_predicate representative).
  eapply Forall_impl; [|exact Model]. intros ax H. apply (quotient_holds representative Correct); exact H.
Qed.
End RelationalModel.
Print Assumptions quotient_model.

End Models.

Require Import AxiomFuzzer.Source.Validation AxiomFuzzer.Source.Kernel.
Require Import AxiomFuzzer.Source.Refutation AxiomFuzzer.Wire.Refutation.
Require Export AxiomFuzzer.Logic.Completeness.
From Stdlib Require Import String List Bool Arith.PeanoNat Lia Logic.Classical_Prop.
Import ListNotations Models.
Local Open Scope list_scope.
Local Set Implicit Arguments.

Definition named_function := Fun.
Definition named_predicate p ts := Atom (Some p) ts.
Definition default_term := Fun EmptyString [].
Definition equal x y := Atom None [x;y].
Definition conjunction a b := neg (Imp a (neg b)).
Definition disjunction a b := Imp (neg a) b.
Definition truth := Imp Bot Bot.
Fixpoint translate_term depth (t : source_term string) : Syntax.term := match t with
  | SBound i => if i <? depth then Var i else default_term
  | SFree _ => default_term
  | SApply f ts => Fun f (map (translate_term depth) ts) end.
Fixpoint translate depth (f : source_formula string string) : form := match f with
  | STop => truth | SBot => Bot
  | SPred p ts => named_predicate p (map (translate_term depth) ts)
  | SEq x y => equal (translate_term depth x) (translate_term depth y)
  | SNeg f => neg (translate depth f)
  | SConj fs => (fix all fs := match fs with [] => truth | f::fs => conjunction (translate depth f) (all fs) end) fs
  | SDisj fs => (fix some fs := match fs with [] => Bot | f::fs => disjunction (translate depth f) (some fs) end) fs
  | SAll f => All (translate (S depth) f)
  | SEx f => neg (All (neg (translate (S depth) f))) end.
Definition source_sentence f := close (translate 0 f).

Fixpoint equal_arguments (xs ys : list Syntax.term) := match xs,ys with
  | [],[] => truth
  | x::xs,y::ys => conjunction (equal x y) (equal_arguments xs ys)
  | _,_ => Bot end.
Inductive equality_axiom : form -> Prop :=
  | EqualityReflexive t : equality_axiom (equal t t)
  | EqualitySymmetric t u : equality_axiom (Imp (equal t u) (equal u t))
  | EqualityTransitive t u v : equality_axiom (Imp (equal t u) (Imp (equal u v) (equal t v)))
  | EqualityFunction f xs ys : equality_axiom (Imp (equal_arguments xs ys) (equal (Fun f xs) (Fun f ys)))
  | EqualityPredicate p xs ys : equality_axiom (Imp (equal_arguments xs ys) (Imp (named_predicate p xs) (named_predicate p ys))).
Definition equality_theory f := exists a, equality_axiom a /\ f=close a.
Definition source_theory (t : Validation.theory) a :=
  equality_theory a \/ exists f, authorized t f /\ a=source_sentence f.
Lemma source_theory_closed t a : source_theory t a -> closed a.
Proof. intros [[f [_ ->]]|[f [_ ->]]]; apply close_closed. Qed.

Section Interpretation.
Context {U : Type}.
Variable functions : string -> list U -> U.
Variable predicates : option string -> list U -> Prop.
Definition original_predicate p := predicates (Some p).
Definition original_equal x y := predicates None [x;y].
Definition default := functions EmptyString [].
Definition environment depth rho i := if i <? depth then rho i else default.
Lemma environment_push depth rho x : environment (S depth) (Syntax.push x rho)=Language.push x (environment depth rho).
Proof. apply functional_extensionality; intros [|i]; reflexivity. Qed.
Lemma translate_term_eval : forall t depth rho,
  eval functions rho (translate_term depth t)=source_eval functions (environment depth rho) (fun _ => default) t.
Proof.
  fix IH 1; intros [i|i|f ts] depth rho; simpl.
  - unfold environment; destruct (i <? depth); reflexivity.
  - reflexivity.
  - rewrite map_map; f_equal; induction ts as [|t ts HT]; simpl; [reflexivity|].
    now rewrite IH, HT.
Qed.
Lemma classical_conjunction (a b : Prop) : ((a -> b -> False) -> False) <-> a /\ b.
Proof. destruct (classic a),(classic b); tauto. Qed.
Lemma classical_disjunction (a b : Prop) : ((~a) -> b) <-> a \/ b.
Proof. destruct (classic a),(classic b); tauto. Qed.
Lemma translate_holds : forall f depth rho,
  holds functions predicates rho (translate depth f) <->
  relational_holds functions original_predicate original_equal (environment depth rho) (fun _ => default) f.
Proof.
  fix IH 1; intros [| |p ts|x y|f|fs|fs|f|f] depth rho; cbn [translate relational_holds].
  - cbn [truth holds]; tauto.
  - reflexivity.
  - cbn [named_predicate holds]; rewrite map_map.
    assert (E : map (fun t => eval functions rho (translate_term depth t)) ts =
      map (source_eval functions (environment depth rho) (fun _ => default)) ts)
      by (apply map_ext; intros t; apply translate_term_eval). now rewrite E.
  - cbn [equal holds map original_equal]; now rewrite !translate_term_eval.
  - cbn [neg holds]; now rewrite IH.
  - induction fs; cbn [holds conjunction truth neg]; [tauto|].
    rewrite IH,IHfs; apply classical_conjunction.
  - induction fs; cbn [holds disjunction neg]; [tauto|].
    rewrite IH,IHfs; apply classical_disjunction.
  - cbn [holds]; setoid_rewrite IH; setoid_rewrite environment_push; reflexivity.
  - cbn [holds neg]; setoid_rewrite IH; setoid_rewrite environment_push.
    split; [intros H; apply NNPP; intros No; apply H; intros x Hx; apply No; now exists x|firstorder].
Qed.
Lemma equal_arguments_sat rho xs ys : holds functions predicates rho (equal_arguments xs ys) <->
  Forall2 original_equal (map (eval functions rho) xs) (map (eval functions rho) ys).
Proof.
  revert ys; induction xs as [|x xs IH]; intros [|y ys]; cbn [equal_arguments holds truth conjunction neg equal map].
  - split; [intros _; constructor|tauto].
  - split; [tauto|inversion 1].
  - split; [tauto|inversion 1].
  - rewrite classical_conjunction,IH; split; [intros [H R]; now constructor|inversion 1; auto].
Qed.
Lemma represent_list (xs : list U) : exists rho ts, map (eval functions rho) ts=xs.
Proof.
  induction xs as [|x xs [rho [ts E]]].
  - exists (fun _ => default),[]; reflexivity.
  - exists (Syntax.push x rho),(Var 0::map shift_term ts); simpl.
    rewrite map_map; f_equal; rewrite <- E; apply map_ext; intros t.
    unfold shift_term; rewrite eval_subst; apply eval_ext; intros i; reflexivity.
Qed.
Lemma represent_lists (xs ys : list U) : exists rho ts us,
  map (eval functions rho) ts=xs /\ map (eval functions rho) us=ys.
Proof.
  destruct (represent_list (xs++ys)) as [rho [ts E]].
  exists rho,(firstn (List.length xs) ts),(skipn (List.length xs) ts); split.
  - rewrite <- firstn_map,E,firstn_app,firstn_all,Nat.sub_diag; simpl; apply app_nil_r.
  - rewrite <- skipn_map,E,skipn_app,skipn_all,Nat.sub_diag; reflexivity.
Qed.
Variable rho0 : nat -> U.
Hypothesis equality_model : forall a, equality_theory a -> holds functions predicates rho0 a.
Lemma equality_instance rho a : equality_axiom a -> holds functions predicates rho a.
Proof.
  intros A; apply (Syntax.close_eliminate functions predicates a rho0 rho).
  apply equality_model; exists a; auto.
Qed.
Lemma original_reflexive x : original_equal x x.
Proof. exact (equality_instance (fun _ => x) (EqualityReflexive (Var 0))). Qed.
Lemma original_symmetric x y : original_equal x y -> original_equal y x.
Proof. exact (equality_instance (Syntax.push x (Syntax.push y rho0)) (EqualitySymmetric (Var 0) (Var 1))). Qed.
Lemma original_transitive x y z : original_equal x y -> original_equal y z -> original_equal x z.
Proof. exact (equality_instance (Syntax.push x (Syntax.push y (Syntax.push z rho0))) (EqualityTransitive (Var 0) (Var 1) (Var 2))). Qed.
Lemma original_function_congruence f xs ys : Forall2 original_equal xs ys -> original_equal (functions f xs) (functions f ys).
Proof.
  intros Related; destruct (represent_lists xs ys) as [rho [ts [us [X Y]]]].
  pose proof (equality_instance rho (EqualityFunction f ts us)) as Law.
  cbn [holds equal map eval] in Law. rewrite X,Y in Law; apply Law.
  apply equal_arguments_sat; now rewrite X,Y.
Qed.
Lemma original_predicate_congruence p xs ys : Forall2 original_equal xs ys -> (original_predicate p xs <-> original_predicate p ys).
Proof.
  assert (Forward : forall xs ys, Forall2 original_equal xs ys -> original_predicate p xs -> original_predicate p ys).
  { intros xs' ys' Related; destruct (represent_lists xs' ys') as [rho [ts [us [X Y]]]].
    pose proof (equality_instance rho (EqualityPredicate p ts us)) as Law.
    cbn [holds named_predicate] in Law; rewrite X,Y in Law; apply Law.
    apply equal_arguments_sat; now rewrite X,Y. }
  intros Related; split; [now apply Forward|]. apply Forward.
  induction Related; constructor; [now apply original_symmetric|exact IHRelated].
Qed.
(* Boolean normalization of a Source axiom adds no logical strength. Transfer
   through the equality quotient so the existing Source theorem also applies
   when the standard-logic model interprets equality relationally. *)
Lemma equivalent_sentence a b rho : Validation.equivalent a b=true ->
  holds functions predicates rho (source_sentence a) ->
  holds functions predicates rho (source_sentence b).
Proof.
  intros Equivalent A. unfold source_sentence in *.
  apply Syntax.close_introduce; intros eta. apply (translate_holds b 0 eta).
  apply (Syntax.close_eliminate functions predicates _ rho eta) in A.
  apply (translate_holds a 0 eta) in A.
  destruct (@representatives U original_equal) as [representative Correct].
  pose proof (@quotient_holds string string U functions original_predicate original_equal
    original_reflexive original_symmetric original_transitive original_function_congruence
    original_predicate_congruence representative Correct) as Transfer.
  apply Transfer. eapply (proj1 (Validation.equivalent_sound
    (quotient_function functions original_equal representative)
    (quotient_predicate original_predicate original_equal representative)
    classic a b Equivalent _ _)). apply Transfer; exact A.
Qed.
End Interpretation.

Module Connection (Order : WireOrder with Definition function_name := string with Definition predicate_name := string).
Module Checked := AxiomFuzzer.Source.Kernel.Kernel Order.
Theorem refutation_is_standard limit encode_variable decode_function decode_predicate t :
  Checked.derives_false limit encode_variable decode_function decode_predicate t -> source_theory t ⊢T Bot.
Proof.
  intros [inputs normalized numeric Allowed Unique Inputs Normalized Encoded Refuted].
  apply refutation_complete; [apply source_theory_closed|]. intros U functions predicates rho Model.
  assert (Eqs : forall a, equality_theory a -> holds functions predicates rho a).
  { intros a H; apply Model; now left. }
  assert (Relational : Forall (relational_holds functions (original_predicate predicates) (original_equal predicates)
      (fun _ => default functions) (fun _ => default functions)) (map source_text inputs)).
  { rewrite Forall_map; eapply Forall_impl; [|exact Allowed]. intros input A.
    apply (translate_holds functions predicates (source_text input) 0 rho).
    apply (Syntax.close_eliminate functions predicates (translate 0 (source_text input)) rho rho).
    apply Model; right; exists (source_text input); auto. }
  destruct (@quotient_model string string U functions (original_predicate predicates) (original_equal predicates)
    (@original_reflexive U functions predicates rho Eqs) (@original_symmetric U functions predicates rho Eqs)
    (@original_transitive U functions predicates rho Eqs) (@original_function_congruence U functions predicates rho Eqs)
    (@original_predicate_congruence U functions predicates rho Eqs)
    (default functions) (map source_text inputs) Relational) as [Q [d [f [p Qmodel]]]].
  destruct (primitive_refutation_checked numeric Refuted) as [proof Proof].
  apply (Checked.Sound.source_inputs_check_sound d f p classic (fun R H => choice R H)
    String.eqb String.eqb (fun x y => proj1 (String.eqb_eq x y)) (fun x y => proj1 (String.eqb_eq x y))
    encode_variable decode_function decode_predicate inputs limit normalized numeric proof
    Unique Inputs Normalized Encoded Proof).
  unfold source_input_holds; rewrite Forall_map in Qmodel; exact Qmodel.
Qed.
Theorem check_is_standard visit limit budget encode_variable decode_function decode_predicate t c :
  Checked.check visit limit budget encode_variable decode_function decode_predicate t c=true -> source_theory t ⊢T Bot.
Proof. intros H; apply (refutation_is_standard (Checked.check_derives_false visit limit budget encode_variable decode_function decode_predicate t c H)). Qed.
Theorem avatar_check_is_standard visit limit budget encode_variable decode_function decode_predicate t c proof :
  Checked.avatar_check visit limit budget encode_variable decode_function decode_predicate t c proof=true ->
  source_theory t ⊢T Bot.
Proof.
  unfold Checked.avatar_check. rewrite !andb_true_iff. intros [[Name Axioms] CheckedSources].
  assert (Allowed : Forall (fun a => authorized t (axiom_formula (original_axiom a))) (certificate_axioms c)).
  { apply Forall_forall. intros a In. apply (validate_axiom_authorized limit).
    rewrite List.forallb_forall in Axioms. now apply Axioms. }
  apply refutation_complete; [apply source_theory_closed|]. intros U functions predicates rho Model.
  assert (Eqs : forall a, equality_theory a -> holds functions predicates rho a).
  { intros a H; apply Model; now left. }
  assert (Relational : Forall (relational_holds functions (original_predicate predicates) (original_equal predicates)
      (fun _ => default functions) (fun _ => default functions))
      (map (fun a => axiom_formula (original_axiom a)) (certificate_axioms c))).
  { rewrite Forall_map; eapply Forall_impl; [|exact Allowed]. intros a A.
    apply (translate_holds functions predicates (axiom_formula (original_axiom a)) 0 rho).
    apply (Syntax.close_eliminate functions predicates (translate 0 (axiom_formula (original_axiom a))) rho rho).
    apply Model; right; exists (axiom_formula (original_axiom a)); auto. }
  destruct (@quotient_model string string U functions (original_predicate predicates) (original_equal predicates)
    (@original_reflexive U functions predicates rho Eqs) (@original_symmetric U functions predicates rho Eqs)
    (@original_transitive U functions predicates rho Eqs) (@original_function_congruence U functions predicates rho Eqs)
    (@original_predicate_congruence U functions predicates rho Eqs)
    (default functions) (map (fun a => axiom_formula (original_axiom a)) (certificate_axioms c)) Relational)
    as [Q [d [f [p Qmodel]]]].
  apply (Checked.avatar_check_sources_sound visit limit budget encode_variable decode_function decode_predicate
    f p d classic (fun R H => choice R H) c proof CheckedSources).
  rewrite Forall_map in Qmodel. exact Qmodel.
Qed.
Print Assumptions refutation_is_standard.
Print Assumptions avatar_check_is_standard.
End Connection.
