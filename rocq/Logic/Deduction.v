(* Classical first-order natural deduction and its finite proof data. *)
From Stdlib Require Import List String Bool Arith.PeanoNat Lia Logic.Classical_Prop.
Require Export AxiomFuzzer.Logic.Syntax.
Import ListNotations.
Local Set Implicit Arguments.

Inductive prv : list form -> form -> Prop :=
  | Ctx G a : In a G -> prv G a
  | II G a b : prv (a::G) b -> prv G (Imp a b)
  | IE G a b : prv G (Imp a b) -> prv G a -> prv G b
  | AllI G a : prv (map shift G) a -> prv G (All a)
  | AllE G a t : prv G (All a) -> prv G (instantiate t a)
  | Exp G a : prv G Bot -> prv G a
  | Pc G a b : prv G (Imp (Imp (Imp a b) a) a).
Definition tprv (T : form -> Prop) a := exists G, Forall T G /\ prv G a.
Notation "G ⊢ a" := (prv G a) (at level 55).
Notation "T ⊢T a" := (tprv T a) (at level 55).

Lemma weakening G a : G ⊢ a -> forall D, incl G D -> D ⊢ a.
Proof.
  induction 1; intros D Sub.
  - apply Ctx,Sub,H.
  - apply II,IHprv; intros x [<-|In]; simpl; auto.
  - eapply IE; [apply IHprv1|apply IHprv2]; exact Sub.
  - apply AllI,IHprv; intros x In. apply in_map_iff in In as [y [<- In]]. apply in_map,Sub,In.
  - apply AllE,IHprv,Sub.
  - apply Exp,IHprv,Sub.
  - apply Pc.
Qed.
Lemma substitution G a : G ⊢ a -> forall sigma, map (subst sigma) G ⊢ subst sigma a.
Proof.
  induction 1; intros sigma; simpl.
  - apply Ctx,in_map,H.
  - apply II,IHprv.
  - eapply IE; [apply IHprv1|apply IHprv2].
  - apply AllI. specialize (IHprv (up sigma)).
    replace (map shift (map (subst sigma) G)) with (map (subst (up sigma)) (map shift G)); [exact IHprv|].
    rewrite !map_map. apply map_ext; intros f; apply shift_comp.
  - rewrite instantiate_comp. apply AllE,IHprv.
  - apply Exp,IHprv.
  - apply Pc.
Qed.
Lemma deduction_cut G a : G ⊢ a -> forall D, (forall f, In f G -> D ⊢ f) -> D ⊢ a.
Proof.
  induction 1; intros D Derive.
  - apply Derive,H.
  - apply II,IHprv. intros f [<-|In]; [apply Ctx; now left|].
    apply (weakening (Derive f In)); intros x X; now right.
  - eapply IE; [apply IHprv1|apply IHprv2]; exact Derive.
  - apply AllI,IHprv. intros f In. apply in_map_iff in In as [a' [<- In]].
    apply (substitution (Derive a' In) (fun i => Var (S i))).
  - apply AllE,IHprv,Derive.
  - apply Exp,IHprv,Derive.
  - apply Pc.
Qed.

Definition extend (T : form -> Prop) a f := T f \/ f=a.
Definition consistent T := ~ T ⊢T Bot.
Lemma theory_ctx T a : T a -> T ⊢T a.
Proof. intros H; exists [a]; split; [now repeat constructor|apply Ctx; now left]. Qed.
Lemma theory_weak T U a : (forall f, T f -> U f) -> T ⊢T a -> U ⊢T a.
Proof.
  intros Sub [G [Allowed D]]. exists G; split; [|exact D].
  eapply Forall_impl; [|exact Allowed]; exact Sub.
Qed.
Lemma theory_imp_elim T a b : T ⊢T Imp a b -> T ⊢T a -> T ⊢T b.
Proof.
  intros [G [GA GD]] [D [DA DD]]. exists (G++D); split; [now apply Forall_app|].
  eapply IE; [apply (weakening GD)|apply (weakening DD)]; intros f In; apply in_or_app; auto.
Qed.
Lemma theory_explosion T a : T ⊢T Bot -> T ⊢T a.
Proof. intros [G [A D]]; exists G; split; [exact A|now apply Exp]. Qed.
Lemma remove_assumption T a G : Forall (extend T a) G ->
  exists D, Forall T D /\ incl G (a::D).
Proof.
  induction 1 as [|f G [Allowed|Equal] Rest [D [AD Sub]]].
  - exists []; split; [constructor|intros x []].
  - exists (f::D); split; [now constructor|]. intros x [<-|In]; [now right; left|].
    destruct (Sub x In) as [<-|In']; [now left|now right; right].
  - subst f. exists D; split; [exact AD|]. intros x [<-|In]; [now left|apply Sub,In].
Qed.
Lemma theory_imp_intro T a b : extend T a ⊢T b -> T ⊢T Imp a b.
Proof.
  intros [G [A Derivation]]. destruct (remove_assumption A) as [D [Allowed Sub]].
  exists D; split; [exact Allowed|apply II; exact (weakening Derivation Sub)].
Qed.
Lemma theory_classical T a : extend T (neg a) ⊢T Bot -> T ⊢T a.
Proof.
  intros D. apply (theory_imp_elim (a:=Imp (neg a) a)).
  - exists []; split; [constructor|apply Pc].
  - apply theory_imp_intro,theory_explosion,D.
Qed.
Lemma inconsistent_extension T a : ~consistent (extend T a) -> T ⊢T neg a.
Proof. intros H; apply theory_imp_intro,NNPP,H. Qed.
Lemma negative_extension T a : consistent T -> ~consistent (extend T a) -> consistent (extend T (neg a)).
Proof.
  intros Good Bad Contradiction. apply Good.
  eapply theory_imp_elim; [apply inconsistent_extension,Bad|apply theory_classical,Contradiction].
Qed.

(* Generalization over a variable absent from the entire assumption theory. *)
Definition abstract_variable k i := if Nat.eqb i k then Var 0 else Var (S i).
Lemma abstract_fresh k a : bound a<=k -> subst (abstract_variable k) a=shift a.
Proof.
  intros B; apply subst_agree; intros i I. unfold abstract_variable.
  destruct (Nat.eqb_spec i k); [lia|reflexivity].
Qed.
Lemma abstract_instance k a : bound (All a)<=k -> subst (abstract_variable k) (instantiate (Var k) a)=a.
Proof.
  intros B. unfold instantiate; rewrite subst_comp.
  transitivity (subst Var a); [|apply subst_id]. apply subst_agree; intros [|i] I; simpl.
  - unfold abstract_variable; now rewrite Nat.eqb_refl.
  - unfold abstract_variable. destruct (Nat.eqb_spec i k); [simpl in B; lia|reflexivity].
Qed.
Lemma theory_generalize T a k : (forall f, T f -> bound f<=k) -> bound (All a)<=k ->
  T ⊢T instantiate (Var k) a -> T ⊢T All a.
Proof.
  intros B A [G [Allowed D]]. exists G; split; [exact Allowed|]. apply AllI.
  rewrite <- (abstract_instance (k:=k) a A).
  replace (map shift G) with (map (subst (abstract_variable k)) G).
  - apply substitution,D.
  - apply map_ext_in; intros f In; apply abstract_fresh,B.
    exact (proj1 (Forall_forall _ _) Allowed f In).
Qed.
Lemma witness_extension T a k : consistent T -> T (neg (All a)) ->
  (forall f, T f -> bound f<=k) -> bound (All a)<=k ->
  consistent (extend T (neg (instantiate (Var k) a))).
Proof.
  intros Good Negative Bounds Body Refuted. apply Good.
  eapply theory_imp_elim; [apply theory_ctx,Negative|].
  eapply theory_generalize; [exact Bounds|exact Body|]. apply theory_classical,Refuted.
Qed.

Theorem soundness {U} (functions : string -> list U -> U) predicates G a : G ⊢ a ->
  forall rho, (forall f, In f G -> holds functions predicates rho f) -> holds functions predicates rho a.
Proof.
  induction 1; intros rho Model; simpl.
  - apply Model,H.
  - intros A; apply IHprv; intros f [<-|In]; auto.
  - apply IHprv1; [exact Model|now apply IHprv2].
  - intros x; apply IHprv. intros f In; apply in_map_iff in In as [a' [<- In]].
    unfold shift; rewrite holds_subst. apply Model,In.
  - unfold instantiate; rewrite holds_subst.
    apply (holds_ext functions predicates a (push (eval functions rho t) rho)
      (fun i => eval functions rho (push t Var i))); [intros [|i]; reflexivity|].
    apply IHprv,Model.
  - exfalso; exact (IHprv rho Model).
  - destruct (classic (holds functions predicates rho a)); tauto.
Qed.

Inductive proof :=
  | Assume (index : nat)
  | ImplicationIntroduction (premise : form) (body : proof)
  | ImplicationElimination (function argument : proof)
  | UniversalIntroduction (body : proof)
  | UniversalElimination (witness : term) (body : proof)
  | Explosion (conclusion : form) (body : proof)
  | Peirce (a b : form).
Fixpoint infer G p : option form := match p with
  | Assume i => nth_error G i
  | ImplicationIntroduction a p => option_map (Imp a) (infer (a::G) p)
  | ImplicationElimination p q => match infer G p,infer G q with
      | Some (Imp a b),Some a' => if form_dec a a' then Some b else None | _,_ => None end
  | UniversalIntroduction p => option_map All (infer (map shift G) p)
  | UniversalElimination t p => match infer G p with Some (All a) => Some (instantiate t a) | _ => None end
  | Explosion a p => match infer G p with Some Bot => Some a | _ => None end
  | Peirce a b => Some (Imp (Imp (Imp a b) a) a) end.
Theorem infer_sound p : forall G a, infer G p=Some a -> G ⊢ a.
Proof.
  induction p; intros G result; simpl.
  - intros H; apply Ctx; now apply nth_error_In in H.
  - destruct (infer (premise::G) p) eqn:E; [|discriminate].
    intros H; inversion H; subst; apply II; now apply IHp.
  - destruct (infer G p1) as [[|r ts|b c|b]|] eqn:E; try discriminate.
    destruct (infer G p2) as [d|] eqn:F; [|discriminate].
    destruct (form_dec b d) as [<-|]; [|discriminate].
    intros H; inversion H; subst. eapply IE; [exact (IHp1 _ _ E)|exact (IHp2 _ _ F)].
  - destruct (infer (map shift G) p) eqn:E; [|discriminate].
    intros H; inversion H; subst; apply AllI; now apply IHp.
  - destruct (infer G p) as [[|r ts|b c|b]|] eqn:E; try discriminate.
    intros H; inversion H; subst; apply AllE; now apply IHp.
  - destruct (infer G p) as [[|r ts|b c|b]|] eqn:E; try discriminate.
    intros H; inversion H; subst; apply Exp; now apply IHp.
  - intros H; inversion H; subst; apply Pc.
Qed.
Theorem infer_complete G a : G ⊢ a -> exists p, infer G p=Some a.
Proof.
  induction 1.
  - apply In_nth_error in H as [i E]; exists (Assume i); exact E.
  - destruct IHprv as [p E]; exists (ImplicationIntroduction a p); simpl; now rewrite E.
  - destruct IHprv1 as [p E],IHprv2 as [q F]; exists (ImplicationElimination p q); simpl; rewrite E,F.
    destruct (form_dec a a); congruence.
  - destruct IHprv as [p E]; exists (UniversalIntroduction p); simpl; now rewrite E.
  - destruct IHprv as [p E]; exists (UniversalElimination t p); simpl; now rewrite E.
  - destruct IHprv as [p E]; exists (Explosion a p); simpl; now rewrite E.
  - exists (Peirce a b); reflexivity.
Qed.
Section Certificates.
Context {Witness : Type}.
Variable axiom_at : Witness -> option form.
Definition theory a := exists w, axiom_at w=Some a.
Fixpoint context_at ids : option (list form) := match ids with
  | [] => Some [] | i::ids => match axiom_at i,context_at ids with
      | Some a,Some G => Some (a::G) | _,_ => None end end.
Record certificate := { assumptions : list Witness; deduction : proof }.
Definition check c := match context_at (assumptions c) with
  | Some G => match infer G (deduction c) with Some Bot => true | _ => false end | None => false end.
Lemma context_sound ids G : context_at ids=Some G -> Forall theory G.
Proof.
  revert G; induction ids; intros G; simpl.
  - intros H; inversion H; constructor.
  - destruct (axiom_at a) as [f|] eqn:E; [|discriminate].
    destruct (context_at ids) as [D|] eqn:F; [|discriminate].
    intros H; inversion H; subst. constructor; [now exists a|now apply IHids].
Qed.
Lemma context_complete G : Forall theory G -> exists ids, context_at ids=Some G.
Proof.
  induction 1 as [|a G [w E] Rest [ids F]].
  - exists []; reflexivity.
  - exists (w::ids); simpl; now rewrite E,F.
Qed.
Theorem check_sound c : check c=true -> theory ⊢T Bot.
Proof.
  unfold check. destruct (context_at (assumptions c)) as [G|] eqn:E; [|discriminate].
  destruct (infer G (deduction c)) as [[|p ts|a b|a]|] eqn:F; try discriminate.
  intros _; exists G; split; [now apply context_sound in E|now apply infer_sound in F].
Qed.
Theorem check_complete : theory ⊢T Bot -> exists c, check c=true.
Proof.
  intros [G [Allowed D]]. destruct (context_complete Allowed) as [ids E].
  destruct (infer_complete D) as [p F]. exists {| assumptions:=ids; deduction:=p |}.
  unfold check; simpl; now rewrite E,F.
Qed.
End Certificates.
Print Assumptions infer_complete.
Print Assumptions check_complete.
