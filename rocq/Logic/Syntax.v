(* First-order syntax needed by this project. Function arity is the length of
   its argument list; None is reserved for the equality predicate. Bound and
   free variables use the usual de Bruijn convention. *)
From Stdlib Require Import List String Bool Arith.PeanoNat Lia.
Require Import AxiomFuzzer.Reference.Encoding.
Import ListNotations.
Local Open Scope list_scope.
Local Set Implicit Arguments.

Inductive term := Var (index : nat) | Fun (name : string) (arguments : list term).
Inductive form := Bot | Atom (name : option string) (arguments : list term)
  | Imp (premise conclusion : form) | All (body : form).
Definition neg a := Imp a Bot.
Definition push {A} (x : A) (rho : nat -> A) i := match i with 0 => x | S i => rho i end.
Fixpoint subst_term sigma t := match t with
  | Var i => sigma i | Fun f ts => Fun f (map (subst_term sigma) ts) end.
Definition shift_term := subst_term (fun i => Var (S i)).
Definition up sigma i := match i with 0 => Var 0 | S i => shift_term (sigma i) end.
Fixpoint subst sigma a := match a with
  | Bot => Bot | Atom p ts => Atom p (map (subst_term sigma) ts)
  | Imp a b => Imp (subst sigma a) (subst sigma b) | All a => All (subst (up sigma) a) end.
Definition shift := subst (fun i => Var (S i)).
Definition instantiate t := subst (push t Var).

Lemma term_induction (P : term -> Prop) :
  (forall n, P (Var n)) -> (forall f ts, Forall P ts -> P (Fun f ts)) -> forall t, P t.
Proof.
  intros Hvar Hfun. fix IH 1; intros [n|f ts]; [apply Hvar|].
  apply Hfun. induction ts; constructor; auto.
Qed.
Lemma subst_term_ext sigma tau t : (forall i, sigma i=tau i) -> subst_term sigma t=subst_term tau t.
Proof.
  intros Agree. induction t using term_induction; simpl; [apply Agree|].
  f_equal; apply map_ext_in; intros x In; now apply (proj1 (Forall_forall _ _) H).
Qed.
Lemma subst_term_id t : subst_term Var t=t.
Proof.
  induction t using term_induction; simpl; [reflexivity|]. f_equal.
  induction H; simpl; congruence.
Qed.
Lemma subst_term_comp sigma tau t :
  subst_term sigma (subst_term tau t)=subst_term (fun i => subst_term sigma (tau i)) t.
Proof.
  induction t using term_induction; simpl; [reflexivity|]. rewrite map_map; f_equal.
  apply map_ext_in; intros x In; now apply (proj1 (Forall_forall _ _) H).
Qed.
Lemma subst_shift_term sigma t : subst_term (up sigma) (shift_term t)=shift_term (subst_term sigma t).
Proof. unfold shift_term; rewrite !subst_term_comp; apply subst_term_ext; reflexivity. Qed.
Lemma up_ext sigma tau : (forall i, sigma i=tau i) -> forall i, up sigma i=up tau i.
Proof. intros H [|i]; simpl; [reflexivity|now rewrite H]. Qed.
Lemma subst_ext sigma tau a : (forall i, sigma i=tau i) -> subst sigma a=subst tau a.
Proof.
  revert sigma tau; induction a; intros sigma tau H; simpl; f_equal; auto using up_ext.
  apply map_ext; intros t; now apply subst_term_ext.
Qed.
Lemma subst_id a : subst Var a=a.
Proof.
  induction a; simpl; f_equal; auto.
  - induction arguments; simpl; now rewrite ?subst_term_id, ?IHarguments.
  - rewrite <- IHa at 2. apply subst_ext; intros [|i]; reflexivity.
Qed.
Lemma up_comp sigma tau i :
  subst_term (up sigma) (up tau i)=up (fun j => subst_term sigma (tau j)) i.
Proof. destruct i; simpl; [reflexivity|apply subst_shift_term]. Qed.
Lemma subst_comp sigma tau a :
  subst sigma (subst tau a)=subst (fun i => subst_term sigma (tau i)) a.
Proof.
  revert sigma tau; induction a; intros sigma tau; simpl; f_equal; auto.
  - rewrite map_map; apply map_ext; apply subst_term_comp.
  - rewrite IHa. apply subst_ext, up_comp.
Qed.
Lemma instantiate_shift t a : instantiate t (shift a)=a.
Proof.
  unfold instantiate,shift. rewrite subst_comp. transitivity (subst Var a); [|apply subst_id].
  apply subst_ext; reflexivity.
Qed.
Lemma instantiate_comp sigma t a :
  subst sigma (instantiate t a)=instantiate (subst_term sigma t) (subst (up sigma) a).
Proof.
  unfold instantiate. rewrite !subst_comp. apply subst_ext; intros [|i]; simpl; [reflexivity|].
  unfold shift_term. rewrite subst_term_comp. symmetry; transitivity (subst_term Var (sigma i));
    [apply subst_term_ext; reflexivity|apply subst_term_id].
Qed.
Lemma shift_comp sigma a : subst (up sigma) (shift a)=shift (subst sigma a).
Proof. unfold shift; rewrite !subst_comp; apply subst_ext; reflexivity. Qed.
Lemma instantiate_up sigma t a : instantiate t (subst (up sigma) a)=subst (push t sigma) a.
Proof.
  unfold instantiate; rewrite subst_comp; apply subst_ext; intros [|i]; simpl; [reflexivity|].
  unfold shift_term; rewrite subst_term_comp. transitivity (subst_term Var (sigma i));
    [apply subst_term_ext; reflexivity|apply subst_term_id].
Qed.

Definition maximum := fold_right Nat.max 0.
Lemma maximum_member xs n : In n xs -> n<=maximum xs.
Proof. induction xs; simpl; [contradiction|]. intros [<-|H]; [lia|specialize (IHxs H); lia]. Qed.
Fixpoint term_bound t := match t with
  | Var i => S i | Fun _ ts => maximum (map term_bound ts) end.
Fixpoint bound a := match a with
  | Bot => 0 | Atom _ ts => maximum (map term_bound ts)
  | Imp a b => Nat.max (bound a) (bound b) | All a => Nat.pred (bound a) end.
Definition closed a := bound a=0.
Lemma subst_term_agree t sigma tau :
  (forall i, i<term_bound t -> sigma i=tau i) -> subst_term sigma t=subst_term tau t.
Proof.
  revert sigma tau; induction t using term_induction; intros sigma tau Agree; simpl in *.
  - apply Agree; lia.
  - f_equal; apply map_ext_in; intros x In.
    apply (proj1 (Forall_forall _ _) H x In). intros i Bound; apply Agree.
    pose proof (maximum_member (map term_bound ts) (term_bound x) (in_map _ _ _ In)); lia.
Qed.
Lemma subst_agree a sigma tau : (forall i, i<bound a -> sigma i=tau i) -> subst sigma a=subst tau a.
Proof.
  revert sigma tau; induction a; intros sigma tau Agree; simpl in *; try reflexivity; f_equal.
  - apply map_ext_in; intros t In; apply subst_term_agree; intros i Bound; apply Agree.
    pose proof (maximum_member (map term_bound arguments) (term_bound t) (in_map _ _ _ In)); lia.
  - apply IHa1; intros i H; apply Agree; lia.
  - apply IHa2; intros i H; apply Agree; lia.
  - apply IHa; intros [|i] H; simpl; [reflexivity|]. rewrite Agree by lia; reflexivity.
Qed.
Lemma subst_closed a sigma : closed a -> subst sigma a=a.
Proof. intros H; transitivity (subst Var a); [apply subst_agree; unfold closed in H; intros; lia|apply subst_id]. Qed.
Fixpoint capture n a := match n with 0 => a | S n => All (capture n a) end.
Definition close a := capture (bound a) a.
Lemma capture_bound n a : bound (capture n a)=bound a-n.
Proof. induction n; simpl; [lia|rewrite IHn; lia]. Qed.
Lemma close_closed a : closed (close a).
Proof. unfold closed,close; rewrite capture_bound; lia. Qed.

(* A compact codec also supplies the countable syntax used by the model proof. *)
Fixpoint term_code t := match t with
  | Var i => Number i | Fun f ts => Pair (string_code f) (list_code term_code ts) end.
Fixpoint term_value c : option term := match c with
  | Number i => Some (Var i)
  | Pair f ts => match string_value f,list_value term_value ts with
      | Some f,Some ts => Some (Fun f ts) | _,_ => None end end.
Lemma term_roundtrip t : term_value (term_code t)=Some t.
Proof.
  induction t using term_induction; simpl; [reflexivity|]. rewrite string_roundtrip.
  rewrite list_roundtrip_on; [reflexivity|]. exact (proj1 (Forall_forall _ _) H).
Qed.
Fixpoint form_code a := match a with
  | Bot => Number 0
  | Atom None ts => Pair (Number 1) (list_code term_code ts)
  | Atom (Some p) ts => Pair (Number 2) (Pair (string_code p) (list_code term_code ts))
  | Imp a b => Pair (Number 3) (Pair (form_code a) (form_code b))
  | All a => Pair (Number 4) (form_code a) end.
Fixpoint form_value c : option form := match c with
  | Number 0 => Some Bot
  | Pair (Number 1) ts => option_map (Atom None) (list_value term_value ts)
  | Pair (Number 2) (Pair p ts) => match string_value p,list_value term_value ts with
      | Some p,Some ts => Some (Atom (Some p) ts) | _,_ => None end
  | Pair (Number 3) (Pair a b) => match form_value a,form_value b with
      | Some a,Some b => Some (Imp a b) | _,_ => None end
  | Pair (Number 4) a => option_map All (form_value a)
  | _ => None end.
Lemma form_roundtrip a : form_value (form_code a)=Some a.
Proof.
  induction a; simpl; try congruence.
  - destruct name; simpl; rewrite ?string_roundtrip, (list_roundtrip _ _ term_roundtrip); reflexivity.
  - now rewrite IHa1,IHa2.
  - now rewrite IHa.
Qed.
Definition code_dec : forall x y : code, {x=y}+{x<>y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition form_dec (a b : form) : {a=b}+{a<>b}.
Proof.
  destruct (code_dec (form_code a) (form_code b)) as [E|N].
  - left. apply (f_equal form_value) in E; rewrite !form_roundtrip in E; congruence.
  - right; intros ->; now apply N.
Defined.

Section Semantics.
Context {U : Type}.
Variable functions : string -> list U -> U.
Variable predicates : option string -> list U -> Prop.
Fixpoint eval rho t := match t with Var i => rho i | Fun f ts => functions f (map (eval rho) ts) end.
Fixpoint holds rho a : Prop := match a with
  | Bot => False | Atom p ts => predicates p (map (eval rho) ts)
  | Imp a b => holds rho a -> holds rho b | All a => forall x, holds (push x rho) a end.
Lemma eval_ext t rho eta : (forall i, rho i=eta i) -> eval rho t=eval eta t.
Proof.
  intros Agree; induction t using term_induction; simpl; [apply Agree|].
  f_equal; apply map_ext_in; intros t In; now apply (proj1 (Forall_forall _ _) H).
Qed.
Lemma eval_subst t sigma rho : eval rho (subst_term sigma t)=eval (fun i => eval rho (sigma i)) t.
Proof.
  induction t using term_induction; simpl; [reflexivity|]. rewrite map_map; f_equal.
  apply map_ext_in; intros t In; now apply (proj1 (Forall_forall _ _) H).
Qed.
Lemma holds_ext a rho eta : (forall i, rho i=eta i) -> (holds rho a <-> holds eta a).
Proof.
  revert rho eta; induction a; intros rho eta Agree; simpl; try tauto.
  - assert (E : map (eval rho) arguments=map (eval eta) arguments) by
      (apply map_ext; intros t; now apply eval_ext). now rewrite E.
  - now rewrite (IHa1 _ _ Agree),(IHa2 _ _ Agree).
  - split; intros H x; [apply (IHa (push x rho) (push x eta))|apply (IHa (push x rho) (push x eta))];
      try (intros [|i]; simpl; auto); apply H.
Qed.
Lemma holds_subst a sigma rho : holds rho (subst sigma a) <-> holds (fun i => eval rho (sigma i)) a.
Proof.
  revert sigma rho; induction a; intros sigma rho; simpl; try tauto.
  - rewrite map_map. assert (E : map (fun t => eval rho (subst_term sigma t)) arguments =
        map (eval (fun i => eval rho (sigma i))) arguments) by (apply map_ext; intros t; apply eval_subst).
    now rewrite E.
  - now rewrite IHa1,IHa2.
  - assert (Env : forall x i, eval (push x rho) (up sigma i)=push x (fun j => eval rho (sigma j)) i).
    { intros x [|i]; simpl; [reflexivity|]. unfold shift_term; rewrite eval_subst; apply eval_ext; reflexivity. }
    split; intros H x.
    + specialize (H x). apply IHa in H. apply (holds_ext a _ _ (Env x)); exact H.
    + apply IHa. apply (holds_ext a _ _ (Env x)); apply H.
Qed.
Lemma holds_agree a rho eta : (forall i, i<bound a -> rho i=eta i) -> (holds rho a <-> holds eta a).
Proof.
  revert rho eta; induction a; intros rho eta Agree; simpl in *; try tauto.
  - assert (Terms : forall t, (forall i, i<term_bound t -> rho i=eta i) -> eval rho t=eval eta t).
    { intros t; induction t as [n|f ts Children] using term_induction; intros Ag; simpl; [apply Ag; simpl; lia|].
      f_equal; apply map_ext_in; intros x In; apply (proj1 (Forall_forall _ _) Children x In).
      intros i Bound; apply Ag. simpl. pose proof (maximum_member (map term_bound ts) (term_bound x) (in_map _ _ _ In)); lia. }
    assert (E : map (eval rho) arguments=map (eval eta) arguments).
    { apply map_ext_in; intros t In; apply Terms; intros i Bound; apply Agree.
      pose proof (maximum_member (map term_bound arguments) (term_bound t) (in_map _ _ _ In)); lia. }
    now rewrite E.
  - rewrite (IHa1 rho eta), (IHa2 rho eta); try (intros; apply Agree; lia); tauto.
  - split; intros H x; [apply (IHa (push x rho) (push x eta))|apply (IHa (push x rho) (push x eta))];
      try (intros [|i] B; simpl; [reflexivity|apply Agree; lia]); apply H.
Qed.
Lemma holds_closed a rho eta : closed a -> (holds rho a <-> holds eta a).
Proof. intros Closed; apply holds_agree; unfold closed in Closed; intros; lia. Qed.
Lemma capture_eliminate n a rho : holds rho (capture n a) -> forall eta,
  holds (fun i => if i <? n then eta i else rho (i-n)) a.
Proof.
  revert rho; induction n; intros rho H eta; cbn [capture holds] in H.
  - eapply holds_ext; [|exact H]; intros i; simpl; now rewrite Nat.sub_0_r.
  - specialize (IHn (push (eta n) rho) (H (eta n)) eta).
    apply (holds_ext a (fun i => if i <? n then eta i else push (eta n) rho (i-n))
      (fun i => if i <? S n then eta i else rho (i-S n))); [|exact IHn].
    intros i. destruct (i <? n) eqn:B, (i <? S n) eqn:C;
      (apply Nat.ltb_lt in B || apply Nat.ltb_ge in B);
      (apply Nat.ltb_lt in C || apply Nat.ltb_ge in C); try lia; try reflexivity.
    + assert (i=n) by lia; subst. rewrite Nat.sub_diag; reflexivity.
    + assert (i-n=S(i-S n)) as E by lia; rewrite E; reflexivity.
Qed.
Lemma close_eliminate a rho eta : holds rho (close a) -> holds eta a.
Proof.
  intros H; apply capture_eliminate with (eta:=eta) in H.
  apply (holds_agree a (fun i => if i <? bound a then eta i else rho (i-bound a)) eta); [|exact H].
  intros i B; rewrite (proj2 (Nat.ltb_lt i (bound a)) B); reflexivity.
Qed.
Lemma close_introduce a rho : (forall eta, holds eta a) -> holds rho (close a).
Proof.
  unfold close. generalize (bound a); intros n; revert rho.
  induction n; intros rho H; simpl; [apply H|intros x; apply IHn,H].
Qed.
End Semantics.
