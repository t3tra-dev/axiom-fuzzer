(* Finite stages of an unbounded search. Both the word bound and the checking
   budget grow. No assumption of monotonicity of the checker is needed. *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

Fixpoint words (alphabet length : nat) : list (list nat) :=
  match length with
  | 0 => [[]]
  | S length => flat_map (fun x => map (cons x) (words alphabet length)) (seq 0 alphabet)
  end.
Definition stage n := flat_map (words (S n)) (seq 0 (S n)).
Lemma words_spec alphabet length xs :
  In xs (words alphabet length) <-> List.length xs=length /\ Forall (fun x => x<alphabet) xs.
Proof.
  revert xs. induction length as [|length IH]; intros xs; simpl.
  - split.
    + intros [<-|[]]; auto.
    + intros [H _]. destruct xs; [auto|discriminate].
  - rewrite in_flat_map. split.
    + intros [x [X Ys]]. apply in_map_iff in Ys as [ys [<- Ys]].
      apply IH in Ys as [L Bound]. apply in_seq in X. simpl; split; [lia|constructor; tauto].
    + intros [L Bound]. destruct xs as [|x xs]; [discriminate|]. inversion Bound; subst.
      exists x; split; [apply in_seq; lia|]. apply in_map_iff. exists xs; split; [reflexivity|].
      apply IH; split; [simpl in L; lia|assumption].
Qed.
Lemma stage_spec n xs :
  In xs (stage n) <-> List.length xs<=n /\ Forall (fun x => x<=n) xs.
Proof.
  unfold stage; rewrite in_flat_map. split.
  - intros [k [K X]]. apply in_seq in K. apply words_spec in X as [L Bound].
    split; [lia|]. eapply Forall_impl; [|exact Bound]. intros x H; simpl in H |- *; lia.
  - intros [L Bound]. exists (List.length xs). split; [apply in_seq; lia|].
    apply words_spec; split; [reflexivity|]. eapply Forall_impl; [|exact Bound]. intros x H; simpl in H |- *; lia.
Qed.
Fixpoint maximum xs := match xs with [] => 0 | x::xs => Nat.max x (maximum xs) end.
Lemma maximum_bound xs : Forall (fun x => x<=maximum xs) xs.
Proof.
  induction xs; simpl; constructor; [apply Nat.le_max_l|].
  eapply Forall_impl; [|exact IHxs]. intros x H; simpl in H |- *; lia.
Qed.
Theorem every_word xs : exists n, In xs (stage n).
Proof.
  exists (Nat.max (List.length xs) (maximum xs)); apply stage_spec; split; [lia|].
  eapply Forall_impl; [|apply maximum_bound]. intros x H; simpl in H |- *; lia.
Qed.
Lemma stage_monotone n m xs : n<=m -> In xs (stage n) -> In xs (stage m).
Proof.
  intros NM X; apply stage_spec in X as [L Bound]. apply stage_spec; split; [lia|].
  eapply Forall_impl; [|exact Bound]. intros x H; simpl in H |- *; lia.
Qed.

Section Search.
Context {C : Type}.
Variable decode : list nat -> option C.
Variable check : nat -> C -> bool.
Definition attempt budget code :=
  match decode code with Some c => if check budget c then Some c else None | None => None end.
Fixpoint first_success (jobs : list (nat * list nat)) : option C :=
  match jobs with
  | [] => None
  | (budget,code)::rest => match attempt budget code with
      | Some c => Some c | None => first_success rest end
  end.
Definition jobs n := flat_map (fun budget => map (pair budget) (stage n)) (seq 0 (S n)).
Definition search n := first_success (jobs n).
Lemma first_success_sound js c : first_success js=Some c ->
  exists budget code, In (budget,code) js /\ decode code=Some c /\ check budget c=true.
Proof.
  induction js as [|[budget code] js IH]; simpl; [discriminate|].
  unfold attempt at 1. destruct (decode code) as [d|] eqn:Decoded.
  - destruct (check budget d) eqn:Checked.
    + intros H; inversion H; subst. exists budget,code; auto.
    + intros H. destruct (IH H) as [b [w [In [D Check]]]]. exists b,w; auto.
  - intros H. destruct (IH H) as [b [w [In [D Check]]]]. exists b,w; auto.
Qed.
Lemma first_success_complete js budget code c : In (budget,code) js ->
  decode code=Some c -> check budget c=true -> exists found, first_success js=Some found.
Proof.
  intros In D Check. induction js as [|[b w] js IH]; simpl in *; [contradiction|].
  destruct (attempt b w) as [found|] eqn:Run; [eauto|]. apply IH.
  destruct In as [E|In]; [|exact In]. inversion E; subst. unfold attempt in Run.
  rewrite D,Check in Run; discriminate.
Qed.
Theorem search_sound n c : search n=Some c -> exists budget, check budget c=true.
Proof.
  intros H. destruct (first_success_sound _ _ H) as [budget [code [_ [_ Check]]]]. eauto.
Qed.
Theorem search_complete code c budget : decode code=Some c -> check budget c=true ->
  exists n found, search n=Some found.
Proof.
  intros D Check. destruct (every_word code) as [k K].
  set (n:=Nat.max budget k).
  assert (InJob : In (budget,code) (jobs n)).
  { unfold jobs. apply in_flat_map. exists budget; split; [apply in_seq; unfold n; lia|].
    apply in_map. eapply stage_monotone; [unfold n; apply Nat.le_max_r|exact K]. }
  destruct (first_success_complete _ _ _ _ InJob D Check) as [found Run]. exists n,found; exact Run.
Qed.
(* Rechecking every lower budget makes timeouts provisional. *)
Theorem search_persistent n c m : n<=m -> search n=Some c -> exists found, search m=Some found.
Proof.
  intros NM Run. destruct (first_success_sound _ _ Run) as [budget [code [Job [D Check]]]].
  unfold jobs in Job. apply in_flat_map in Job as [b [B W]].
  apply in_map_iff in W as [w [E Word]]. inversion E; subst. apply in_seq in B.
  eapply first_success_complete; [|exact D|exact Check]. unfold jobs. apply in_flat_map.
  exists budget; split; [apply in_seq; lia|]. apply in_map.
  exact (stage_monotone n m code NM Word).
Qed.
End Search.
Print Assumptions search_complete.
Print Assumptions search_persistent.
