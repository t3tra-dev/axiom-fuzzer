(* WireSyntax *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Require Import AxiomFuzzer.Source.Language.
Import ListNotations.
Scheme All for list.

(* Constructor and field order match the portable OCaml representation. Wire
   re-exports these extracted types, rather than copying their definitions. *)
Inductive wire_symbol (F : Type) := Original : F -> wire_symbol F | Skolem : nat -> nat -> wire_symbol F.
Inductive wire_predicate (PT : Type) := Named : PT -> wire_predicate PT | Auxiliary : (nat * nat) -> wire_predicate PT.
Inductive wire_term (F : Type) :=
| V : (nat * nat) -> wire_term F
| Fn : wire_symbol F -> list (wire_term F) -> wire_term F.
Inductive wire_atom (F PT : Type) :=
| P : PT -> list (wire_term F) -> wire_atom F PT
| E : wire_term F -> wire_term F -> wire_atom F PT
| D : (nat * nat) -> list (wire_term F) -> wire_atom F PT.
Record wire_literal (F PT : Type) := { positive : bool; atom : wire_atom F PT }.
Arguments Original {F} _.
Arguments Skolem {F} _ _.
Arguments Named {PT} _.
Arguments Auxiliary {PT} _.
Arguments V {F} _.
Arguments Fn {F} _ _.
Arguments P {F PT} _ _.
Arguments E {F PT} _ _.
Arguments D {F PT} _ _.
Arguments Build_wire_literal {F PT} _ _.
Arguments positive {F PT} _.
Arguments atom {F PT} _.

Section Variables.
Context {F PT : Type}.
Fixpoint term_variables (t : wire_term F) : list (nat * nat) :=
  match t with V v => [v] | Fn _ ts => flat_map term_variables ts end.
Fixpoint term_variables_acc (t : wire_term F) acc :=
  match t with V v => v::acc | Fn _ ts => fold_left (fun acc t => term_variables_acc t acc) ts acc end.
Definition atom_variables (a : wire_atom F PT) :=
  match a with P _ ts | D _ ts => flat_map term_variables ts | E x y => term_variables x ++ term_variables y end.
Definition atom_variables_acc (a : wire_atom F PT) :=
  match a with
  | P _ ts | D _ ts => fold_left (fun acc t => term_variables_acc t acc) ts []
  | E x y => term_variables_acc y (term_variables_acc x [])
  end.
Fixpoint term_indices_acc (t : wire_term F) acc :=
  match t with V (_,i) => i::acc | Fn _ ts => fold_left (fun acc t => term_indices_acc t acc) ts acc end.
Definition atom_indices_acc (a : wire_atom F PT) :=
  match a with
  | P _ ts | D _ ts => fold_left (fun acc t => term_indices_acc t acc) ts []
  | E x y => term_indices_acc y (term_indices_acc x [])
  end.
Definition wire_support (a : wire_atom F PT) := sort_handles (atom_indices_acc a).
Definition base_atom (a : wire_atom F PT) := match a with D _ _ => false | _ => true end.
(* The nonnegative test is redundant on Rocq nat but remains necessary at the
   boundary where extraction uses signed OCaml integers. *)
Definition local_variable (v : nat * nat) := (fst v =? 0) && (0 <=? snd v).
Fixpoint wire_term_local (t : wire_term F) :=
  match t with V v => local_variable v | Fn _ ts => forallb wire_term_local ts end.
(* Lookup validation needs no variable list or sorting allocation. *)
Definition wire_base_valid (a : wire_atom F PT) :=
  match a with P _ ts => forallb wire_term_local ts | E x y => wire_term_local x && wire_term_local y | D _ _ => false end.
Definition checked_wire_support (a : wire_atom F PT) :=
  if wire_base_valid a then Some (wire_support a) else None.

Lemma term_variables_acc_members : forall t acc v,
  In v (term_variables_acc t acc) <-> In v (term_variables t) \/ In v acc.
Proof.
  fix IH 1. intros [x|s ts] acc v; simpl; [tauto|].
  revert acc. induction ts as [|t ts Hts]; intros acc; simpl; [tauto|].
  rewrite Hts, IH, in_app_iff. tauto.
Qed.
Lemma argument_variables_acc_members ts : forall acc v,
  In v (fold_left (fun acc t => term_variables_acc t acc) ts acc) <->
  In v (flat_map term_variables ts) \/ In v acc.
Proof.
  induction ts as [|t ts IH]; intros acc v; simpl; [tauto|].
  rewrite IH, term_variables_acc_members, in_app_iff. tauto.
Qed.
Theorem atom_variables_acc_members a v : In v (atom_variables_acc a) <-> In v (atom_variables a).
Proof.
  destruct a; simpl; rewrite ?argument_variables_acc_members, ?term_variables_acc_members, ?in_app_iff; simpl; tauto.
Qed.
Lemma term_indices_acc_members : forall t acc i,
  In i (term_indices_acc t acc) <-> (exists scope, In (scope,i) (term_variables t)) \/ In i acc.
Proof.
  fix IH 1. intros [[scope j]|s ts] acc i; simpl.
  - split.
    + intros [Eq|In]; [left; exists scope; left; now rewrite Eq|auto].
    + intros [[other [Eq|Absent]]|In]; [inversion Eq; auto|contradiction|auto].
  - revert acc. induction ts as [|t ts Hts]; intros acc; simpl; [firstorder|].
    rewrite Hts, IH. setoid_rewrite in_app_iff. firstorder.
Qed.
Lemma argument_indices_acc_members ts : forall acc i,
  In i (fold_left (fun acc t => term_indices_acc t acc) ts acc) <->
  (exists scope, In (scope,i) (flat_map term_variables ts)) \/ In i acc.
Proof.
  induction ts as [|t ts IH]; intros acc i; simpl; [firstorder|].
  rewrite IH, term_indices_acc_members. setoid_rewrite in_app_iff. firstorder.
Qed.
Theorem wire_support_members a i : In i (wire_support a) <-> exists scope, In (scope,i) (atom_variables a).
Proof.
  unfold wire_support. rewrite sort_handles_members.
  destruct a; simpl; rewrite ?argument_indices_acc_members, ?term_indices_acc_members; simpl;
    try setoid_rewrite in_app_iff; firstorder.
Qed.
Lemma wire_term_local_correct : forall t, wire_term_local t=true <->
  forall v, In v (term_variables t) -> local_variable v=true.
Proof.
  fix IH 1. intros [x|s ts]; simpl.
  - split; intros H; [intros v [E|Absent]; [now subst|contradiction]|apply H; now left].
  - induction ts as [|t ts Hts]; simpl.
    + split; [intros _ v Absent; contradiction|auto].
    + rewrite andb_true_iff, IH, Hts. split.
      * intros [Head Tail] v In. apply in_app_or in In as [In|In]; auto.
      * intros H. split; intros v In; apply H, in_or_app; auto.
Qed.
Theorem wire_base_valid_correct a : wire_base_valid a=true <->
  base_atom a=true /\ forall v, In v (atom_variables a) -> local_variable v=true.
Proof.
  destruct a as [p ts|x y|id ts]; simpl.
  - rewrite forallb_forall. split.
    + intros H. split; [reflexivity|]. intros v In. apply in_flat_map in In as [t [Ht Hv]].
      exact (proj1 (wire_term_local_correct t) (H t Ht) v Hv).
    + intros [_ H] t In. apply wire_term_local_correct. intros v Hv. apply H, in_flat_map. exists t; auto.
  - rewrite andb_true_iff, !wire_term_local_correct. split.
    + intros [X Y]. split; [reflexivity|]. intros v In. apply in_app_or in In as [In|In]; auto.
    + intros [_ H]. split; intros v In; apply H, in_or_app; auto.
  - split; intros H; [discriminate|destruct H as [H _]; discriminate].
Qed.
Theorem checked_wire_support_correct a vars : checked_wire_support a=Some vars ->
  vars=wire_support a /\ base_atom a=true /\ forall v, In v (atom_variables a) -> fst v=0.
Proof.
  unfold checked_wire_support. destruct (wire_base_valid a) eqn:Valid; [|discriminate].
  intros Accepted. inversion Accepted; subst vars. split; [reflexivity|].
  apply wire_base_valid_correct in Valid as [Base Local]. split; [exact Base|].
  intros v In. specialize (Local v In). unfold local_variable in Local. apply andb_true_iff in Local.
  now apply Nat.eqb_eq, (proj1 Local).
Qed.
End Variables.

Section Semantics.
Context {F PT U : Type}.
Variable functions : F -> list U -> U.
Variable predicates : PT -> list U -> Prop.
Variable skolem : (nat * nat) -> list U -> U.
Variable definitions : (nat * nat) -> list U -> Prop.
Fixpoint wire_eval (rho : (nat * nat) -> U) (t : wire_term F) : U :=
  match t with
  | V v => rho v
  | Fn (Original f) ts => functions f (map (wire_eval rho) ts)
  | Fn (Skolem ax id) ts => skolem (ax,id) (map (wire_eval rho) ts)
  end.
Definition wire_atom_holds rho a :=
  match a with
  | P p ts => predicates p (map (wire_eval rho) ts)
  | E x y => wire_eval rho x=wire_eval rho y
  | D id ts => definitions id (map (wire_eval rho) ts)
  end.
Definition wire_literal_holds rho (l : wire_literal F PT) :=
  if positive l then wire_atom_holds rho (atom l) else ~wire_atom_holds rho (atom l).

Theorem wire_eval_support : forall t rho other,
  (forall v, In v (term_variables t) -> rho v=other v) -> wire_eval rho t=wire_eval other t.
Proof.
  fix IH 1. intros [v|s ts] rho other Agree; simpl.
  - apply Agree. now left.
  - assert (Args : map (wire_eval rho) ts=map (wire_eval other) ts).
    { revert Agree. induction ts as [|t ts Hts]; intros Agree; simpl in *; [reflexivity|].
      f_equal.
      - apply IH. intros v In. apply Agree, in_or_app. now left.
      - apply Hts. intros v In. apply Agree, in_or_app. now right. }
    destruct s; simpl; now rewrite Args.
Qed.
Theorem wire_atom_support a rho other :
  (forall v, In v (atom_variables a) -> rho v=other v) -> (wire_atom_holds rho a <-> wire_atom_holds other a).
Proof.
  destruct a as [p ts|x y|id ts]; intros Agree; simpl in *.
  - assert (Args : map (wire_eval rho) ts=map (wire_eval other) ts).
    { apply map_ext_in. intros t In. apply wire_eval_support. intros v Hv. apply Agree.
      apply in_flat_map. exists t. auto. }
    now rewrite Args.
  - rewrite (wire_eval_support x rho other), (wire_eval_support y rho other); [reflexivity| |];
      intros v In; apply Agree, in_or_app; auto.
  - assert (Args : map (wire_eval rho) ts=map (wire_eval other) ts).
    { apply map_ext_in. intros t In. apply wire_eval_support. intros v Hv. apply Agree.
      apply in_flat_map. exists t. auto. }
    now rewrite Args.
Qed.
Theorem wire_local_support a rho other :
  (forall i, In i (wire_support a) -> rho i=other i) ->
  (wire_atom_holds (fun v => rho (snd v)) a <-> wire_atom_holds (fun v => other (snd v)) a).
Proof.
  intros Agree. apply wire_atom_support. intros [scope i] In. apply Agree, wire_support_members. eauto.
Qed.
End Semantics.
Print Assumptions wire_eval_support.
Print Assumptions wire_local_support.
Print Assumptions checked_wire_support_correct.

(* WireClauses *)
From Stdlib Require Import List Bool.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Import ListNotations.

Section Syntax.
Context {F PT : Type}.
Definition wire_clause := list (wire_literal F PT).
Definition clause_variables (c : wire_clause) := flat_map (fun l => atom_variables (atom l)) c.
Fixpoint rename_term (rename : (nat * nat) -> (nat * nat)) (t : wire_term F) :=
  match t with V v => V (rename v) | Fn s ts => Fn s (map (rename_term rename) ts) end.
Definition rename_atom rename (a : wire_atom F PT) :=
  match a with
  | P p ts => P p (map (rename_term rename) ts)
  | E x y => E (rename_term rename x) (rename_term rename y)
  | D id ts => D id (map (rename_term rename) ts)
  end.
Definition rename_literal rename (l : wire_literal F PT) := Build_wire_literal (positive l) (rename_atom rename (atom l)).
Definition rename_clause rename (c : wire_clause) := map (rename_literal rename) c.
Lemma rename_term_ext t f g : (forall v, f v=g v) -> rename_term f t=rename_term g t.
Proof.
  revert t f g. fix IH 1. intros [v|s ts] f g Same; simpl.
  - now rewrite Same.
  - f_equal. induction ts as [|t ts Hts]; simpl; [reflexivity|]. now rewrite (IH t f g Same), Hts.
Qed.
Lemma rename_clause_ext c f g : (forall v, f v=g v) -> rename_clause f c=rename_clause g c.
Proof.
  intros Same. apply map_ext. intros [sign a]. unfold rename_literal; simpl. f_equal.
  destruct a; simpl; f_equal; try (apply rename_term_ext; exact Same);
    apply map_ext; intros t; apply rename_term_ext; exact Same.
Qed.
End Syntax.

Section Semantics.
Context {F PT U : Type}.
Variable functions : F -> list U -> U.
Variable predicates : PT -> list U -> Prop.
Variable skolem : (nat * nat) -> list U -> U.
Variable definitions : (nat * nat) -> list U -> Prop.
Let holds := wire_literal_holds functions predicates skolem definitions.
Definition wire_clause_holds rho (c : @wire_clause F PT) := AxiomFuzzer.Preprocess.NormalForms.clause_holds (holds rho) c.
Definition wire_valid c := forall rho, wire_clause_holds rho c.

Lemma wire_clause_member rho c : wire_clause_holds rho c <-> exists l, In l c /\ holds rho l.
Proof.
  induction c as [|l c IH]; simpl; [unfold wire_clause_holds; simpl; firstorder|].
  change (holds rho l \/ wire_clause_holds rho c <-> exists k, (l=k \/ In k c) /\ holds rho k).
  rewrite IH. split.
  - intros [Head|[k [In Model]]]; [exists l|exists k]; auto.
  - intros [k [[Eq|In] Model]]; [subst k; now left|right; exists k; auto].
Qed.
Lemma wire_literal_support l rho other :
  (forall v, In v (atom_variables (atom l)) -> rho v=other v) -> (holds rho l <-> holds other l).
Proof.
  destruct l as [sign a]. intros Agree. unfold holds, wire_literal_holds; simpl.
  destruct sign; rewrite (wire_atom_support functions predicates skolem definitions a rho other Agree); reflexivity.
Qed.
Lemma wire_clause_support c rho other :
  (forall v, In v (clause_variables c) -> rho v=other v) -> (wire_clause_holds rho c <-> wire_clause_holds other c).
Proof.
  intros Agree. rewrite !wire_clause_member. split; intros [l [In Holds]]; exists l; split; [exact In| |exact In|];
    apply (wire_literal_support l rho other); try assumption; intros v Hv; apply Agree, in_flat_map; exists l; auto.
Qed.
Lemma rename_term_eval : forall t rename rho,
  wire_eval functions skolem rho (rename_term rename t)=wire_eval functions skolem (fun v => rho (rename v)) t.
Proof.
  fix IH 1. intros [v|s ts] rename rho; simpl; [reflexivity|].
  assert (Args : map (wire_eval functions skolem rho) (map (rename_term rename) ts)=
    map (wire_eval functions skolem (fun v => rho (rename v))) ts).
  { induction ts as [|t ts Hts]; simpl; [reflexivity|]. now rewrite IH, Hts. }
  destruct s; simpl; now rewrite Args.
Qed.
Lemma rename_atom_holds rename rho a :
  wire_atom_holds functions predicates skolem definitions rho (rename_atom rename a) <->
  wire_atom_holds functions predicates skolem definitions (fun v => rho (rename v)) a.
Proof.
  destruct a; simpl; rewrite ?rename_term_eval; try reflexivity;
    assert (Args : map (wire_eval functions skolem rho) (map (rename_term rename) l)=
      map (wire_eval functions skolem (fun v => rho (rename v))) l)
      by (rewrite map_map; apply map_ext; intros t; apply rename_term_eval);
    now rewrite Args.
Qed.
Lemma rename_literal_holds rename rho l : holds rho (rename_literal rename l) <-> holds (fun v => rho (rename v)) l.
Proof.
  destruct l as [sign a]. unfold holds, wire_literal_holds, rename_literal; simpl.
  destruct sign; rewrite rename_atom_holds; reflexivity.
Qed.
Theorem rename_clause_holds rename rho c :
  wire_clause_holds rho (rename_clause rename c) <-> wire_clause_holds (fun v => rho (rename v)) c.
Proof.
  induction c as [|l c IH]; simpl; [reflexivity|].
  change (holds rho (rename_literal rename l) \/ wire_clause_holds rho (rename_clause rename c) <->
    holds (fun v => rho (rename v)) l \/ wire_clause_holds (fun v => rho (rename v)) c).
  now rewrite rename_literal_holds, IH.
Qed.
End Semantics.
