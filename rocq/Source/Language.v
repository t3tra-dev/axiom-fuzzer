(* Source *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Import ListNotations.
Scheme All for list.

(* Source syntax keeps free parameters separate from De Bruijn indices.
   Symbol types are abstract, so extraction can retain OCaml string symbols. *)
Inductive source_term (F : Type) : Type :=
| SBound : nat -> source_term F
| SFree : nat -> source_term F
| SApply : F -> list (source_term F) -> source_term F.
Arguments SBound {F} _.
Arguments SFree {F} _.
Arguments SApply {F} _ _.
Inductive source_formula (F P : Type) : Type :=
| STop : source_formula F P
| SBot : source_formula F P
| SPred : P -> list (source_term F) -> source_formula F P
| SEq : source_term F -> source_term F -> source_formula F P
| SNeg : source_formula F P -> source_formula F P
| SConj : list (source_formula F P) -> source_formula F P
| SDisj : list (source_formula F P) -> source_formula F P
| SAll : source_formula F P -> source_formula F P
| SEx : source_formula F P -> source_formula F P.
Arguments STop {F P}.
Arguments SBot {F P}.
Arguments SPred {F P} _ _.
Arguments SEq {F P} _ _.
Arguments SNeg {F P} _.
Arguments SConj {F P} _.
Arguments SDisj {F P} _.
Arguments SAll {F P} _.
Arguments SEx {F P} _.

Section Scope.
Context {F P : Type}.
Fixpoint term_scoped depth closed (t : source_term F) : bool :=
  match t with
  | SBound i => (0 <=? i) && negb (depth <=? i) | SFree i => (0 <=? i) && negb closed
  | SApply _ ts => forallb (term_scoped depth closed) ts
  end.
Fixpoint formula_scoped depth closed (f : source_formula F P) : bool :=
  match f with
  | STop | SBot => true | SPred _ ts => forallb (term_scoped depth closed) ts
  | SEq x y => term_scoped depth closed x && term_scoped depth closed y
  | SNeg f => formula_scoped depth closed f
  | SConj fs | SDisj fs => forallb (formula_scoped depth closed) fs
  | SAll f | SEx f => formula_scoped (S depth) closed f
  end.
Fixpoint term_wf depth closed (t : source_term F) : Prop :=
  match t with
  | SBound i => i < depth | SFree _ => closed = false
  | SApply _ ts => (fix every ts := match ts with [] => True | t::ts => term_wf depth closed t /\ every ts end) ts
  end.
Fixpoint formula_wf depth closed (f : source_formula F P) : Prop :=
  match f with
  | STop | SBot => True | SPred _ ts => (fix every ts := match ts with [] => True | t::ts => term_wf depth closed t /\ every ts end) ts
  | SEq x y => term_wf depth closed x /\ term_wf depth closed y
  | SNeg f => formula_wf depth closed f
  | SConj fs | SDisj fs => (fix every fs := match fs with [] => True | f::fs => formula_wf depth closed f /\ every fs end) fs
  | SAll f | SEx f => formula_wf (S depth) closed f
  end.
Lemma term_scope_spec : forall (t : source_term F) depth closed,
  term_scoped depth closed t = true <-> term_wf depth closed t.
Proof.
  fix IH 1. intros [i|i|s ts] depth closed; simpl.
  - rewrite negb_true_iff, Nat.leb_gt. reflexivity.
  - destruct closed; simpl; intuition discriminate.
  - induction ts as [|t ts Hts]; simpl.
    + tauto.
    + rewrite andb_true_iff, IH, Hts. reflexivity.
Qed.
Theorem source_scope_spec : forall (f : source_formula F P) depth closed,
  formula_scoped depth closed f = true <-> formula_wf depth closed f.
Proof.
  fix IH 1. intros [| |p ts|x y|f|fs|fs|f|f] depth closed; simpl.
  - tauto.
  - tauto.
  - induction ts as [|t ts Hts]; simpl.
    + tauto.
    + rewrite andb_true_iff, term_scope_spec, Hts. reflexivity.
  - rewrite andb_true_iff, !term_scope_spec. reflexivity.
  - apply IH.
  - induction fs as [|f fs Hfs]; simpl.
    + tauto.
    + rewrite andb_true_iff, IH, Hfs. reflexivity.
  - induction fs as [|f fs Hfs]; simpl.
    + tauto.
    + rewrite andb_true_iff, IH, Hfs. reflexivity.
  - apply IH.
  - apply IH.
Qed.
End Scope.

Section Abstraction.
Context {F P : Type}.
Fixpoint bind_term depth variable (t : source_term F) : source_term F :=
  match t with
  | SBound i => SBound (if depth <=? i then S i else i)
  | SFree i => if i =? variable then SBound depth else SFree i
  | SApply s ts => SApply s (map (bind_term depth variable) ts)
  end.
Fixpoint bind_formula depth variable (f : source_formula F P) : source_formula F P :=
  match f with
  | STop => STop | SBot => SBot
  | SPred p ts => SPred p (map (bind_term depth variable) ts)
  | SEq x y => SEq (bind_term depth variable x) (bind_term depth variable y)
  | SNeg f => SNeg (bind_formula depth variable f)
  | SConj fs => SConj (map (bind_formula depth variable) fs)
  | SDisj fs => SDisj (map (bind_formula depth variable) fs)
  | SAll f => SAll (bind_formula (S depth) variable f)
  | SEx f => SEx (bind_formula (S depth) variable f)
  end.
End Abstraction.

Section Semantics.
Context {F P D : Type} (functions : F -> list D -> D) (predicates : P -> list D -> Prop).
Definition push (x : D) (rho : nat -> D) n := match n with 0 => x | S n => rho n end.
Fixpoint insert depth (x : D) (rho : nat -> D) : nat -> D :=
  match depth with
  | 0 => push x rho
  | S depth => fun n => match n with 0 => rho 0 | S n => insert depth x (fun i => rho (S i)) n end
  end.
Definition update (rho : nat -> D) variable x i := if i =? variable then x else rho i.
Fixpoint source_eval bound free (t : source_term F) : D :=
  match t with
  | SBound i => bound i | SFree i => free i
  | SApply s ts => functions s (map (source_eval bound free) ts)
  end.
Fixpoint source_holds bound free (f : source_formula F P) : Prop :=
  match f with
  | STop => True | SBot => False
  | SPred p ts => predicates p (map (source_eval bound free) ts)
  | SEq x y => source_eval bound free x = source_eval bound free y
  | SNeg f => ~ source_holds bound free f
  | SConj fs => (fix every fs := match fs with [] => True | f::fs => source_holds bound free f /\ every fs end) fs
  | SDisj fs => (fix some fs := match fs with [] => False | f::fs => source_holds bound free f \/ some fs end) fs
  | SAll f => forall x, source_holds (push x bound) free f
  | SEx f => exists x, source_holds (push x bound) free f
  end.
Lemma insert_at depth x rho : insert depth x rho depth = x.
Proof. revert rho. induction depth; intros; simpl; auto. Qed.
Lemma insert_shift depth i x rho :
  insert depth x rho (if depth <=? i then S i else i) = rho i.
Proof.
  revert i rho. induction depth; intros [|i] rho; simpl; auto.
  specialize (IHdepth i (fun n => rho (S n))).
  destruct (depth <=? i); simpl in *; exact IHdepth.
Qed.
Theorem term_abstraction : forall t depth variable bound free x,
  source_eval (insert depth x bound) free (bind_term depth variable t) =
  source_eval bound (update free variable x) t.
Proof.
  fix IH 1. intros [i|i|s ts] depth variable bound free x; simpl.
  - apply insert_shift.
  - unfold update. destruct (i =? variable); simpl; auto using insert_at.
  - f_equal. induction ts as [|t ts Hts]; simpl; [reflexivity|].
    rewrite IH, Hts. reflexivity.
Qed.
Theorem source_abstraction : forall f depth variable bound free x,
  source_holds (insert depth x bound) free (bind_formula depth variable f) <->
  source_holds bound (update free variable x) f.
Proof.
  fix IH 1. intros [| |p ts|s t|f|fs|fs|f|f] depth variable bound free x; simpl.
  - tauto.
  - tauto.
  - assert (H : map (source_eval (insert depth x bound) free) (map (bind_term depth variable) ts) =
        map (source_eval bound (update free variable x)) ts).
    { induction ts; simpl; [reflexivity|]. rewrite term_abstraction, IHts. reflexivity. }
    rewrite H. reflexivity.
  - rewrite !term_abstraction. reflexivity.
  - rewrite IH. reflexivity.
  - induction fs as [|f fs Hfs]; simpl.
    + tauto.
    + rewrite IH, Hfs. reflexivity.
  - induction fs as [|f fs Hfs]; simpl.
    + tauto.
    + rewrite IH, Hfs. reflexivity.
  - split; intros H y; apply (IH f (S depth) variable (push y bound) free x); apply H.
  - split; intros [y H]; exists y; apply (IH f (S depth) variable (push y bound) free x); exact H.
Qed.
Corollary source_universal_closure f variable bound free :
  source_holds bound free (SAll (bind_formula 0 variable f)) <->
  forall x, source_holds bound (update free variable x) f.
Proof.
  simpl. split; intros H x; apply (source_abstraction f 0 variable bound free x); apply H.
Qed.
Corollary source_existential_closure f variable bound free :
  source_holds bound free (SEx (bind_formula 0 variable f)) <->
  exists x, source_holds bound (update free variable x) f.
Proof.
  simpl. split; intros [x H]; exists x; apply (source_abstraction f 0 variable bound free x); exact H.
Qed.
End Semantics.
Print Assumptions source_scope_spec.
Print Assumptions source_abstraction.
Print Assumptions source_universal_closure.
Print Assumptions source_existential_closure.

(* SourceSubstitution *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Import ListNotations.

(* A replacement is expressed at the root of the formula. Under [depth]
   binders every bound index in that replacement must be lifted. Free
   parameters in the replacement are not themselves substituted. *)
Section Syntax.
Context {F P : Type}.
Fixpoint lift_term depth (t : source_term F) : source_term F :=
  match t with
  | SBound i => SBound (depth + i)
  | SFree i => SFree i
  | SApply s ts => SApply s (map (lift_term depth) ts)
  end.
Fixpoint substitute_term depth variable replacement (t : source_term F) : source_term F :=
  match t with
  | SBound i => SBound i
  | SFree i => if i =? variable then lift_term depth replacement else SFree i
  | SApply s ts => SApply s (map (substitute_term depth variable replacement) ts)
  end.
Fixpoint substitute_formula depth variable replacement (f : source_formula F P) : source_formula F P :=
  match f with
  | STop => STop | SBot => SBot
  | SPred p ts => SPred p (map (substitute_term depth variable replacement) ts)
  | SEq x y => SEq (substitute_term depth variable replacement x) (substitute_term depth variable replacement y)
  | SNeg f => SNeg (substitute_formula depth variable replacement f)
  | SConj fs => SConj (map (substitute_formula depth variable replacement) fs)
  | SDisj fs => SDisj (map (substitute_formula depth variable replacement) fs)
  | SAll f => SAll (substitute_formula (S depth) variable replacement f)
  | SEx f => SEx (substitute_formula (S depth) variable replacement f)
  end.
End Syntax.

Section Scope.
Context {F P : Type}.
Lemma lifting_scoped : forall (t : source_term F) depth scope,
  term_scoped scope false t = true -> term_scoped (depth + scope) false (lift_term depth t) = true.
Proof.
  fix IH 1. intros [i|i|s ts] depth scope; simpl.
  - rewrite !negb_true_iff, !Nat.leb_gt. apply Nat.add_lt_mono_l.
  - auto.
  - induction ts as [|t ts Hts]; simpl; [auto|].
    rewrite !andb_true_iff. intros [Ht Hs]. split; [apply IH|apply Hts]; assumption.
Qed.
Lemma term_substitution_scoped : forall (t : source_term F) depth scope variable replacement,
  term_scoped scope false replacement = true ->
  term_scoped (depth + scope) false t = true ->
  term_scoped (depth + scope) false (substitute_term depth variable replacement t) = true.
Proof.
  fix IH 1. intros [i|i|s ts] depth scope variable replacement Hr; simpl.
  - auto.
  - destruct (i =? variable); simpl; auto using lifting_scoped.
  - induction ts as [|t ts Hts]; simpl; [auto|].
    rewrite !andb_true_iff. intros [Ht Hs]. split; [apply IH|apply Hts]; assumption.
Qed.
Theorem source_substitution_scoped : forall (f : source_formula F P) depth scope variable replacement,
  term_scoped scope false replacement = true ->
  formula_scoped (depth + scope) false f = true ->
  formula_scoped (depth + scope) false (substitute_formula depth variable replacement f) = true.
Proof.
  fix IH 1. intros [| |p ts|s t|f|fs|fs|f|f] depth scope variable replacement Hr; simpl.
  - auto.
  - auto.
  - induction ts as [|t ts Hts]; simpl; [auto|].
    rewrite !andb_true_iff. intros [Ht Hs]. split; [apply term_substitution_scoped|apply Hts]; assumption.
  - rewrite !andb_true_iff. intros [Hs Ht]. split; apply term_substitution_scoped; assumption.
  - apply IH. exact Hr.
  - induction fs as [|f fs Hfs]; simpl; [auto|].
    rewrite !andb_true_iff. intros [Hf Hs]. split; [apply IH|apply Hfs]; assumption.
  - induction fs as [|f fs Hfs]; simpl; [auto|].
    rewrite !andb_true_iff. intros [Hf Hs]. split; [apply IH|apply Hfs]; assumption.
  - apply (IH f (S depth) scope variable replacement Hr).
  - apply (IH f (S depth) scope variable replacement Hr).
Qed.
End Scope.

Section Semantics.
Context {F P D : Type} (functions : F -> list D -> D) (predicates : P -> list D -> Prop).
Local Abbreviation eval := (source_eval functions).
Local Abbreviation holds := (source_holds functions predicates).

Theorem term_lifting : forall t depth bound free,
  eval bound free (lift_term depth t) = eval (fun i => bound (depth + i)) free t.
Proof.
  fix IH 1. intros [i|i|s ts] depth bound free; simpl; try reflexivity.
  f_equal. induction ts as [|t ts Hts]; simpl; [reflexivity|].
  rewrite IH, Hts. reflexivity.
Qed.

Theorem term_substitution : forall t depth variable replacement bound free,
  eval bound free (substitute_term depth variable replacement t) =
  eval bound (update free variable (eval (fun i => bound (depth + i)) free replacement)) t.
Proof.
  fix IH 1. intros [i|i|s ts] depth variable replacement bound free; simpl.
  - reflexivity.
  - unfold update. destruct (i =? variable); simpl; auto using term_lifting.
  - f_equal. induction ts as [|t ts Hts]; simpl; [reflexivity|].
    rewrite IH, Hts. reflexivity.
Qed.

Theorem source_substitution : forall f depth variable replacement bound free,
  holds bound free (substitute_formula depth variable replacement f) <->
  holds bound (update free variable (eval (fun i => bound (depth + i)) free replacement)) f.
Proof.
  fix IH 1. intros [| |p ts|s t|f|fs|fs|f|f] depth variable replacement bound free; simpl.
  - tauto.
  - tauto.
  - assert (H : map (eval bound free) (map (substitute_term depth variable replacement) ts) =
        map (eval bound (update free variable (eval (fun i => bound (depth + i)) free replacement))) ts).
    { induction ts; simpl; [reflexivity|]. rewrite term_substitution, IHts. reflexivity. }
    rewrite H. reflexivity.
  - rewrite !term_substitution. reflexivity.
  - rewrite IH. reflexivity.
  - induction fs as [|f fs Hfs]; simpl; [tauto|]. rewrite IH, Hfs. reflexivity.
  - induction fs as [|f fs Hfs]; simpl; [tauto|]. rewrite IH, Hfs. reflexivity.
  - split; intros H x; apply (IH f (S depth) variable replacement (push x bound) free); apply H.
  - split; intros [x H]; exists x; apply (IH f (S depth) variable replacement (push x bound) free); exact H.
Qed.

Corollary source_substitution_at_root f variable replacement bound free :
  holds bound free (substitute_formula 0 variable replacement f) <->
  holds bound (update free variable (eval bound free replacement)) f.
Proof. apply source_substitution. Qed.
End Semantics.
Print Assumptions term_lifting.
Print Assumptions source_substitution.
Print Assumptions source_substitution_scoped.

(* SourceBoolean *)
From Stdlib Require Import List Bool Arith.PeanoNat Sorting.Mergesort Sorting.Permutation Lia.
Import ListNotations.

(* A shallow view of an arena node. BKeep represents an opaque atom or
   quantifier when used as a view, and an existing node when used as a result.
   Natural-number handles keep sorting independent of arena ownership. *)
Inductive boolean_node :=
| BTrue | BFalse | BKeep (id : nat) | BNot (id : nat)
| BAnd (ids : list nat) | BOr (ids : list nat).

Module HandleOrder <: Orders.TotalLeBool'.
  Definition t := nat.
  Definition leb := Nat.leb.
  Lemma leb_total x y : leb x y = true \/ leb y x = true.
  Proof.
    unfold leb. destruct (x <=? y) eqn:E; [left; reflexivity|right].
    apply Nat.leb_le. apply Nat.leb_gt in E. lia.
  Qed.
End HandleOrder.
Module HandleSort := Mergesort.Sort HandleOrder.

Fixpoint unique_after previous ids :=
  match ids with
  | [] => []
  | id::ids => if previous =? id then unique_after previous ids else id::unique_after id ids
  end.
Definition unique_sorted ids :=
  match ids with [] => [] | id::ids => id::unique_after id ids end.
Definition sort_handles ids := unique_sorted (HandleSort.sort ids).

Lemma unique_after_members : forall ids previous id,
  In id (previous::unique_after previous ids) <-> In id (previous::ids).
Proof.
  induction ids as [|x xs IH]; intros previous id; simpl; [tauto|].
  destruct (previous =? x) eqn:E.
  - apply Nat.eqb_eq in E. subst. change (In id (x::unique_after x xs) <-> x=id \/ x=id \/ In id xs).
    rewrite IH. simpl. tauto.
  - specialize (IH x id). simpl in IH. simpl. tauto.
Qed.
Theorem sort_handles_members ids id : In id (sort_handles ids) <-> In id ids.
Proof.
  unfold sort_handles. assert (H : forall xs, In id (unique_sorted xs) <-> In id xs).
  { intros [|x xs]; simpl; [tauto|apply unique_after_members]. }
  rewrite H. split; apply Permutation_in; [apply Permutation_sym|]; apply HandleSort.Permuted_sort.
Qed.

Section Operations.
Variable view : nat -> boolean_node.
Definition flatten_and ids := flat_map (fun id => match view id with BAnd xs => xs | BTrue => [] | _ => [id] end) ids.
Definition flatten_or ids := flat_map (fun id => match view id with BOr xs => xs | BFalse => [] | _ => [id] end) ids.
Definition is_false id := match view id with BFalse => true | _ => false end.
Definition is_true id := match view id with BTrue => true | _ => false end.
Definition boolean_not id :=
  match view id with BTrue => BFalse | BFalse => BTrue | BNot x => BKeep x | _ => BNot id end.
Definition boolean_and ids :=
  let ids := flatten_and ids in
  if existsb is_false ids then BFalse else
  match sort_handles ids with [] => BTrue | [id] => BKeep id | ids => BAnd ids end.
Definition boolean_or ids :=
  let ids := flatten_or ids in
  if existsb is_true ids then BTrue else
  match sort_handles ids with [] => BFalse | [id] => BKeep id | ids => BOr ids end.
End Operations.

Section Semantics.
Variable holds : nat -> Prop.
Definition boolean_holds node :=
  match node with
  | BTrue => True | BFalse => False | BKeep id => holds id | BNot id => ~ holds id
  | BAnd ids => Forall holds ids | BOr ids => Exists holds ids
  end.
Variable view : nat -> boolean_node.
Hypothesis view_sound : forall id, holds id <-> boolean_holds (view id).

Lemma all_sort ids : Forall holds (sort_handles ids) <-> Forall holds ids.
Proof.
  rewrite !Forall_forall. split; intros H id Hi; apply H; apply sort_handles_members; exact Hi.
Qed.
Lemma any_sort ids : Exists holds (sort_handles ids) <-> Exists holds ids.
Proof.
  rewrite !Exists_exists. split; intros [id [Hi H]]; exists id; split; [apply sort_handles_members| |apply sort_handles_members|]; assumption.
Qed.
Lemma all_flatten ids : Forall holds (flatten_and view ids) <-> Forall holds ids.
Proof.
  induction ids as [|id ids IH]; simpl; [tauto|]. unfold flatten_and in *. simpl.
  rewrite Forall_app, IH, Forall_cons_iff. specialize (view_sound id).
  destruct (view id); simpl in *; try (rewrite Forall_cons_iff, Forall_nil_iff; tauto).
  - rewrite Forall_nil_iff. tauto.
  - tauto.
Qed.
Lemma any_flatten ids : Exists holds (flatten_or view ids) <-> Exists holds ids.
Proof.
  induction ids as [|id ids IH]; simpl; [tauto|]. unfold flatten_or in *. simpl.
  rewrite Exists_app, IH, Exists_cons. specialize (view_sound id).
  destruct (view id); simpl in *; try (rewrite Exists_cons, Exists_nil; tauto).
  - rewrite Exists_nil. tauto.
  - tauto.
Qed.
Lemma has_false ids : existsb (is_false view) ids = true -> ~ Forall holds ids.
Proof.
  rewrite existsb_exists. intros [id [Hi Hf]] Hall. rewrite Forall_forall in Hall.
  specialize (Hall id Hi). apply view_sound in Hall. unfold is_false in Hf.
  destruct (view id); simpl in *; discriminate || contradiction.
Qed.
Lemma has_true ids : existsb (is_true view) ids = true -> Exists holds ids.
Proof.
  rewrite existsb_exists. intros [id [Hi Ht]]. rewrite Exists_exists. exists id. split; [assumption|].
  apply view_sound. unfold is_true in Ht. destruct (view id); simpl in *; discriminate || tauto.
Qed.

Theorem boolean_and_correct ids : boolean_holds (boolean_and view ids) <-> Forall holds ids.
Proof.
  rewrite <- all_flatten. unfold boolean_and. destruct (existsb (is_false view) (flatten_and view ids)) eqn:E.
  - simpl. pose proof (has_false _ E). tauto.
  - rewrite <- all_sort. destruct (sort_handles (flatten_and view ids)) as [|x [|y ys]]; simpl;
      rewrite ?Forall_cons_iff, ?Forall_nil_iff; tauto.
Qed.
Theorem boolean_or_correct ids : boolean_holds (boolean_or view ids) <-> Exists holds ids.
Proof.
  rewrite <- any_flatten. unfold boolean_or. destruct (existsb (is_true view) (flatten_or view ids)) eqn:E.
  - simpl. pose proof (has_true _ E). tauto.
  - rewrite <- any_sort. destruct (sort_handles (flatten_or view ids)) as [|x [|y ys]]; simpl;
      rewrite ?Exists_cons, ?Exists_nil; tauto.
Qed.

(* Double-negation elimination is classical. As for NNF, keep the premise
   explicit instead of introducing a global axiom. And/Or need no such premise. *)
Theorem boolean_not_correct (excluded_middle : forall A : Prop, A \/ ~ A) id :
  boolean_holds (boolean_not view id) <-> ~ holds id.
Proof.
  unfold boolean_not. specialize (view_sound id). destruct (view id); simpl in *; try tauto.
  destruct (excluded_middle (holds id0)); tauto.
Qed.
End Semantics.
Print Assumptions sort_handles_members.
Print Assumptions boolean_and_correct.
Print Assumptions boolean_or_correct.
Check boolean_not_correct.
Print Assumptions boolean_not_correct.

(* AxiomSchema *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

Inductive schema_kind := Comprehension | Separation | Replacement | UnrestrictedSeparation.
Definition schema_arity kind := match kind with Replacement => 2 | _ => 1 end.

Section Syntax.
Context {F P : Type}.
Fixpoint term_parameters_below limit (t : source_term F) : bool :=
  match t with
  | SBound _ => true | SFree i => negb (limit <=? i)
  | SApply _ ts => forallb (term_parameters_below limit) ts
  end.
Fixpoint parameters_below limit (f : source_formula F P) : bool :=
  match f with
  | STop | SBot => true | SPred _ ts => forallb (term_parameters_below limit) ts
  | SEq x y => term_parameters_below limit x && term_parameters_below limit y
  | SNeg f | SAll f | SEx f => parameters_below limit f
  | SConj fs | SDisj fs => forallb (parameters_below limit) fs
  end.
Definition implication (f g : source_formula F P) := SDisj [SNeg f;g].
Definition equivalence (f g : source_formula F P) := SConj [implication f g;implication g f].
Definition all_free variable (f : source_formula F P) := SAll (bind_formula 0 variable f).
Definition ex_free variable (f : source_formula F P) := SEx (bind_formula 0 variable f).
Definition close_parameters variables (f : source_formula F P) := fold_right all_free f variables.
Definition replacement_unique fresh (phi : source_formula F P) :=
  let z := SFree (S (S fresh)) in
  all_free (S (S fresh)) (implication (substitute_formula 0 1 z phi) (SEq z (SFree 1))).
Definition replacement_functional fresh (phi : source_formula F P) :=
  all_free 0 (ex_free 1 (SConj [phi;replacement_unique fresh phi])).
Definition replacement_image member fresh (phi : source_formula F P) :=
  all_free fresh (ex_free (S fresh) (all_free 1
    (equivalence (SPred member [SFree 1;SFree (S fresh)])
      (ex_free 0 (SConj [SPred member [SFree 0;SFree fresh];phi]))))).

Definition schema_core kind member fresh (phi : source_formula F P) :=
  let x := SFree 0 in
  let set := SFree fresh in let result := SFree (S fresh) in
  match kind with
  | Comprehension | UnrestrictedSeparation =>
    ex_free (S fresh) (all_free 0 (equivalence (SPred member [x;result]) phi))
  | Separation =>
    all_free fresh (ex_free (S fresh) (all_free 0
      (equivalence (SPred member [x;result]) (SConj [SPred member [x;set];phi]))))
  | Replacement =>
    implication (replacement_functional fresh phi) (replacement_image member fresh phi)
  end.
Definition expand_schema kind member variables fresh phi :=
  close_parameters variables (schema_core kind member fresh phi).
Definition checked_schema kind member variables fresh phi :=
  if (schema_arity kind <=? fresh) && formula_scoped 0 false phi && parameters_below fresh phi then
    let f := expand_schema kind member variables fresh phi in
    if formula_scoped 0 true f then Some f else None
  else None.
End Syntax.

Section Semantics.
Context {F P D : Type} (functions : F -> list D -> D) (predicates : P -> list D -> Prop).
Local Abbreviation eval := (source_eval functions).
Local Abbreviation holds := (source_holds functions predicates).

Lemma term_parameters_agree : forall t limit bound free other,
  term_parameters_below limit t = true ->
  (forall i, i < limit -> free i = other i) -> eval bound free t = eval bound other t.
Proof.
  fix IH 1. intros [i|i|s ts] limit bound free other H Agree; simpl in *.
  - reflexivity.
  - apply Agree. apply negb_true_iff in H. now apply Nat.leb_gt in H.
  - f_equal. induction ts as [|t ts Hts]; simpl in *; [reflexivity|].
    apply andb_true_iff in H as [Ht Hs]. rewrite (IH t limit bound free other Ht Agree), (Hts Hs). reflexivity.
Qed.
Theorem source_parameters_agree : forall f limit bound free other,
  parameters_below limit f = true ->
  (forall i, i < limit -> free i = other i) -> (holds bound free f <-> holds bound other f).
Proof.
  fix IH 1. intros [| |p ts|s t|f|fs|fs|f|f] limit bound free other H Agree; simpl in *.
  - tauto.
  - tauto.
  - assert (E : map (eval bound free) ts = map (eval bound other) ts).
    { induction ts as [|t ts Hts]; simpl in *; [reflexivity|]. apply andb_true_iff in H as [Ht Hs].
      rewrite (term_parameters_agree t limit bound free other Ht Agree), (Hts Hs). reflexivity. }
    rewrite E. reflexivity.
  - apply andb_true_iff in H as [Hs Ht].
    rewrite (term_parameters_agree s limit bound free other Hs Agree), (term_parameters_agree t limit bound free other Ht Agree). reflexivity.
  - rewrite (IH f limit bound free other H Agree). reflexivity.
  - induction fs as [|f fs Hfs]; simpl in *; [tauto|]. apply andb_true_iff in H as [Hf Hs].
    rewrite (IH f limit bound free other Hf Agree), (Hfs Hs). reflexivity.
  - induction fs as [|f fs Hfs]; simpl in *; [tauto|]. apply andb_true_iff in H as [Hf Hs].
    rewrite (IH f limit bound free other Hf Agree), (Hfs Hs). reflexivity.
  - split; intros A x; apply (IH f limit (push x bound) free other H Agree); apply A.
  - split; intros [x A]; exists x; apply (IH f limit (push x bound) free other H Agree); exact A.
Qed.
Lemma all_free_holds variable f bound free :
  holds bound free (all_free variable f) <-> forall x, holds bound (update free variable x) f.
Proof. apply source_universal_closure. Qed.
Lemma ex_free_holds variable f bound free :
  holds bound free (ex_free variable f) <-> exists x, holds bound (update free variable x) f.
Proof. apply source_existential_closure. Qed.

Hypothesis excluded_middle : forall A : Prop, A \/ ~ A.
Lemma implication_holds f g bound free :
  holds bound free (implication f g) <-> (holds bound free f -> holds bound free g).
Proof. unfold implication. simpl. destruct (excluded_middle (holds bound free f)); tauto. Qed.
Lemma equivalence_holds f g bound free :
  holds bound free (equivalence f g) <-> (holds bound free f <-> holds bound free g).
Proof.
  change ((holds bound free (implication f g) /\ (holds bound free (implication g f) /\ True)) <->
    (holds bound free f <-> holds bound free g)).
  rewrite !implication_holds. tauto.
Qed.

Definition schema_meaning kind member (phi : source_formula F P) bound free :=
  let mem x y := predicates member [x;y] in
  let unary x := holds bound (update free 0 x) phi in
  let relation x y := holds bound (update (update free 0 x) 1 y) phi in
  match kind with
  | Comprehension | UnrestrictedSeparation => exists result, forall x, mem x result <-> unary x
  | Separation => forall set, exists result, forall x, mem x result <-> mem x set /\ unary x
  | Replacement =>
    (forall x, exists y, relation x y /\ forall z, relation x z -> z=y) ->
    forall set, exists result, forall y, mem y result <-> exists x, mem x set /\ relation x y
  end.

(* Extensional reasoning about environments is pointwise. No function
   extensionality is needed to remove the fresh set/result/uniqueness names. *)
Ltac environment :=
  unfold update; repeat match goal with
  | |- context [?i =? ?j] => destruct (Nat.eqb_spec i j); subst
  end; try reflexivity; lia.

Lemma comprehension_correct member fresh phi bound free :
  0 < fresh -> parameters_below fresh phi = true ->
  (holds bound free (schema_core Comprehension member fresh phi) <->
   schema_meaning Comprehension member phi bound free).
Proof.
  intros Fresh Scope. unfold schema_core, schema_meaning.
  rewrite ex_free_holds. setoid_rewrite all_free_holds. setoid_rewrite equivalence_holds.
  assert (Hphi : forall result x,
    holds bound (update (update free (S fresh) result) 0 x) phi <-> holds bound (update free 0 x) phi).
  { intros. apply (source_parameters_agree phi fresh); [assumption|]. intros i Hi. environment. }
  setoid_rewrite Hphi. simpl. unfold update. simpl.
  destruct fresh; [lia|]. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.
Lemma separation_correct member fresh phi bound free :
  0 < fresh -> parameters_below fresh phi = true ->
  (holds bound free (schema_core Separation member fresh phi) <->
   schema_meaning Separation member phi bound free).
Proof.
  intros Fresh Scope. unfold schema_core, schema_meaning.
  rewrite all_free_holds. setoid_rewrite ex_free_holds. setoid_rewrite all_free_holds.
  setoid_rewrite equivalence_holds. simpl.
  assert (Hphi : forall set result x,
    holds bound (update (update (update free fresh set) (S fresh) result) 0 x) phi <-> holds bound (update free 0 x) phi).
  { intros. apply (source_parameters_agree phi fresh); [assumption|]. intros i Hi. environment. }
  setoid_rewrite Hphi.
  assert (Hset : forall set result x, update (update (update free fresh set) (S fresh) result) 0 x fresh=set) by (intros; environment).
  assert (Hresult : forall set result x, update (update (update free fresh set) (S fresh) result) 0 x (S fresh)=result) by (intros; environment).
  setoid_rewrite Hset. setoid_rewrite Hresult. unfold update at 1. simpl.
  split; intros H set; destruct (H set) as [result Hresult']; exists result; intros x; specialize (Hresult' x); tauto.
Qed.

Lemma replacement_unique_correct fresh phi bound free x y :
  1 < fresh -> parameters_below fresh phi = true ->
  (holds bound (update (update free 0 x) 1 y) (replacement_unique fresh phi) <->
   forall z, holds bound (update (update free 0 x) 1 z) phi -> z=y).
Proof.
  intros Fresh Scope. unfold replacement_unique. rewrite all_free_holds.
  setoid_rewrite implication_holds. setoid_rewrite source_substitution_at_root.
  assert (Hz : forall z, eval bound (update (update (update free 0 x) 1 y) (S (S fresh)) z) (SFree (S (S fresh)))=z).
  { intros. simpl. unfold update. rewrite Nat.eqb_refl. reflexivity. }
  setoid_rewrite Hz.
  assert (Hphi : forall z,
    holds bound (update (update (update (update free 0 x) 1 y) (S (S fresh)) z) 1 z) phi <->
    holds bound (update (update free 0 x) 1 z) phi).
  { intros. apply (source_parameters_agree phi fresh); [assumption|]. intros i Hi. environment. }
  setoid_rewrite Hphi. simpl.
  assert (Hyz : forall z, update (update (update free 0 x) 1 y) (S (S fresh)) z (S (S fresh))=z) by (intros; environment).
  assert (Hy : forall z, update (update (update free 0 x) 1 y) (S (S fresh)) z 1=y) by (intros; environment).
  setoid_rewrite Hyz. setoid_rewrite Hy. reflexivity.
Qed.

Lemma replacement_functional_correct fresh phi bound free :
  1 < fresh -> parameters_below fresh phi = true ->
  (holds bound free (replacement_functional fresh phi) <->
   forall x, exists y, holds bound (update (update free 0 x) 1 y) phi /\
     forall z, holds bound (update (update free 0 x) 1 z) phi -> z=y).
Proof.
  intros Fresh Scope. unfold replacement_functional. rewrite all_free_holds. setoid_rewrite ex_free_holds.
  change ((forall x, exists y, holds bound (update (update free 0 x) 1 y) phi /\
    (holds bound (update (update free 0 x) 1 y) (replacement_unique fresh phi) /\ True)) <->
    forall x, exists y, holds bound (update (update free 0 x) 1 y) phi /\
      forall z, holds bound (update (update free 0 x) 1 z) phi -> z=y).
  setoid_rewrite (replacement_unique_correct fresh phi bound free _ _ Fresh Scope).
  split; intros H x; destruct (H x) as [y Hy]; exists y; tauto.
Qed.

Lemma replacement_image_correct member fresh phi bound free :
  1 < fresh -> parameters_below fresh phi = true ->
  (holds bound free (replacement_image member fresh phi) <->
   forall set, exists result, forall y, predicates member [y;result] <->
     exists x, predicates member [x;set] /\ holds bound (update (update free 0 x) 1 y) phi).
Proof.
  intros Fresh Scope. unfold replacement_image. rewrite all_free_holds.
  setoid_rewrite ex_free_holds. setoid_rewrite all_free_holds.
  setoid_rewrite equivalence_holds. setoid_rewrite ex_free_holds. simpl.
  assert (Hphi : forall set result y x,
    holds bound (update (update (update (update free fresh set) (S fresh) result) 1 y) 0 x) phi <->
    holds bound (update (update free 0 x) 1 y) phi).
  { intros. apply (source_parameters_agree phi fresh); [assumption|]. intros i Hi. environment. }
  setoid_rewrite Hphi.
  destruct fresh as [|[|fresh]]; try lia. unfold update. simpl.
  assert (E : (fresh =? S fresh)=false) by (apply Nat.eqb_neq;lia).
  rewrite Nat.eqb_refl, E.
  split; intros H set; destruct (H set) as [result Hr]; exists result; intros y; specialize (Hr y).
  - split; intros Hy'.
    + apply Hr in Hy'. destruct Hy' as [x Hx']. exists x. tauto.
    + apply Hr. destruct Hy' as [x Hx']. exists x. tauto.
  - split; intros Hy'.
    + apply Hr in Hy'. destruct Hy' as [x Hx']. exists x. tauto.
    + apply Hr. destruct Hy' as [x Hx']. exists x. tauto.
Qed.

Theorem schema_core_correct kind member fresh phi bound free :
  schema_arity kind <= fresh -> parameters_below fresh phi = true ->
  (holds bound free (schema_core kind member fresh phi) <-> schema_meaning kind member phi bound free).
Proof.
  destruct kind; simpl schema_arity; intros Fresh Scope.
  - apply comprehension_correct; [lia|assumption].
  - apply separation_correct; [lia|assumption].
  - change (holds bound free (implication (replacement_functional fresh phi) (replacement_image member fresh phi)) <->
      schema_meaning Replacement member phi bound free).
    rewrite implication_holds, (replacement_functional_correct fresh phi bound free ltac:(lia) Scope),
      (replacement_image_correct member fresh phi bound free ltac:(lia) Scope). reflexivity.
  - apply comprehension_correct; [lia|assumption].
Qed.

Fixpoint parameter_meaning variables (meaning : (nat -> D) -> Prop) free : Prop :=
  match variables with [] => meaning free | variable::variables => forall value, parameter_meaning variables meaning (update free variable value) end.
Lemma close_parameters_holds variables phi bound free :
  holds bound free (close_parameters variables phi) <-> parameter_meaning variables (fun free => holds bound free phi) free.
Proof.
  revert free. induction variables as [|v vs IH]; intros free; [reflexivity|].
  change (holds bound free (all_free v (close_parameters vs phi)) <-> forall x, parameter_meaning vs (fun free => holds bound free phi) (update free v x)).
  rewrite all_free_holds. split; intros H x; apply IH; apply H.
Qed.
Lemma parameter_meaning_iff variables A B :
  (forall free, A free <-> B free) -> forall free, parameter_meaning variables A free <-> parameter_meaning variables B free.
Proof.
  intros H. induction variables as [|v vs IH]; intros free; simpl; [apply H|].
  split; intros All x; apply IH; apply All.
Qed.
Theorem expand_schema_correct kind member variables fresh phi bound free :
  schema_arity kind <= fresh -> parameters_below fresh phi = true ->
  (holds bound free (expand_schema kind member variables fresh phi) <->
   parameter_meaning variables (schema_meaning kind member phi bound) free).
Proof.
  intros Fresh Scope. unfold expand_schema. rewrite close_parameters_holds.
  apply parameter_meaning_iff. intros other. apply schema_core_correct; assumption.
Qed.
Theorem checked_schema_correct kind member variables fresh phi result :
  checked_schema kind member variables fresh phi = Some result ->
  formula_wf 0 true result /\ forall bound free,
    holds bound free result <-> parameter_meaning variables (schema_meaning kind member phi bound) free.
Proof.
  unfold checked_schema. destruct (_ && _) eqn:E; [|discriminate].
  destruct (formula_scoped 0 true (expand_schema kind member variables fresh phi)) eqn:S; [|discriminate].
  intros H. inversion H; subst. split; [now apply source_scope_spec|].
  apply andb_true_iff in E as [E Scope]. apply andb_true_iff in E as [Fresh Scoped].
  apply Nat.leb_le in Fresh. intros. apply expand_schema_correct; assumption.
Qed.
End Semantics.
Check checked_schema_correct.
Print Assumptions source_parameters_agree.
Print Assumptions checked_schema_correct.
