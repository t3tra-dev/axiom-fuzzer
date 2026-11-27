(* Skolem *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Import ListNotations.

Fixpoint map_option {X Y : Type} (f : X -> option Y) xs : option (list Y) :=
  match xs with
  | [] => Some []
  | x::xs => match f x with
    | None => None
    | Some y => match map_option f xs with Some ys => Some (y::ys) | None => None end
    end
  end.

(* Substitute the current binder environment into an original-language term.
   The target type is abstract: the kernel uses Wire terms containing the
   independently allocated universal variables and Skolem applications. *)
Fixpoint instantiate_bound {F T : Type} (visit : unit -> bool)
  (apply : F -> list T -> T) (env : list T) (t : source_term F) : option T :=
  if visit tt then
    match t with
    | SBound i => nth_error env i
    | SFree _ => None
    | SApply f ts => match map_option (instantiate_bound visit apply env) ts with
      | Some args => Some (apply f args) | None => None end
    end
  else None.

Section BoundInstantiation.
Context {F T D : Type}.
Variable visit : unit -> bool.
Variable apply : F -> list T -> T.
Variable functions : F -> list D -> D.
Variable eval : T -> D.
Hypothesis apply_correct : forall f args, eval (apply f args)=functions f (map eval args).
Variable env : list T.
Variable bound free : nat -> D.
Hypothesis env_correct : forall i t, nth_error env i=Some t -> eval t=bound i.

Theorem instantiate_bound_correct : forall t result,
  instantiate_bound visit apply env t=Some result ->
  eval result=source_eval functions bound free t.
Proof.
  fix IH 1. intros [i|i|f ts] result; cbn [instantiate_bound]; destruct (visit tt); try discriminate.
  - apply env_correct.
  - destruct (map_option (instantiate_bound visit apply env) ts) as [args|] eqn:Args; [|discriminate].
    intros H. inversion H; subst. clear H. rewrite apply_correct. simpl. f_equal.
    revert args Args. induction ts as [|t ts Hts]; intros args; simpl.
    + intros E. inversion E. reflexivity.
    + destruct (instantiate_bound visit apply env t) as [x|] eqn:Term;
        destruct (map_option (instantiate_bound visit apply env) ts) as [xs|] eqn:Rest; try discriminate.
      intros E. inversion E; subst. simpl. rewrite (IH t x Term), (Hts xs eq_refl). reflexivity.
Qed.
Theorem instantiate_bound_scoped : forall t result,
  instantiate_bound visit apply env t=Some result -> term_scoped (length env) true t=true.
Proof.
  fix IH 1. intros [i|i|f ts] result; cbn [instantiate_bound]; destruct (visit tt); try discriminate.
  - intros H. simpl. rewrite negb_true_iff, Nat.leb_gt.
    apply nth_error_Some. rewrite H. discriminate.
  - destruct (map_option (instantiate_bound visit apply env) ts) as [args|] eqn:Args; [|discriminate].
    intros _. simpl. revert args Args. induction ts as [|t ts Hts]; intros args; simpl; [auto|].
    destruct (instantiate_bound visit apply env t) as [x|] eqn:Term;
      destruct (map_option (instantiate_bound visit apply env) ts) as [xs|] eqn:Rest; try discriminate.
    intros _. rewrite (IH t x Term), (Hts xs eq_refl). reflexivity.
Qed.
End BoundInstantiation.

Section WitnessFunctions.
Context {D : Type}.
Variable default : D.
(* These are explicit premises of the local Skolemization theorem, not global
   axioms and not premises of the clause-refutation checker. Choice selects one
   function for ALL argument vectors, including vectors with no witness. *)
Hypothesis excluded_middle : forall P : Prop, P \/ ~ P.
Hypothesis functional_choice : forall R : list D -> D -> Prop,
  (forall args, exists x, R args x) -> exists f, forall args, R args (f args).

Theorem uniform_witness (R : list D -> D -> Prop) :
  exists f, forall args, ((exists x, R args x) <-> R args (f args)).
Proof.
  assert (Total : forall args, exists x, (exists y, R args y) -> R args x).
  { intros args. destruct (excluded_middle (exists x, R args x)) as [[x H]|H].
    - exists x. auto.
    - exists default. tauto. }
  destruct (functional_choice (fun args x => (exists y, R args y) -> R args x) Total) as [f Hf].
  exists f. intros args. split; [apply Hf|intros H; exists (f args); exact H].
Qed.

Variable variables : list nat.
Variable body : (nat -> D) -> D -> Prop.
Hypothesis body_support : forall rho other x,
  (forall v, In v variables -> rho v=other v) -> (body rho x <-> body other x).

Theorem skolem_witness_on_support : exists f, forall rho,
  ((exists x, body rho x) <-> body rho (f (map rho variables))).
Proof.
  destruct (uniform_witness (fun args x => body (restore_variables default variables args) x)) as [f Hf].
  exists f. intros rho.
  assert (Agree : forall v, In v variables -> restore_variables default variables (map rho variables) v=rho v)
    by (intros; now apply restore_variables_correct).
  assert (Body : forall x, body (restore_variables default variables (map rho variables)) x <-> body rho x)
    by (intros; apply body_support; exact Agree).
  rewrite <- Body, <- Hf. split; intros [x H]; exists x; apply Body; assumption.
Qed.

(* This covers a single existential step under universally quantified
   parameters. Preprocess/SkolemModel.v connects it to the complete traversal, constructing
   one interpretation for every fresh symbol before universal erasure and CNF. *)
Corollary skolem_step_equisat :
  (forall rho, exists x, body rho x) <->
  exists f, forall rho, body rho (f (map rho variables)).
Proof.
  split.
  - intros H. destruct skolem_witness_on_support as [f Hf]. exists f. intros rho. apply Hf, H.
  - intros [f H] rho. exists (f (map rho variables)). apply H.
Qed.
End WitnessFunctions.
Print Assumptions instantiate_bound_correct.
Print Assumptions instantiate_bound_scoped.
Print Assumptions skolem_witness_on_support.
Print Assumptions skolem_step_equisat.

(* Universals *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Import ListNotations.

(* Existential witnesses have already been substituted, but universal binders
   remain explicit until their lexical scopes and fresh variable IDs are checked. *)
Inductive universal (L : Type) :=
| ULiteral : L -> universal L
| UConj : list (universal L) -> universal L
| UDisj : list (universal L) -> universal L
| UAll : nat -> universal L -> universal L.
Arguments ULiteral {L} _.
Arguments UConj {L} _.
Arguments UDisj {L} _.
Arguments UAll {L} _ _.

Fixpoint scope_list {X : Type} (check : nat -> X -> option nat) next xs :=
  match xs with
  | [] => Some next
  | x::xs => match check next x with
    | Some after => scope_list check after xs | None => None end
  end.

Section Syntax.
Context {L : Type}.
Fixpoint erase_universals (f : universal L) : matrix L :=
  match f with
  | ULiteral l => MLiteral l
  | UConj fs => MConj (map erase_universals fs)
  | UDisj fs => MDisj (map erase_universals fs)
  | UAll _ f => erase_universals f
  end.
Fixpoint universal_variables (support : L -> list nat) (f : universal L) :=
  match f with
  | ULiteral l => support l
  | UConj fs | UDisj fs => flat_map (universal_variables support) fs
  | UAll _ f => universal_variables support f
  end.
Fixpoint universal_scope (support : L -> list nat) allowed limit next (f : universal L) : option nat :=
  match f with
  | ULiteral l => if forallb (fun v => existsb (Nat.eqb v) allowed) (support l) then Some next else None
  | UConj fs | UDisj fs => scope_list (universal_scope support allowed limit) next fs
  | UAll v f => if (v =? next) && negb (limit <=? next)
    then universal_scope support (v::allowed) limit (S next) f else None
  end.
Definition checked_universals support limit f :=
  match universal_scope support [] limit 0 f with
  | Some _ => Some (erase_universals f) | None => None end.

Theorem universal_scope_monotone : forall f support allowed limit next after,
  universal_scope support allowed limit next f=Some after -> next<=after.
Proof.
  fix IH 1. intros [l|fs|fs|v f] support allowed limit next after; cbn [universal_scope].
  - destruct (forallb _ _); intros E; inversion E; lia.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl.
    + intros E; inversion E; lia.
    + destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
      intros Rest. specialize (Hfs middle after Rest). pose proof (IH f _ _ _ _ _ First). lia.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl.
    + intros E; inversion E; lia.
    + destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
      intros Rest. specialize (Hfs middle after Rest). pose proof (IH f _ _ _ _ _ First). lia.
  - destruct ((v =? next) && negb (limit <=? next)); [|discriminate].
    intros H. specialize (IH f _ _ _ _ _ H). lia.
Qed.
Theorem universal_scope_bounded : forall f support allowed limit next after,
  universal_scope support allowed limit next f=Some after -> next<=limit -> after<=limit.
Proof.
  fix IH 1. intros [l|fs|fs|v f] support allowed limit next after; cbn [universal_scope].
  - destruct (forallb _ _); intros E; inversion E; auto.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl.
    + intros E; inversion E; auto.
    + destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
      intros Rest Bound. apply (Hfs _ _ Rest). eapply IH; eauto.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl.
    + intros E; inversion E; auto.
    + destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
      intros Rest Bound. apply (Hfs _ _ Rest). eapply IH; eauto.
  - destruct ((v =? next) && negb (limit <=? next)) eqn:Fresh; [|discriminate].
    apply andb_true_iff in Fresh as [_ Bound]. apply negb_true_iff, Nat.leb_gt in Bound.
    intros Body _. apply (IH f _ _ _ _ _ Body). lia.
Qed.
Theorem universal_scope_variables : forall f support allowed limit next after,
  universal_scope support allowed limit next f=Some after ->
  (forall v, In v allowed -> v<next) ->
  forall v, In v (universal_variables support f) -> v<after.
Proof.
  fix IH 1. intros [l|fs|fs|v f] support allowed limit next after; cbn [universal_scope universal_variables].
  - destruct (forallb _ _) eqn:Vars; [|discriminate]. intros E Before x Hx. inversion E; subst.
    apply Before. rewrite forallb_forall in Vars. specialize (Vars x Hx).
    apply existsb_exists in Vars as [y [Hy Eq]]. apply Nat.eqb_eq in Eq. now subst.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl; [tauto|].
    destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
    intros Rest Before x Hx. apply in_app_or in Hx as [Hx|Hx].
    + pose proof (IH f _ _ _ _ _ First Before x Hx).
      pose proof (universal_scope_monotone (UConj fs) support allowed limit middle after Rest). lia.
    + apply (Hfs middle after Rest); [|exact Hx]. intros y Hy.
      pose proof (Before y Hy). pose proof (universal_scope_monotone f _ _ _ _ _ First). lia.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl; [tauto|].
    destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
    intros Rest Before x Hx. apply in_app_or in Hx as [Hx|Hx].
    + pose proof (IH f _ _ _ _ _ First Before x Hx).
      pose proof (universal_scope_monotone (UDisj fs) support allowed limit middle after Rest). lia.
    + apply (Hfs middle after Rest); [|exact Hx]. intros y Hy.
      pose proof (Before y Hy). pose proof (universal_scope_monotone f _ _ _ _ _ First). lia.
  - destruct ((v =? next) && negb (limit <=? next)) eqn:Fresh; [|discriminate].
    apply andb_true_iff in Fresh as [Eq _]. apply Nat.eqb_eq in Eq. subst v.
    intros Body Before x Hx. apply (IH f _ _ _ _ _ Body); [|exact Hx].
    intros y [Eq|Hy]; [subst; lia|]. specialize (Before y Hy). lia.
Qed.
End Syntax.

Section Semantics.
Context {L D : Type} (literal : (nat -> D) -> L -> Prop).
Fixpoint universal_holds rho (f : universal L) {struct f} : Prop :=
  match f with
  | ULiteral l => literal rho l
  | UConj fs => (fix every fs := match fs with [] => True | f::fs => universal_holds rho f /\ every fs end) fs
  | UDisj fs => (fix some fs := match fs with [] => False | f::fs => universal_holds rho f \/ some fs end) fs
  | UAll v f => forall x, universal_holds (update rho v x) f
  end.
Lemma universal_conj rho fs : universal_holds rho (UConj fs) <-> Forall (universal_holds rho) fs.
Proof. induction fs; simpl; [rewrite Forall_nil_iff|rewrite Forall_cons_iff, <- IHfs]; tauto. Qed.
Lemma universal_disj rho fs : universal_holds rho (UDisj fs) <-> AxiomFuzzer.Preprocess.NormalForms.clause_holds (universal_holds rho) fs.
Proof. induction fs; simpl; [tauto|rewrite IHfs; reflexivity]. Qed.
Lemma erased_conj rho fs : matrix_holds (literal rho) (erase_universals (UConj fs)) <->
  Forall (fun f => matrix_holds (literal rho) (erase_universals f)) fs.
Proof. induction fs; simpl; [rewrite Forall_nil_iff|rewrite Forall_cons_iff, <- IHfs]; tauto. Qed.
Lemma erased_disj rho fs : matrix_holds (literal rho) (erase_universals (UDisj fs)) <->
  AxiomFuzzer.Preprocess.NormalForms.clause_holds (fun f => matrix_holds (literal rho) (erase_universals f)) fs.
Proof. induction fs; simpl; [tauto|rewrite IHfs; reflexivity]. Qed.

Variable support : L -> list nat.
Hypothesis literal_support : forall l rho other,
  (forall v, In v (support l) -> rho v=other v) -> (literal rho l <-> literal other l).
Theorem erased_support : forall f rho other,
  (forall v, In v (universal_variables support f) -> rho v=other v) ->
  (matrix_holds (literal rho) (erase_universals f) <-> matrix_holds (literal other) (erase_universals f)).
Proof.
  fix IH 1. intros [l|fs|fs|v f] rho other Agree; cbn [erase_universals matrix_holds] in *.
  - apply literal_support, Agree.
  - induction fs as [|f fs Hfs]; simpl; [tauto|]. rewrite IH, Hfs; try reflexivity;
      intros x Hx; apply Agree; simpl; apply in_or_app; auto.
  - induction fs as [|f fs Hfs]; simpl; [tauto|]. rewrite IH, Hfs; try reflexivity;
      intros x Hx; apply Agree; simpl; apply in_or_app; auto.
  - apply IH, Agree.
Qed.
Theorem universal_scope_support : forall f allowed limit next after rho other,
  universal_scope support allowed limit next f=Some after ->
  (forall v, In v allowed -> rho v=other v) ->
  (universal_holds rho f <-> universal_holds other f).
Proof.
  fix IH 1. intros [l|fs|fs|v f] allowed limit next after rho other; cbn [universal_scope].
  - destruct (forallb _ _) eqn:Vars; [|discriminate]. intros _ Agree. apply literal_support.
    intros x Hx. apply Agree. rewrite forallb_forall in Vars. specialize (Vars x Hx).
    apply existsb_exists in Vars as [y [Hy E]]. apply Nat.eqb_eq in E. now subst.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl; [tauto|].
    destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
    intros Rest Agree. rewrite (IH f _ _ _ _ _ _ First Agree), (Hfs _ _ Rest Agree). reflexivity.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl; [tauto|].
    destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
    intros Rest Agree. rewrite (IH f _ _ _ _ _ _ First Agree), (Hfs _ _ Rest Agree). reflexivity.
  - destruct ((v =? next) && negb (limit <=? next)); [|discriminate].
    intros Body Agree. simpl.
    assert (Each : forall x, universal_holds (update rho v x) f <-> universal_holds (update other v x) f).
    { intros x. apply (IH f _ _ _ _ _ _ Body). intros y [E|Hy]; unfold update.
      - subst. now rewrite Nat.eqb_refl.
      - destruct (y =? v); [reflexivity|]. now apply Agree. }
    split; intros H x; apply Each, H.
Qed.

(* Pointwise evaluation of the universal formula implies its erased matrix.
   The stronger reverse direction below needs fresh scopes and classical logic. *)
Theorem erase_universals_forward : forall f allowed limit next after rho,
  universal_scope support allowed limit next f=Some after ->
  universal_holds rho f -> matrix_holds (literal rho) (erase_universals f).
Proof.
  fix IH 1. intros [l|fs|fs|v f] allowed limit next after rho; cbn [universal_scope].
  - auto.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl; [auto|].
    destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
    intros Rest [Hf Hfs']. split; [eapply IH; eauto|eapply Hfs; eauto].
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl; [auto|].
    destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
    intros Rest [Hf|Hfs']; [left; eapply IH; eauto|right; eapply Hfs; eauto].
  - destruct ((v =? next) && negb (limit <=? next)); [|discriminate]. intros Body Holds. simpl in *.
    apply (IH f _ _ _ _ rho Body).
    apply (universal_scope_support f _ _ _ _ (update rho v (rho v)) rho Body).
    + intros y _. unfold update. destruct (Nat.eqb_spec y v); subst; reflexivity.
    + apply Holds.
Qed.

Hypothesis excluded_middle : forall P : Prop, P \/ ~ P.
(* A false formula has a falsifying assignment for its erased matrix, without
   changing any variable allocated before this subtree. Disjunction combines
   counterassignments only across the disjoint fresh intervals of its children. *)
Theorem universal_counterassignment : forall f allowed limit next after rho,
  universal_scope support allowed limit next f=Some after ->
  (forall v, In v allowed -> v<next) -> ~ universal_holds rho f ->
  exists other, (forall v, v<next -> other v=rho v) /\
    ~ matrix_holds (literal other) (erase_universals f).
Proof.
  fix IH 1. intros [l|fs|fs|v f] allowed limit next after rho; cbn [universal_scope].
  - intros _ _ Not. exists rho. split; [reflexivity|exact Not].
  - revert next after rho. induction fs as [|f fs Hfs]; intros next after rho; simpl.
    + tauto.
    + destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
      intros Rest Before Not. destruct (excluded_middle (universal_holds rho f)) as [Yes|No].
      * assert (Before' : forall v, In v allowed -> v<middle).
        { intros x Hx. pose proof (Before x Hx). pose proof (universal_scope_monotone f _ _ _ _ _ First). lia. }
        destruct (Hfs middle after rho Rest Before') as [other [Keep FalseTail]]; [tauto|].
        exists other. split; [|tauto]. intros x Hx. apply Keep.
        pose proof (universal_scope_monotone f _ _ _ _ _ First). lia.
      * destruct (IH f _ _ _ _ rho First Before No) as [other [Keep FalseHead]].
        exists other. split; [exact Keep|tauto].
  - revert next after rho. induction fs as [|f fs Hfs]; intros next after rho; simpl.
    + intros _ _ _. exists rho. split; [reflexivity|tauto].
    + destruct (universal_scope support allowed limit next f) as [middle|] eqn:First; [|discriminate].
      intros Rest Before Not.
      assert (NoHead : ~ universal_holds rho f) by tauto.
      destruct (IH f _ _ _ _ rho First Before NoHead) as [one [KeepOne FalseHead]].
      assert (Before' : forall v, In v allowed -> v<middle).
      { intros x Hx. pose proof (Before x Hx). pose proof (universal_scope_monotone f _ _ _ _ _ First). lia. }
      assert (NoTail : ~ universal_holds one (UDisj fs)).
      { rewrite (universal_scope_support (UDisj fs) _ _ _ _ one rho Rest).
        - simpl. tauto.
        - intros x Hx. apply KeepOne, Before, Hx. }
      destruct (Hfs middle after one Rest Before' NoTail) as [other [KeepOther FalseTail]].
      exists other. split.
      * intros x Hx. rewrite KeepOther; [apply KeepOne; exact Hx|].
        pose proof (universal_scope_monotone f _ _ _ _ _ First). lia.
      * assert (SameHead : matrix_holds (literal one) (erase_universals f) <->
            matrix_holds (literal other) (erase_universals f)).
        { apply erased_support. intros x Hx. symmetry. apply KeepOther.
          eapply universal_scope_variables; eauto. }
        tauto.
  - destruct ((v =? next) && negb (limit <=? next)) eqn:Fresh; [|discriminate].
    apply andb_true_iff in Fresh as [Eq _]. apply Nat.eqb_eq in Eq. subst v.
    intros Body Before Not. simpl in Not.
    destruct (AxiomFuzzer.Preprocess.NormalForms.negated_universal excluded_middle _ Not) as [x NoBody].
    assert (Before' : forall v, In v (next::allowed) -> v<S next).
    { intros y [E|Hy]; [subst; lia|]. specialize (Before y Hy). lia. }
    destruct (IH f _ _ _ _ (update rho next x) Body Before' NoBody) as [other [Keep FalseBody]].
    exists other. split; [|exact FalseBody]. intros y Hy. rewrite Keep; [|lia].
    unfold update. destruct (Nat.eqb_spec y next); [lia|reflexivity].
Qed.

Theorem universal_erasure_correct f allowed limit next after rho :
  universal_scope support allowed limit next f=Some after ->
  (forall v, In v allowed -> v<next) ->
  (universal_holds rho f <-> forall other,
    (forall v, v<next -> other v=rho v) -> matrix_holds (literal other) (erase_universals f)).
Proof.
  intros Scope Before. split.
  - intros Holds other Agree. apply (erase_universals_forward f _ _ _ _ other Scope).
    apply (universal_scope_support f _ _ _ _ rho other Scope).
    + intros x Hx. symmetry. apply Agree, Before, Hx.
    + exact Holds.
  - intros Holds. destruct (excluded_middle (universal_holds rho f)) as [Yes|No]; [exact Yes|].
    destruct (universal_counterassignment f _ _ _ _ rho Scope Before No) as [other [Agree False]].
    exfalso. apply False, Holds, Agree.
Qed.
Theorem checked_universals_correct limit f m rho :
  checked_universals support limit f=Some m ->
  (universal_holds rho f <-> forall other, matrix_holds (literal other) m).
Proof.
  unfold checked_universals. destruct (universal_scope support [] limit 0 f) as [after|] eqn:Scope; [|discriminate].
  intros E. inversion E; subst.
  rewrite (universal_erasure_correct f [] limit 0 after rho Scope); [|simpl; tauto].
  split; intros H other; [apply H; lia|intros _; apply H].
Qed.
End Semantics.
Print Assumptions erase_universals_forward.
Print Assumptions universal_scope_bounded.
Print Assumptions universal_erasure_correct.
Print Assumptions checked_universals_correct.

(* Skolemize *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Import ListNotations.

Record supplied (X : Type) := {
  supplied_value : X;
  next_variable : nat;
  next_symbol : nat
}.
Arguments supplied_value {X} _.
Arguments next_variable {X} _.
Arguments next_symbol {X} _.
Definition supply {X : Type} (value : X) variable symbol :=
  {| supplied_value := value; next_variable := variable; next_symbol := symbol |}.

Fixpoint map_supply {X Y : Type} (compile : nat -> nat -> X -> option (supplied Y)) variable symbol xs
  : option (supplied (list Y)) :=
  match xs with
  | [] => Some (supply [] variable symbol)
  | x::xs => match compile variable symbol x with
    | None => None
    | Some first => match map_supply compile (next_variable first) (next_symbol first) xs with
      | None => None
      | Some rest => Some (supply (supplied_value first::supplied_value rest) (next_variable rest) (next_symbol rest))
      end
    end
  end.

Section Elimination.
Context {F P T L : Type}.
Variable visit : unit -> bool.
Variable apply : F -> list T -> T.
Variable variable : nat -> T.
Variable witness : nat -> list T -> T.
Variable predicate : bool -> P -> list T -> L.
Variable equality : bool -> T -> T -> L.
Variable limit : nat.

(* Supplies are threaded across siblings; binder environments and universal
   dependencies remain lexical. Check BEFORE incrementing a machine integer. *)
Fixpoint eliminate_quantifiers env universals next_v next_s (f : normal F P)
  : option (supplied (universal L)) :=
  if visit tt then
    match f with
    | NPred sign p ts => match map_option (instantiate_bound visit apply env) ts with
      | Some args => Some (supply (ULiteral (predicate sign p args)) next_v next_s) | None => None end
    | NEqual sign x y => match instantiate_bound visit apply env x with
      | None => None
      | Some x => match instantiate_bound visit apply env y with
        | Some y => Some (supply (ULiteral (equality sign x y)) next_v next_s) | None => None end
      end
    | NConj fs => match map_supply (eliminate_quantifiers env universals) next_v next_s fs with
      | Some r => Some (supply (UConj (supplied_value r)) (next_variable r) (next_symbol r)) | None => None end
    | NDisj fs => match map_supply (eliminate_quantifiers env universals) next_v next_s fs with
      | Some r => Some (supply (UDisj (supplied_value r)) (next_variable r) (next_symbol r)) | None => None end
    | NAll f => if negb (limit <=? next_v) then
      let term := variable next_v in
      match eliminate_quantifiers (term::env) (universals++[term]) (S next_v) next_s f with
      | Some r => Some (supply (UAll next_v (supplied_value r)) (next_variable r) (next_symbol r)) | None => None end
      else None
    | NEx f => if negb (limit <=? next_s) then
      eliminate_quantifiers (witness next_s universals::env) universals next_v (S next_s) f
      else None
    end
  else None.

(* A successful execution follows this explicit traversal relation. In
   particular, witnesses receive only the lexically enclosing universal terms,
   and each allocation advances the corresponding supply before descending. *)
Inductive quantifier_trace : list T -> list T -> nat -> nat -> normal F P -> universal L -> nat -> nat -> Prop :=
| QPred : forall env us v s sign p ts args,
    map_option (instantiate_bound visit apply env) ts=Some args ->
    quantifier_trace env us v s (NPred sign p ts) (ULiteral (predicate sign p args)) v s
| QEqual : forall env us v s sign x y a b,
    instantiate_bound visit apply env x=Some a -> instantiate_bound visit apply env y=Some b ->
    quantifier_trace env us v s (NEqual sign x y) (ULiteral (equality sign a b)) v s
| QConj : forall env us v s fs qs v' s',
    quantifier_traces env us v s fs qs v' s' -> quantifier_trace env us v s (NConj fs) (UConj qs) v' s'
| QDisj : forall env us v s fs qs v' s',
    quantifier_traces env us v s fs qs v' s' -> quantifier_trace env us v s (NDisj fs) (UDisj qs) v' s'
| QAll : forall env us v s f q v' s', v<limit ->
    quantifier_trace (variable v::env) (us++[variable v]) (S v) s f q v' s' ->
    quantifier_trace env us v s (NAll f) (UAll v q) v' s'
| QExists : forall env us v s f q v' s', s<limit ->
    quantifier_trace (witness s us::env) us v (S s) f q v' s' ->
    quantifier_trace env us v s (NEx f) q v' s'
with quantifier_traces : list T -> list T -> nat -> nat -> list (normal F P) -> list (universal L) -> nat -> nat -> Prop :=
| QNil : forall env us v s, quantifier_traces env us v s [] [] v s
| QCons : forall env us v s f fs q qs middle_v middle_s v' s',
    quantifier_trace env us v s f q middle_v middle_s ->
    quantifier_traces env us middle_v middle_s fs qs v' s' ->
    quantifier_traces env us v s (f::fs) (q::qs) v' s'.
Scheme trace_ind := Induction for quantifier_trace Sort Prop
with traces_ind := Induction for quantifier_traces Sort Prop.
Combined Scheme traces_mutind from trace_ind, traces_ind.

Theorem eliminate_quantifiers_trace : forall f env us v s r,
  eliminate_quantifiers env us v s f=Some r ->
  quantifier_trace env us v s f (supplied_value r) (next_variable r) (next_symbol r).
Proof.
  fix IH 1. intros [sign p ts|sign x y|fs|fs|f|f] env us v s r;
    cbn [eliminate_quantifiers]; destruct (visit tt); try discriminate.
  - destruct (map_option _ ts) as [args|] eqn:Args; [|discriminate].
    intros E. inversion E; subst; simpl. constructor. exact Args.
  - destruct (instantiate_bound visit apply env x) as [a|] eqn:X; [|discriminate].
    destruct (instantiate_bound visit apply env y) as [b|] eqn:Y; [|discriminate].
    intros E. inversion E; subst; simpl. constructor; assumption.
  - destruct (map_supply _ v s fs) as [out|] eqn:Out; [|discriminate].
    intros E. inversion E; subst; simpl. constructor. clear E.
    revert v s out Out. induction fs as [|f fs Hfs]; intros v s out; simpl.
    + intros E. inversion E; subst; simpl. constructor.
    + destruct (eliminate_quantifiers env us v s f) as [first|] eqn:First; [|discriminate].
      destruct (map_supply _ _ _ fs) as [rest|] eqn:Rest; [|discriminate].
      intros E. inversion E; subst; simpl. econstructor; [apply IH; exact First|apply Hfs; exact Rest].
  - destruct (map_supply _ v s fs) as [out|] eqn:Out; [|discriminate].
    intros E. inversion E; subst; simpl. constructor. clear E.
    revert v s out Out. induction fs as [|f fs Hfs]; intros v s out; simpl.
    + intros E. inversion E; subst; simpl. constructor.
    + destruct (eliminate_quantifiers env us v s f) as [first|] eqn:First; [|discriminate].
      destruct (map_supply _ _ _ fs) as [rest|] eqn:Rest; [|discriminate].
      intros E. inversion E; subst; simpl. econstructor; [apply IH; exact First|apply Hfs; exact Rest].
  - destruct (negb (limit <=? v)) eqn:Bound; [|discriminate].
    destruct (eliminate_quantifiers (variable v::env) (us++[variable v]) (S v) s f) as [out|] eqn:Out; [|discriminate].
    intros E. inversion E; subst; simpl. constructor; [apply negb_true_iff, Nat.leb_gt in Bound; exact Bound|].
    apply IH, Out.
  - destruct (negb (limit <=? s)) eqn:Bound; [|discriminate]. intros Out.
    constructor; [apply negb_true_iff, Nat.leb_gt in Bound; exact Bound|]. apply IH, Out.
Qed.

Fixpoint quantifier_count (count_all : bool) (f : normal F P) :=
  match f with
  | NPred _ _ _ | NEqual _ _ _ => 0
  | NConj fs | NDisj fs => fold_right (fun f n => quantifier_count count_all f+n) 0 fs
  | NAll f => (if count_all then 1 else 0)+quantifier_count count_all f
  | NEx f => (if count_all then 0 else 1)+quantifier_count count_all f
  end.

Theorem quantifier_trace_counts :
  (forall env us v s f q v' s', quantifier_trace env us v s f q v' s' ->
    v'=v+quantifier_count true f /\ s'=s+quantifier_count false f) /\
  (forall env us v s fs qs v' s', quantifier_traces env us v s fs qs v' s' ->
    v'=v+fold_right (fun f n => quantifier_count true f+n) 0 fs /\
    s'=s+fold_right (fun f n => quantifier_count false f+n) 0 fs).
Proof. apply traces_mutind; simpl; intros; lia. Qed.

Theorem quantifier_trace_bounds :
  (forall env us v s f q v' s', quantifier_trace env us v s f q v' s' ->
    v<=limit -> s<=limit -> v'<=limit /\ s'<=limit) /\
  (forall env us v s fs qs v' s', quantifier_traces env us v s fs qs v' s' ->
    v<=limit -> s<=limit -> v'<=limit /\ s'<=limit).
Proof. apply traces_mutind; simpl; intros; lia. Qed.
Lemma instantiated_terms_scoped env ts args :
  map_option (instantiate_bound visit apply env) ts=Some args ->
  forallb (term_scoped (length env) true) ts=true.
Proof.
  revert args. induction ts as [|t ts IH]; intros args; simpl; [auto|].
  destruct (instantiate_bound visit apply env t) as [x|] eqn:Term; [|discriminate].
  destruct (map_option (instantiate_bound visit apply env) ts) as [xs|] eqn:Rest; [|discriminate].
  intros _. rewrite (instantiate_bound_scoped visit apply env t x Term), (IH xs eq_refl). reflexivity.
Qed.
Theorem quantifier_trace_scoped :
  (forall env us v s f q v' s', quantifier_trace env us v s f q v' s' ->
    normal_scoped (length env) true f=true) /\
  (forall env us v s fs qs v' s', quantifier_traces env us v s fs qs v' s' ->
    forallb (normal_scoped (length env) true) fs=true).
Proof.
  apply traces_mutind; simpl; intros; auto.
  - eapply instantiated_terms_scoped; eauto.
  - rewrite (instantiate_bound_scoped visit apply env x a e), (instantiate_bound_scoped visit apply env y b e0). reflexivity.
  - now rewrite H, H0.
Qed.
Corollary eliminate_quantifiers_counts f env us v s r :
  eliminate_quantifiers env us v s f=Some r ->
  next_variable r=v+quantifier_count true f /\ next_symbol r=s+quantifier_count false f.
Proof. intros H. apply eliminate_quantifiers_trace in H. eapply (proj1 quantifier_trace_counts); eauto. Qed.
Corollary eliminate_quantifiers_bounds f env us v s r :
  eliminate_quantifiers env us v s f=Some r -> v<=limit -> s<=limit ->
  next_variable r<=limit /\ next_symbol r<=limit.
Proof. intros H. apply eliminate_quantifiers_trace in H. eapply (proj1 quantifier_trace_bounds); eauto. Qed.
Corollary eliminate_quantifiers_scoped f env us v s r :
  eliminate_quantifiers env us v s f=Some r -> normal_scoped (length env) true f=true.
Proof. intros H. apply eliminate_quantifiers_trace in H. eapply (proj1 quantifier_trace_scoped); eauto. Qed.
End Elimination.
Print Assumptions eliminate_quantifiers_trace.
Print Assumptions eliminate_quantifiers_counts.
Print Assumptions eliminate_quantifiers_bounds.
Print Assumptions eliminate_quantifiers_scoped.
