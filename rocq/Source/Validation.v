(* The authority boundary uses portable Source trees, never arena handles. *)
From Stdlib Require Import List Bool Arith.PeanoNat String Lia.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition formula := source_formula string string.
Definition term := source_term string.

Fixpoint term_equal (a b : term) : bool :=
  match a,b with
  | SBound i,SBound j | SFree i,SFree j => Nat.eqb i j
  | SApply f xs,SApply g ys => String.eqb f g && forallb2 term_equal xs ys
  | _,_ => false
  end.
Lemma term_equal_sound : forall a b, term_equal a b=true -> a=b.
Proof.
  fix IH 1. intros a b. destruct a,b; simpl; try discriminate.
  - intros E. apply Nat.eqb_eq in E; now subst.
  - intros E. apply Nat.eqb_eq in E; now subst.
  - rewrite andb_true_iff. intros [E Args]. apply String.eqb_eq in E; subst.
    f_equal. revert l0 Args. induction l as [|x xs Hxs]; intros [|y ys]; simpl; try discriminate; auto.
    rewrite andb_true_iff. intros [Head Tail]. f_equal; [now apply IH|now apply Hxs].
Qed.
Lemma terms_equal_sound xs ys : forallb2 term_equal xs ys=true -> xs=ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl; try discriminate; auto.
  rewrite andb_true_iff. intros [H T]. f_equal; [now apply term_equal_sound|now apply IH].
Qed.

(* Comparison modulo permutation and repetition of conjunction/disjunction.
   This checks equivalence, rather than trusting an arena's numeric ordering. *)
Fixpoint formula_equal (a b : formula) : bool :=
  match a,b with
  | STop,STop | SBot,SBot => true
  | SPred p xs,SPred q ys => String.eqb p q && forallb2 term_equal xs ys
  | SEq x y,SEq u v => term_equal x u && term_equal y v
  | SNeg f,SNeg g | SAll f,SAll g | SEx f,SEx g => formula_equal f g
  | SConj fs,SConj gs | SDisj fs,SDisj gs =>
      forallb (fun f => existsb (formula_equal f) gs) fs &&
      forallb (fun g => existsb (fun f => formula_equal f g) fs) gs
  | _,_ => false
  end.

Fixpoint deduplicate fs := match fs with
  | [] => []
  | f::fs => if existsb (formula_equal f) fs then deduplicate fs else f::deduplicate fs
  end.
Definition and_parts (f : formula) := match f with STop => [] | SConj fs => fs | _ => [f] end.
Definition or_parts (f : formula) := match f with SBot => [] | SDisj fs => fs | _ => [f] end.
Definition is_bottom (f : formula) := match f with SBot => true | _ => false end.
Definition is_top (f : formula) := match f with STop => true | _ => false end.
Definition smart_and fs :=
  let fs := deduplicate (flat_map and_parts fs) in
  if existsb is_bottom fs then SBot else match fs with [] => STop | [f] => f | _ => SConj fs end.
Definition smart_or fs :=
  let fs := deduplicate (flat_map or_parts fs) in
  if existsb is_top fs then STop else match fs with [] => SBot | [f] => f | _ => SDisj fs end.
Definition smart_not (f : formula) :=
  match f with STop => SBot | SBot => STop | SNeg g => g | _ => SNeg f end.
Fixpoint simplify (f : formula) : formula :=
  match f with
  | SNeg f => smart_not (simplify f)
  | SConj fs => smart_and (map simplify fs)
  | SDisj fs => smart_or (map simplify fs)
  | SAll f => SAll (simplify f) | SEx f => SEx (simplify f)
  | _ => f
  end.
(* The usual certificate contains the exact original tree. Check that in one
   traversal before paying for permutation/repetition-insensitive comparison. *)
Fixpoint formula_identical (a b : formula) : bool := match a,b with
  | STop,STop | SBot,SBot => true
  | SPred p xs,SPred q ys => String.eqb p q && forallb2 term_equal xs ys
  | SEq x y,SEq u v => term_equal x u && term_equal y v
  | SNeg f,SNeg g | SAll f,SAll g | SEx f,SEx g => formula_identical f g
  | SConj fs,SConj gs | SDisj fs,SDisj gs => forallb2 formula_identical fs gs
  | _,_ => false end.
Lemma formula_identical_sound : forall a b, formula_identical a b=true -> a=b.
Proof.
  fix IH 1. intros a b H. destruct a,b; simpl in H; try discriminate; try reflexivity.
  - apply andb_true_iff in H as [H Args]. apply String.eqb_eq in H.
    apply terms_equal_sound in Args; now subst.
  - apply andb_true_iff in H as [X Y]. apply term_equal_sound in X,Y; now subst.
  - f_equal; now apply IH.
  - f_equal. revert l0 H. induction l as [|f fs Rest]; intros [|g gs] H; simpl in H; try discriminate; [reflexivity|].
    apply andb_true_iff in H as [Head Tail]. f_equal; [now apply IH|now apply Rest].
  - f_equal. revert l0 H. induction l as [|f fs Rest]; intros [|g gs] H; simpl in H; try discriminate; [reflexivity|].
    apply andb_true_iff in H as [Head Tail]. f_equal; [now apply IH|now apply Rest].
  - f_equal; now apply IH.
  - f_equal; now apply IH.
Qed.
Definition equivalent a b := if formula_identical a b then true else formula_equal (simplify a) (simplify b).

Lemma term_equal_refl : forall t, term_equal t t=true.
Proof.
  fix IH 1; intros [i|i|f ts]; simpl; rewrite ?Nat.eqb_refl, ?String.eqb_refl; try reflexivity.
  induction ts as [|t ts Rest]; simpl; [reflexivity|now rewrite IH,Rest].
Qed.
Lemma formula_equal_refl : forall f, formula_equal f f=true.
Proof.
  fix IH 1; intros [| |p ts|x y|f|fs|fs|f|f]; simpl; try reflexivity; try apply IH.
  - rewrite String.eqb_refl; simpl. induction ts as [|t ts Rest]; simpl; [reflexivity|now rewrite term_equal_refl,Rest].
  - now rewrite !term_equal_refl.
  - assert (Children : Forall (fun f => formula_equal f f=true) fs).
    { induction fs; constructor; auto. }
    apply andb_true_iff; split; apply forallb_forall; intros f In;
      apply existsb_exists; exists f; split; try assumption;
      exact (proj1 (Forall_forall _ _) Children f In).
  - assert (Children : Forall (fun f => formula_equal f f=true) fs).
    { induction fs; constructor; auto. }
    apply andb_true_iff; split; apply forallb_forall; intros f In;
      apply existsb_exists; exists f; split; try assumption;
      exact (proj1 (Forall_forall _ _) Children f In).
Qed.
Theorem equivalent_spec a b : equivalent a b=formula_equal (simplify a) (simplify b).
Proof.
  unfold equivalent. destruct (formula_identical a b) eqn:E; [|reflexivity].
  apply formula_identical_sound in E; subst. symmetry; apply formula_equal_refl.
Qed.
Lemma equivalent_refl f : equivalent f f=true.
Proof. rewrite equivalent_spec; apply formula_equal_refl. Qed.

Section Meaning.
Context {U : Type}.
Variable functions : string -> list U -> U.
Variable predicates : string -> list U -> Prop.
Local Abbreviation holds := (source_holds functions predicates).
Lemma holds_and fs bound free : holds bound free (SConj fs) <-> Forall (holds bound free) fs.
Proof. induction fs; simpl; rewrite ?Forall_cons_iff, ?Forall_nil_iff; tauto. Qed.
Lemma holds_or fs bound free : holds bound free (SDisj fs) <-> Exists (holds bound free) fs.
Proof. induction fs; simpl; rewrite ?Exists_cons, ?Exists_nil; tauto. Qed.
Lemma formula_equal_sound : forall a b, formula_equal a b=true ->
  forall bound free, holds bound free a <-> holds bound free b.
Proof.
  fix IH 1. intros a b E bound free. destruct a,b; simpl in E; try discriminate; try reflexivity.
  - apply andb_true_iff in E as [E Args]. apply String.eqb_eq in E.
    apply terms_equal_sound in Args. now subst.
  - apply andb_true_iff in E as [X Y]. apply term_equal_sound in X,Y. now subst.
  - simpl. now rewrite (IH a b E).
  - assert (Children : Forall (fun f => forall g, formula_equal f g=true -> forall bound free,
        holds bound free f <-> holds bound free g) l).
    { clear E. induction l as [|f fs Hfs].
      - constructor.
      - constructor; [apply IH|exact Hfs]. }
    rewrite Forall_forall in Children.
    rewrite !holds_and, !Forall_forall. apply andb_true_iff in E as [AB BA].
    rewrite List.forallb_forall in AB,BA. split; intros H f In.
    + specialize (BA f In). apply existsb_exists in BA as [g [Ing Eq]].
      apply (Children g Ing f Eq bound free). now apply H.
    + specialize (AB f In). apply existsb_exists in AB as [g [Ing Eq]].
      apply (Children f In g Eq bound free). now apply H.
  - assert (Children : Forall (fun f => forall g, formula_equal f g=true -> forall bound free,
        holds bound free f <-> holds bound free g) l).
    { clear E. induction l as [|f fs Hfs].
      - constructor.
      - constructor; [apply IH|exact Hfs]. }
    rewrite Forall_forall in Children.
    rewrite !holds_or, !Exists_exists. apply andb_true_iff in E as [AB BA].
    rewrite List.forallb_forall in AB,BA. split; intros [f [In H]].
    + specialize (AB f In). apply existsb_exists in AB as [g [Ing Eq]].
      exists g; split; [exact Ing|]. now apply (Children f In g Eq bound free).
    + specialize (BA f In). apply existsb_exists in BA as [g [Ing Eq]].
      exists g; split; [exact Ing|]. now apply (Children g Ing f Eq bound free).
  - simpl. split; intros H x; apply (IH a b E); apply H.
  - simpl. split; intros [x H]; exists x; apply (IH a b E); exact H.
Qed.
Lemma deduplicate_all fs bound free :
  Forall (holds bound free) (deduplicate fs) <-> Forall (holds bound free) fs.
Proof.
  induction fs as [|f fs IH]; simpl; [tauto|]. destruct (existsb (formula_equal f) fs) eqn:E.
  - rewrite IH, Forall_cons_iff. apply existsb_exists in E as [g [In Eq]].
    rewrite (formula_equal_sound f g Eq). split; [|tauto]. intros All. split; [|exact All].
    now apply (proj1 (Forall_forall _ _) All g).
  - rewrite !Forall_cons_iff, IH. reflexivity.
Qed.
Lemma deduplicate_any fs bound free :
  Exists (holds bound free) (deduplicate fs) <-> Exists (holds bound free) fs.
Proof.
  induction fs as [|f fs IH]; simpl; [tauto|]. destruct (existsb (formula_equal f) fs) eqn:E.
  - rewrite IH, Exists_cons. apply existsb_exists in E as [g [In Eq]].
    rewrite (formula_equal_sound f g Eq). split; [tauto|]. intros [H|H]; [|exact H].
    apply Exists_exists; exists g; auto.
  - rewrite !Exists_cons, IH. reflexivity.
Qed.
Lemma smart_and_sound fs bound free : holds bound free (smart_and fs) <-> Forall (holds bound free) fs.
Proof.
  assert (Flat : Forall (holds bound free) (flat_map and_parts fs) <-> Forall (holds bound free) fs).
  { induction fs as [|f fs IH]; simpl; [tauto|]. rewrite Forall_app, IH, Forall_cons_iff.
    destruct f; simpl and_parts; rewrite ?Forall_cons_iff, ?Forall_nil_iff; try tauto. rewrite <- holds_and. tauto. }
  rewrite <- Flat, <- deduplicate_all. unfold smart_and. set (xs := deduplicate (flat_map and_parts fs)).
  destruct (existsb is_bottom xs) eqn:Bottom.
  - simpl. split; [tauto|]. intros All. apply existsb_exists in Bottom as [f [In B]].
    rewrite Forall_forall in All. specialize (All f In). destruct f; simpl in B; discriminate || assumption.
  - destruct xs as [|f [|g xs]]; simpl; rewrite ?Forall_cons_iff, ?Forall_nil_iff, <- ?holds_and; tauto.
Qed.
Lemma smart_or_sound fs bound free : holds bound free (smart_or fs) <-> Exists (holds bound free) fs.
Proof.
  assert (Flat : Exists (holds bound free) (flat_map or_parts fs) <-> Exists (holds bound free) fs).
  { induction fs as [|f fs IH]; simpl; [rewrite !Exists_nil; tauto|]. rewrite Exists_app, IH, Exists_cons.
    destruct f; simpl or_parts; rewrite ?Exists_cons, ?Exists_nil; try tauto. rewrite <- holds_or. tauto. }
  rewrite <- Flat, <- deduplicate_any. unfold smart_or. set (xs := deduplicate (flat_map or_parts fs)).
  destruct (existsb is_top xs) eqn:Top.
  - simpl. split; [|tauto]. intros _. apply existsb_exists in Top as [f [In T]].
    apply Exists_exists. exists f; split; [exact In|]. destruct f; simpl in T; discriminate || exact I.
  - destruct xs as [|f [|g xs]]; simpl; rewrite ?Exists_cons, ?Exists_nil, <- ?holds_or; tauto.
Qed.
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.
Lemma smart_not_sound f bound free : holds bound free (smart_not f) <-> ~holds bound free f.
Proof. destruct f; simpl; try tauto. destruct (excluded_middle (holds bound free f)); tauto. Qed.
Theorem simplify_sound : forall f bound free, holds bound free (simplify f) <-> holds bound free f.
Proof.
  fix IH 1. intros f bound free. destruct f; simpl simplify; try reflexivity.
  - rewrite smart_not_sound, IH. reflexivity.
  - rewrite smart_and_sound, holds_and, Forall_map.
    induction l; rewrite ?Forall_cons_iff, ?Forall_nil_iff; [tauto|]. rewrite IH, IHl. reflexivity.
  - rewrite smart_or_sound, holds_or, Exists_map.
    induction l; rewrite ?Exists_cons, ?Exists_nil; [tauto|]. rewrite IH, IHl. reflexivity.
  - simpl. split; intros H x; apply IH; apply H.
  - simpl. split; intros [x H]; exists x; apply IH; exact H.
Qed.
Theorem equivalent_sound a b : equivalent a b=true ->
  forall bound free, holds bound free a <-> holds bound free b.
Proof. rewrite equivalent_spec. intros E bound free. rewrite <- (simplify_sound a), <- (simplify_sound b). now apply formula_equal_sound. Qed.
End Meaning.

(* Signature and scope checks run on the raw tree before simplification. *)
Definition symbol_present symbols name arity :=
  existsb (fun entry => String.eqb name (fst entry) && Nat.eqb arity (snd entry)) symbols.
Fixpoint term_signature symbols (t : term) : bool :=
  match t with
  | SBound i | SFree i => 0 <=? i
  | SApply f ts => symbol_present symbols f (List.length ts) && forallb (term_signature symbols) ts
  end.
Fixpoint formula_signature functions predicates (f : formula) : bool :=
  match f with
  | STop | SBot => true
  | SPred p ts => symbol_present predicates p (List.length ts) && forallb (term_signature functions) ts
  | SEq x y => term_signature functions x && term_signature functions y
  | SNeg f | SAll f | SEx f => formula_signature functions predicates f
  | SConj fs | SDisj fs => forallb (formula_signature functions predicates) fs
  end.
Fixpoint term_parameters (t : term) : list nat :=
  match t with SBound _ => [] | SFree i => [i] | SApply _ ts => flat_map term_parameters ts end.
Fixpoint formula_parameters (f : formula) : list nat :=
  match f with
  | STop | SBot => [] | SPred _ ts => flat_map term_parameters ts
  | SEq x y => term_parameters x ++ term_parameters y
  | SNeg f | SAll f | SEx f => formula_parameters f
  | SConj fs | SDisj fs => flat_map formula_parameters fs
  end.

Inductive schema := ComprehensionSchema | SeparationSchema | ReplacementSchema | UnrestrictedSchema
  | RegisteredSchema (name revision : string).
Inductive provenance := FixedAxiom (name : string) | ImportedAxiom (name : string)
  | SchemaInstance (kind : schema) (condition : formula)
  | RegisteredInstance (name revision data : string).
Record axiom := { axiom_id : nat; axiom_name : string; axiom_origin : provenance; axiom_formula : formula }.
Definition builtin kind := match kind with
  | ComprehensionSchema => Some Comprehension | SeparationSchema => Some Separation
  | ReplacementSchema => Some Replacement | UnrestrictedSchema => Some UnrestrictedSeparation
  | RegisteredSchema _ _ => None end.
Definition schema_equal x y := match x,y with
  | ComprehensionSchema,ComprehensionSchema | SeparationSchema,SeparationSchema
  | ReplacementSchema,ReplacementSchema | UnrestrictedSchema,UnrestrictedSchema => true
  | RegisteredSchema n r,RegisteredSchema m s => String.eqb n m && String.eqb r s
  | _,_ => false end.
Lemma schema_equal_sound x y : schema_equal x y=true -> x=y.
Proof. destruct x,y; simpl; try discriminate; auto. rewrite andb_true_iff, !String.eqb_eq. intros [E H]; now subst. Qed.
Definition admitted schemas kind := existsb (schema_equal kind) schemas.
Lemma admitted_sound schemas kind : admitted schemas kind=true -> In kind schemas.
Proof. unfold admitted; rewrite existsb_exists. intros [s [In Eq]]. apply schema_equal_sound in Eq; now subst. Qed.
Record theory := {
  theory_name : string;
  unrestricted_signature : bool;
  function_symbols : list (string * nat);
  predicate_symbols : list (string * nat);
  fixed_axioms : list axiom;
  allowed_schemas : list schema;
  registered_check : string -> string -> string -> formula -> bool
}.
(* The universal countable vocabulary identifies symbols by name and arity. *)
Definition signature_ok t f := unrestricted_signature t ||
  formula_signature (function_symbols t) (predicate_symbols t) f.
Definition fixed_origin_equal a b := match a,b with
  | FixedAxiom n,FixedAxiom m | ImportedAxiom n,ImportedAxiom m => String.eqb n m
  | _,_ => false end.
Definition schema_expansion limit kind phi :=
  let variables := filter (fun i => schema_arity kind <=? i) (sort_handles (formula_parameters phi)) in
  let maximum := fold_left Nat.max variables (schema_arity kind - 1) in
  if maximum <=? limit - (match kind with Replacement => 3 | _ => 2 end) then checked_schema kind "member" variables (S maximum) phi else None.
Definition validate_axiom limit (t : theory) (a : axiom) :=
  (0 <=? axiom_id a) && formula_scoped 0 true (axiom_formula a) &&
  signature_ok t (axiom_formula a) &&
  match axiom_origin a with
  | FixedAxiom n | ImportedAxiom n =>
      String.eqb (axiom_name a) n && existsb (fun expected =>
        fixed_origin_equal (axiom_origin a) (axiom_origin expected) &&
        String.eqb n (axiom_name expected) && equivalent (axiom_formula expected) (axiom_formula a)) (fixed_axioms t)
  | SchemaInstance key phi => admitted (allowed_schemas t) key &&
      formula_scoped 0 false phi && signature_ok t phi &&
      match builtin key with
      | None => false
      | Some kind => match schema_expansion limit kind phi with
          | Some expected => equivalent expected (axiom_formula a) | None => false end
      end
  | RegisteredInstance n r data => admitted (allowed_schemas t) (RegisteredSchema n r) &&
      registered_check t n r data (axiom_formula a)
  end.

(* Explicit axiom-introduction rules for the Source refutation calculus. *)
Inductive authorized (t : theory) : formula -> Prop :=
  | AuthorizedFixed a : In a (fixed_axioms t) -> authorized t (axiom_formula a)
  | AuthorizedSchema key kind variables fresh phi result :
      In key (allowed_schemas t) -> builtin key=Some kind ->
      signature_ok t phi=true ->
      checked_schema kind "member" variables fresh phi=Some result -> authorized t result
  | AuthorizedRegistered name revision data f :
      In (RegisteredSchema name revision) (allowed_schemas t) ->
      formula_scoped 0 true f=true -> signature_ok t f=true ->
      registered_check t name revision data f=true -> authorized t f
  | AuthorizedEquivalent a b : authorized t a -> equivalent a b=true -> authorized t b.
Theorem validate_axiom_authorized limit t a : validate_axiom limit t a=true -> authorized t (axiom_formula a).
Proof.
  unfold validate_axiom. rewrite !andb_true_iff. intros [[[Id Scope] Signature] Origin].
  destruct (axiom_origin a) as [n|n|key phi|n r data].
  - apply andb_true_iff in Origin as [_ Origin]. apply existsb_exists in Origin as [expected [In E]].
    apply andb_true_iff in E as [_ Eq]. eapply (AuthorizedEquivalent t (axiom_formula expected)); [exact (AuthorizedFixed t expected In)|exact Eq].
  - apply andb_true_iff in Origin as [_ Origin]. apply existsb_exists in Origin as [expected [In E]].
    apply andb_true_iff in E as [_ Eq]. eapply (AuthorizedEquivalent t (axiom_formula expected)); [exact (AuthorizedFixed t expected In)|exact Eq].
  - apply andb_true_iff in Origin as [Origin Expanded].
    apply andb_true_iff in Origin as [Origin PhiSignature]. apply andb_true_iff in Origin as [Allowed _].
    destruct (builtin key) as [kind|] eqn:Kind; [|discriminate].
    unfold schema_expansion in Expanded. cbv zeta in Expanded.
    match type of Expanded with context [if ?b then _ else _] => destruct b end; [|discriminate].
    match type of Expanded with context [checked_schema ?k ?m ?vs ?fr ?p] =>
      destruct (checked_schema k m vs fr p) as [expected|] eqn:Expansion
    end; [|discriminate].
    eapply (AuthorizedEquivalent t expected); [|exact Expanded]. eapply (AuthorizedSchema t key kind);
      [now apply admitted_sound|exact Kind|exact PhiSignature|exact Expansion].
  - apply andb_true_iff in Origin as [Allowed Checked]. eapply (AuthorizedRegistered t n r data);
      [now apply admitted_sound|exact Scope|exact Signature|exact Checked].
Qed.

Section TheoryMeaning.
Context {U : Type}.
Variable functions : string -> list U -> U.
Variable predicates : string -> list U -> Prop.
Variable default : U.
Let holds f := source_holds functions predicates (fun _ => default) (fun _ => default) f.
Definition theory_holds (t : theory) :=
  (forall a, In a (fixed_axioms t) -> holds (axiom_formula a)) /\
  (forall key kind variables fresh phi result,
    In key (allowed_schemas t) -> builtin key=Some kind ->
    signature_ok t phi=true ->
    checked_schema kind "member" variables fresh phi=Some result ->
    parameter_meaning variables (schema_meaning functions predicates kind "member" phi (fun _ => default)) (fun _ => default)) /\
  (forall name revision data f, In (RegisteredSchema name revision) (allowed_schemas t) ->
    formula_scoped 0 true f=true -> signature_ok t f=true ->
    registered_check t name revision data f=true -> holds f).
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.
Theorem authorized_sound t f : authorized t f -> theory_holds t -> holds f.
Proof.
  intros Accepted [Fixed [Schemas Registered]]. induction Accepted.
  - now apply Fixed.
  - apply (proj2 (proj2 (checked_schema_correct functions predicates excluded_middle _ _ _ _ _ _ H2) _ _)).
    eapply Schemas; eauto.
  - eapply Registered; eauto.
  - apply (equivalent_sound functions predicates excluded_middle _ _ H). exact IHAccepted.
Qed.
Theorem validate_axiom_sound limit t a : validate_axiom limit t a=true ->
  theory_holds t -> holds (axiom_formula a).
Proof. intros Valid. apply authorized_sound. now apply (validate_axiom_authorized limit). Qed.
End TheoryMeaning.
Print Assumptions equivalent_sound.
Print Assumptions validate_axiom_sound.
