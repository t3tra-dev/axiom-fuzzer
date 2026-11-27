(* Definitions: transparent abbreviations and their expansion.

   A definition environment lists function definitions f(x0..x(n-1)) := t and predicate
   definitions p(x0..x(n-1)) := phi, whose parameters are the free variables SFree 0 to
   SFree (n-1). [expand_formula] replaces every application of a defined symbol by its body,
   instantiated simultaneously with the (already expanded) actuals; bound indices of an
   argument are lifted beneath the binders of a predicate body, so nothing is captured.

   [expand_correct] shows that in every structure satisfying the defining axioms
   (forall x, f(x) = t and forall x, p(x) <-> phi) a formula and its expansion have the same
   truth value. No acyclicity, scope or base-language condition is needed for this direction:
   it is what makes a refutation of the expanded axioms a refutation of the definitions together
   with the original axioms ([expansions_match_sound]). The runtime and the Rocq exports use the
   extracted [expand_formula] and [expansions_match]. *)
From Stdlib Require Import List Bool Arith.PeanoNat String Lia.
Require Import AxiomFuzzer.Source.Language AxiomFuzzer.Source.Validation.
Import ListNotations.

Definition function_definitions := list (string * (nat * source_term string)).
Definition predicate_definitions := list (string * (nat * source_formula string string)).

Section Syntax.

Definition argument (actuals : list (source_term string)) depth i : source_term string :=
  match nth_error actuals i with Some a => lift_term depth a | None => SFree i end.

Fixpoint instantiate_term actuals depth (t : source_term string) : source_term string :=
  match t with
  | SBound i => SBound i
  | SFree i => argument actuals depth i
  | SApply s ts => SApply s (map (instantiate_term actuals depth) ts)
  end.

Fixpoint instantiate_formula actuals depth (f : source_formula string string)
  : source_formula string string :=
  match f with
  | STop => STop | SBot => SBot
  | SPred p ts => SPred p (map (instantiate_term actuals depth) ts)
  | SEq x y => SEq (instantiate_term actuals depth x) (instantiate_term actuals depth y)
  | SNeg f => SNeg (instantiate_formula actuals depth f)
  | SConj fs => SConj (map (instantiate_formula actuals depth) fs)
  | SDisj fs => SDisj (map (instantiate_formula actuals depth) fs)
  | SAll f => SAll (instantiate_formula actuals (S depth) f)
  | SEx f => SEx (instantiate_formula actuals (S depth) f)
  end.

Definition definition_lookup {A} name (entries : list (string * A)) : option A :=
  match find (fun entry => String.eqb name (fst entry)) entries with
  | Some entry => Some (snd entry) | None => None
  end.

Fixpoint options_all {A} (xs : list (option A)) : option (list A) :=
  match xs with
  | [] => Some []
  | x :: xs => match x, options_all xs with Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.

Fixpoint expand_term (functions : function_definitions) (t : source_term string)
  : option (source_term string) :=
  match t with
  | SApply s ts =>
      match options_all (map (expand_term functions) ts) with
      | None => None
      | Some ts =>
          match definition_lookup s functions with
          | Some (n, body) => if List.length ts =? n then Some (instantiate_term ts 0 body) else None
          | None => Some (SApply s ts)
          end
      end
  | t => Some t
  end.

Fixpoint expand_formula (functions : function_definitions) (predicates : predicate_definitions)
  (f : source_formula string string) : option (source_formula string string) :=
  match f with
  | STop => Some STop | SBot => Some SBot
  | SPred p ts =>
      match options_all (map (expand_term functions) ts) with
      | None => None
      | Some ts =>
          match definition_lookup p predicates with
          | Some (n, body) => if List.length ts =? n then Some (instantiate_formula ts 0 body) else None
          | None => Some (SPred p ts)
          end
      end
  | SEq x y =>
      match expand_term functions x, expand_term functions y with
      | Some x, Some y => Some (SEq x y) | _, _ => None
      end
  | SNeg f => option_map SNeg (expand_formula functions predicates f)
  | SConj fs => option_map SConj (options_all (map (expand_formula functions predicates) fs))
  | SDisj fs => option_map SDisj (options_all (map (expand_formula functions predicates) fs))
  | SAll f => option_map SAll (expand_formula functions predicates f)
  | SEx f => option_map SEx (expand_formula functions predicates f)
  end.

Definition parameters n : list (source_term string) := map SFree (seq 0 n).

Definition function_axiom (entry : string * (nat * source_term string)) :=
  let '(name, (n, body)) := entry in
  close_parameters (seq 0 n) (SEq (SApply name (parameters n)) body : source_formula string string).

Definition predicate_axiom (entry : string * (nat * source_formula string string)) :=
  let '(name, (n, body)) := entry in
  close_parameters (seq 0 n) (equivalence (SPred name (parameters n)) body).

Definition defining_axioms functions predicates :=
  map function_axiom functions ++ map predicate_axiom predicates.

(* Each original axiom expands to a formula that the Source kernel's [equivalent] relates to the
   axiom actually used (the Source arena may flatten and reorder conjunctions). *)
Fixpoint expansions_match functions predicates originals axioms : bool :=
  match originals, axioms with
  | [], [] => true
  | o :: os, a :: xs =>
      match expand_formula functions predicates o with
      | Some e => equivalent e a && expansions_match functions predicates os xs
      | None => false
      end
  | _, _ => false
  end.

End Syntax.

Section Semantics.
Context {D : Type} (functions : string -> list D -> D) (predicates : string -> list D -> Prop).
Local Abbreviation eval := (source_eval functions).
Local Abbreviation holds := (source_holds functions predicates).

Definition arguments_env (args : list D) (free : nat -> D) i :=
  match nth_error args i with Some x => x | None => free i end.

Definition function_holds (entry : string * (nat * source_term string)) :=
  let '(name, (n, body)) := entry in
  forall args bound free, List.length args = n -> functions name args = eval bound (arguments_env args free) body.

Definition predicate_holds (entry : string * (nat * source_formula string string)) :=
  let '(name, (n, body)) := entry in
  forall args bound free, List.length args = n ->
    (predicates name args <-> holds bound (arguments_env args free) body).

Lemma eval_ext : forall t bound bound' free free',
  (forall i, bound i = bound' i) -> (forall i, free i = free' i) ->
  eval bound free t = eval bound' free' t.
Proof.
  fix IH 1. intros [i|i|s ts] bound bound' free free' B Fr; simpl; auto.
  f_equal. induction ts as [|t ts Hts]; simpl; [reflexivity|]. rewrite (IH t _ _ _ _ B Fr), Hts. reflexivity.
Qed.

Lemma holds_ext : forall f bound bound' free free',
  (forall i, bound i = bound' i) -> (forall i, free i = free' i) ->
  (holds bound free f <-> holds bound' free' f).
Proof.
  fix IH 1. intros [| |p ts|x y|f|fs|fs|f|f] bound bound' free free' B Fr; simpl.
  - tauto.
  - tauto.
  - replace (map (eval bound free) ts) with (map (eval bound' free') ts); [tauto|].
    apply map_ext. intros t. symmetry. now apply eval_ext.
  - rewrite (eval_ext x bound bound' free free' B Fr), (eval_ext y bound bound' free free' B Fr). tauto.
  - rewrite (IH f bound bound' free free' B Fr). tauto.
  - induction fs as [|f fs Hfs]; [tauto|]. rewrite (IH f bound bound' free free' B Fr), Hfs. tauto.
  - induction fs as [|f fs Hfs]; [tauto|]. rewrite (IH f bound bound' free free' B Fr), Hfs. tauto.
  - assert (P : forall x i, push x bound i = push x bound' i) by (intros x [|i]; simpl; auto).
    split; intros H x; apply (IH f (push x bound) (push x bound') free free' (P x) Fr); apply H.
  - assert (P : forall x i, push x bound i = push x bound' i) by (intros x [|i]; simpl; auto).
    split; intros [x H]; exists x; apply (IH f (push x bound) (push x bound') free free' (P x) Fr); exact H.
Qed.

(* The value environment that an instantiation induces on the body's parameters. *)
Definition instance_env actuals (outer : nat -> D) free i :=
  match nth_error actuals i with Some a => eval outer free a | None => free i end.

Lemma instantiate_term_eval : forall t actuals depth bound outer free,
  (forall j, bound (depth + j) = outer j) ->
  eval bound free (instantiate_term actuals depth t) = eval bound (instance_env actuals outer free) t.
Proof.
  fix IH 1. intros [i|i|s ts] actuals depth bound outer free Outer; simpl.
  - reflexivity.
  - unfold argument, instance_env. destruct (nth_error actuals i) as [a|]; [|reflexivity].
    rewrite term_lifting. apply eval_ext; auto.
  - f_equal. rewrite map_map. induction ts as [|t ts Hts]; simpl; [reflexivity|].
    rewrite (IH t actuals depth bound outer free Outer), Hts. reflexivity.
Qed.

Lemma instantiate_formula_holds : forall f actuals depth bound outer free,
  (forall j, bound (depth + j) = outer j) ->
  (holds bound free (instantiate_formula actuals depth f) <-> holds bound (instance_env actuals outer free) f).
Proof.
  fix IH 1. intros [| |p ts|x y|f|fs|fs|f|f] actuals depth bound outer free Outer; simpl.
  - tauto.
  - tauto.
  - rewrite map_map. replace (map (fun t => eval bound free (instantiate_term actuals depth t)) ts)
      with (map (eval bound (instance_env actuals outer free)) ts); [tauto|].
    apply map_ext. intros t. symmetry. now apply instantiate_term_eval.
  - rewrite !(instantiate_term_eval _ actuals depth bound outer free Outer). tauto.
  - rewrite (IH f actuals depth bound outer free Outer). tauto.
  - induction fs as [|f fs Hfs]; simpl; [tauto|].
    rewrite (IH f actuals depth bound outer free Outer), Hfs. tauto.
  - induction fs as [|f fs Hfs]; simpl; [tauto|].
    rewrite (IH f actuals depth bound outer free Outer), Hfs. tauto.
  - assert (O : forall x j, push x bound (S depth + j) = outer j) by (intros; simpl; apply Outer).
    split; intros H x; apply (IH f actuals (S depth) (push x bound) outer free (O x)); apply H.
  - assert (O : forall x j, push x bound (S depth + j) = outer j) by (intros; simpl; apply Outer).
    split; intros [x H]; exists x; apply (IH f actuals (S depth) (push x bound) outer free (O x)); exact H.
Qed.

Lemma instance_env_arguments actuals bound free i :
  instance_env actuals bound free i = arguments_env (map (eval bound free) actuals) free i.
Proof. unfold instance_env, arguments_env. rewrite nth_error_map. now destruct (nth_error actuals i). Qed.

Lemma definition_lookup_in {A} name (entries : list (string * A)) value :
  definition_lookup name entries = Some value -> In (name, value) entries.
Proof.
  unfold definition_lookup. destruct (find _ entries) as [[key v]|] eqn:E; [|discriminate].
  intros H. inversion H; subst. apply find_some in E as [In Key]. simpl in Key.
  apply String.eqb_eq in Key. now subst.
Qed.

Section Expansion.
Variables (fs : function_definitions) (ps : predicate_definitions).
Hypothesis functions_defined : Forall function_holds fs.
Hypothesis predicates_defined : Forall predicate_holds ps.

Lemma expand_terms_eval ts us bound free
  (IH : forall t u, In t ts -> expand_term fs t = Some u -> eval bound free t = eval bound free u) :
  options_all (map (expand_term fs) ts) = Some us -> map (eval bound free) ts = map (eval bound free) us.
Proof.
  revert us. induction ts as [|t ts Hts]; intros us H; simpl in H.
  - inversion H; reflexivity.
  - destruct (expand_term fs t) as [u|] eqn:Et; [|discriminate].
    destruct (options_all (map (expand_term fs) ts)) as [vs|]; [|discriminate].
    inversion H; subst. simpl. rewrite (IH t u (or_introl eq_refl) Et).
    rewrite (Hts (fun t' u' I => IH t' u' (or_intror I)) vs eq_refl). reflexivity.
Qed.

Lemma options_all_length {A B} (g : A -> option B) xs ys :
  options_all (map g xs) = Some ys -> List.length ys = List.length xs.
Proof.
  revert ys. induction xs as [|x xs IH]; intros ys H; simpl in H; [now inversion H|].
  destruct (g x); [|discriminate]. destruct (options_all (map g xs)) eqn:E; [|discriminate].
  inversion H; subst. simpl. now rewrite (IH l eq_refl).
Qed.

Theorem expand_term_correct : forall t u bound free,
  expand_term fs t = Some u -> eval bound free t = eval bound free u.
Proof.
  fix IH 1. intros [i|i|s ts] u bound free H; simpl in H; try (inversion H; reflexivity).
  destruct (options_all (map (expand_term fs) ts)) as [us|] eqn:Us; [|discriminate].
  assert (Args : map (eval bound free) ts = map (eval bound free) us).
  { clear H. revert us Us. induction ts as [|t ts Hts]; intros us Us; simpl in Us.
    - inversion Us; reflexivity.
    - destruct (expand_term fs t) as [u'|] eqn:Et; [|discriminate].
      destruct (options_all (map (expand_term fs) ts)) as [vs|]; [|discriminate].
      inversion Us; subst. simpl. rewrite (IH t u' bound free Et), (Hts vs eq_refl). reflexivity. }
  simpl. rewrite Args. destruct (definition_lookup s fs) as [[n body]|] eqn:L.
  - destruct (List.length us =? n) eqn:Len; [|discriminate]. inversion H; subst.
    apply Nat.eqb_eq in Len. apply definition_lookup_in in L.
    rewrite Forall_forall in functions_defined. specialize (functions_defined _ L). simpl in functions_defined.
    rewrite (instantiate_term_eval body us 0 bound bound free (fun j => eq_refl)).
    rewrite (functions_defined (map (eval bound free) us) bound free); [|now rewrite length_map].
    apply eval_ext; [reflexivity|]. intros i. symmetry. apply instance_env_arguments.
  - inversion H; subst. reflexivity.
Qed.

Lemma expand_terms_correct ts us bound free :
  options_all (map (expand_term fs) ts) = Some us -> map (eval bound free) ts = map (eval bound free) us.
Proof. apply expand_terms_eval. intros t u _. apply expand_term_correct. Qed.

Theorem expand_correct : forall f g bound free,
  expand_formula fs ps f = Some g -> (holds bound free f <-> holds bound free g).
Proof.
  fix IH 1. intros [| |p ts|x y|f|fs'|fs'|f|f] g bound free H; simpl in H.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
  - destruct (options_all (map (expand_term fs) ts)) as [us|] eqn:Us; [|discriminate].
    simpl. rewrite (expand_terms_correct ts us bound free Us). destruct (definition_lookup p ps) as [[n body]|] eqn:L.
    + destruct (List.length us =? n) eqn:Len; [|discriminate]. inversion H; subst.
      apply Nat.eqb_eq in Len. apply definition_lookup_in in L.
      rewrite Forall_forall in predicates_defined. specialize (predicates_defined _ L). simpl in predicates_defined.
      rewrite (instantiate_formula_holds body us 0 bound bound free (fun j => eq_refl)).
      rewrite (predicates_defined (map (eval bound free) us) bound free); [|now rewrite length_map].
      apply holds_ext; [reflexivity|]. intros i. symmetry. apply instance_env_arguments.
    + inversion H; subst. reflexivity.
  - destruct (expand_term fs x) as [x'|] eqn:X; [|discriminate].
    destruct (expand_term fs y) as [y'|] eqn:Y; [|discriminate]. inversion H; subst. simpl.
    rewrite (expand_term_correct x x' bound free X), (expand_term_correct y y' bound free Y). reflexivity.
  - destruct (expand_formula fs ps f) as [f'|] eqn:E; [|discriminate]. inversion H; subst. simpl.
    rewrite (IH f f' bound free E). reflexivity.
  - destruct (options_all (map (expand_formula fs ps) fs')) as [gs|] eqn:Gs; [|discriminate].
    inversion H; subst. clear H. simpl. revert gs Gs. induction fs' as [|f fs' Hfs]; intros gs Gs; simpl in Gs.
    + inversion Gs; subst. reflexivity.
    + destruct (expand_formula fs ps f) as [f'|] eqn:E; [|discriminate].
      destruct (options_all (map (expand_formula fs ps) fs')) as [hs|]; [|discriminate].
      inversion Gs; subst. simpl. rewrite (IH f f' bound free E), (Hfs hs eq_refl). reflexivity.
  - destruct (options_all (map (expand_formula fs ps) fs')) as [gs|] eqn:Gs; [|discriminate].
    inversion H; subst. clear H. simpl. revert gs Gs. induction fs' as [|f fs' Hfs]; intros gs Gs; simpl in Gs.
    + inversion Gs; subst. reflexivity.
    + destruct (expand_formula fs ps f) as [f'|] eqn:E; [|discriminate].
      destruct (options_all (map (expand_formula fs ps) fs')) as [hs|]; [|discriminate].
      inversion Gs; subst. simpl. rewrite (IH f f' bound free E), (Hfs hs eq_refl). reflexivity.
  - destruct (expand_formula fs ps f) as [f'|] eqn:E; [|discriminate]. inversion H; subst. simpl.
    split; intros A x; apply (IH f f' (push x bound) free E); apply A.
  - destruct (expand_formula fs ps f) as [f'|] eqn:E; [|discriminate]. inversion H; subst. simpl.
    split; intros [x A]; exists x; apply (IH f f' (push x bound) free E); exact A.
Qed.

End Expansion.

(* The defining axioms, true under every assignment, give the semantic definitions. *)
Fixpoint fill start (args : list D) (free : nat -> D) : nat -> D :=
  match args with [] => free | a :: args => fill (S start) args (update free start a) end.

Lemma fill_spec : forall args start free i,
  fill start args free i = if i <? start then free i else
    match nth_error args (i - start) with Some x => x | None => free i end.
Proof.
  induction args as [|a args IH]; intros start free i; simpl.
  - destruct (i <? start); [reflexivity|]. now destruct (i - start).
  - rewrite IH. unfold update.
    destruct (i <? S start) eqn:A; destruct (i <? start) eqn:B; destruct (i =? start) eqn:C;
      rewrite ?Nat.ltb_lt, ?Nat.ltb_ge, ?Nat.eqb_eq, ?Nat.eqb_neq in *; try lia; try reflexivity.
    + subst. now rewrite Nat.sub_diag.
    + replace (i - start) with (S (i - S start)) by lia. reflexivity.
Qed.

Lemma fill_arguments args free i : fill 0 args free i = arguments_env args free i.
Proof. rewrite fill_spec. unfold arguments_env. simpl. now rewrite Nat.sub_0_r. Qed.

Lemma parameter_meaning_fill : forall args start (M : (nat -> D) -> Prop) free,
  parameter_meaning (seq start (List.length args)) M free -> M (fill start args free).
Proof.
  induction args as [|a args IH]; intros start M free H; simpl in *; [exact H|].
  apply IH. apply H.
Qed.

Lemma map_arguments_env : forall args free,
  map (arguments_env args free) (seq 0 (List.length args)) = args.
Proof.
  induction args as [|a args IH]; intros free; [reflexivity|]. simpl. f_equal.
  rewrite <- seq_shift, map_map. exact (IH (fun i => free (S i))).
Qed.

Lemma eval_parameters args bound free :
  map (eval bound (arguments_env args free)) (parameters (List.length args)) = args.
Proof. unfold parameters. rewrite map_map. simpl. apply map_arguments_env. Qed.

Lemma fill_parameters args bound free :
  map (eval bound (fill 0 args free)) (parameters (List.length args)) = args.
Proof.
  transitivity (map (eval bound (arguments_env args free)) (parameters (List.length args))).
  - apply map_ext. intros t. apply eval_ext; [reflexivity|apply fill_arguments].
  - apply eval_parameters.
Qed.

Lemma function_axiom_holds entry :
  (forall bound free, holds bound free (function_axiom entry)) -> function_holds entry.
Proof.
  destruct entry as [name [n body]]. simpl. intros A args bound free Len. subst n.
  specialize (A bound free). rewrite close_parameters_holds in A.
  apply parameter_meaning_fill in A. simpl in A.
  rewrite fill_parameters in A. rewrite A. apply eval_ext; [reflexivity|apply fill_arguments].
Qed.

Lemma predicate_axiom_holds entry :
  (forall bound free, holds bound free (predicate_axiom entry)) -> predicate_holds entry.
Proof.
  destruct entry as [name [n body]]. simpl. intros A args bound free Len. subst n.
  specialize (A bound free). rewrite close_parameters_holds in A.
  apply parameter_meaning_fill in A.
  change ((holds bound (fill 0 args free) (implication (SPred name (parameters (List.length args))) body) /\
           (holds bound (fill 0 args free) (implication body (SPred name (parameters (List.length args)))) /\ True))) in A.
  unfold implication in A. simpl in A.
  rewrite (holds_ext body bound bound (fill 0 args free) (arguments_env args free)) in A
    by (reflexivity || apply fill_arguments).
  rewrite fill_parameters in A.
  destruct A as [[N1|B1] [[N2|B2] _]]; tauto.
Qed.

Definition satisfies (f : source_formula string string) := forall bound free, holds bound free f.

Theorem defining_axioms_hold fs ps :
  Forall satisfies (defining_axioms fs ps) -> Forall function_holds fs /\ Forall predicate_holds ps.
Proof.
  unfold defining_axioms. rewrite Forall_app, !Forall_map. intros [F P]. split.
  - eapply Forall_impl; [|exact F]. intros e. apply function_axiom_holds.
  - eapply Forall_impl; [|exact P]. intros e. apply predicate_axiom_holds.
Qed.

Hypothesis excluded_middle : forall Q : Prop, Q \/ ~ Q.

(* A refutation of the axioms that the original axioms expand to is a refutation of the
   definitions together with the original axioms, over the same domain and interpretation. *)
Theorem expansions_match_sound fs ps originals axioms bound free :
  expansions_match fs ps originals axioms = true ->
  ~ Forall (holds bound free) axioms ->
  ~ (Forall satisfies (defining_axioms fs ps) /\ Forall satisfies originals).
Proof.
  intros M Refuted [Defined Originals]. apply defining_axioms_hold in Defined as [DF DP].
  apply Refuted. clear Refuted. revert axioms M. induction Originals as [|o os O _ IH]; intros [|a xs] M;
    simpl in M; try discriminate; [constructor|].
  destruct (expand_formula fs ps o) as [e|] eqn:E; [|discriminate].
  apply andb_true_iff in M as [Eq M]. constructor; [|now apply IH].
  apply (equivalent_sound functions predicates excluded_middle e a Eq).
  apply (expand_correct fs ps DF DP o e bound free E). apply O.
Qed.

End Semantics.

Print Assumptions expand_correct.
Print Assumptions expansions_match_sound.
