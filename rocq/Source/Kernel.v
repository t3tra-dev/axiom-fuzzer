(* End-to-end acceptance: authority, Source preprocessing, encoding, refutation.
   All intermediate results are computed or checked, not theorem premises. *)
From Stdlib Require Import List Bool Arith.PeanoNat String Lia.
Require Import AxiomFuzzer.Source.Language AxiomFuzzer.Source.Validation.
Require Import AxiomFuzzer.Preprocess.NormalForms AxiomFuzzer.Preprocess.Quantifiers.
Require Import AxiomFuzzer.Wire.Syntax AxiomFuzzer.Wire.Preprocess AxiomFuzzer.Wire.Refutation.
Require Import AxiomFuzzer.Source.Refutation AxiomFuzzer.Clause.Kernel.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Fixpoint wire_term_equal (a b : wire_term string) := match a,b with
  | V x,V y => variable_equal x y
  | Fn f xs,Fn g ys => symbol_equal String.eqb f g && forallb2 wire_term_equal xs ys
  | _,_ => false end.
Lemma wire_term_equal_sound : forall a b, wire_term_equal a b=true -> a=b.
Proof.
  fix IH 1. intros a b. destruct a,b; simpl; try discriminate.
  - intros E. apply variable_equal_spec in E; now subst.
  - rewrite andb_true_iff. intros [E Args].
    apply (symbol_equal_sound String.eqb (fun x y => proj1 (String.eqb_eq x y))) in E; subst.
    f_equal. revert l0 Args. induction l as [|x xs Hxs]; intros [|y ys]; simpl; try discriminate; auto.
    rewrite andb_true_iff. intros [Head Tail]. f_equal; [now apply IH|now apply Hxs].
Qed.
Lemma wire_terms_equal_sound xs ys : forallb2 wire_term_equal xs ys=true -> xs=ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl; try discriminate; auto.
  rewrite andb_true_iff. intros [H T]. f_equal; [now apply wire_term_equal_sound|now apply IH].
Qed.
Definition wire_atom_equal (a b : wire_atom string string) := match a,b with
  | P p xs,P q ys => String.eqb p q && forallb2 wire_term_equal xs ys
  | E x y,E u v => wire_term_equal x u && wire_term_equal y v
  | D x xs,D y ys => variable_equal x y && forallb2 wire_term_equal xs ys
  | _,_ => false end.
Lemma wire_atom_equal_sound a b : wire_atom_equal a b=true -> a=b.
Proof.
  destruct a,b; simpl; try discriminate; rewrite andb_true_iff; intros [H T].
  - apply String.eqb_eq in H. apply wire_terms_equal_sound in T; now subst.
  - apply wire_term_equal_sound in H,T; now subst.
  - apply variable_equal_spec in H. apply wire_terms_equal_sound in T; now subst.
Qed.
Definition wire_literal_equal (a b : wire_literal string string) :=
  Bool.eqb (positive a) (positive b) && wire_atom_equal (AxiomFuzzer.Wire.Syntax.atom a) (AxiomFuzzer.Wire.Syntax.atom b).
Lemma wire_literal_equal_sound a b : wire_literal_equal a b=true -> a=b.
Proof.
  destruct a,b. unfold wire_literal_equal; simpl. rewrite andb_true_iff.
  intros [H T]. apply Bool.eqb_prop in H. apply wire_atom_equal_sound in T; now subst.
Qed.

Inductive cnf_evidence := DistributiveEvidence
  | DefinitionalEvidence (declarations : list (definition (wire_atom string string)))
      (root : definition_literal (wire_atom string string)).
Record prepared_axiom := { original_axiom : axiom; cnf_hint : cnf_evidence }.
Record certificate := {
  certificate_theory : string;
  certificate_axioms : list prepared_axiom;
  numeric_inputs : list AxiomFuzzer.Clause.Kernel.clause;
  numeric_proof : AxiomFuzzer.Clause.Kernel.certificate
}.

Definition compile_input visit limit budget (a : prepared_axiom) : option (source_input string string) :=
  let source := axiom_formula (original_axiom a) in
  let id := axiom_id (original_axiom a) in
  if (0 <=? id) && formula_scoped 0 true source then
    match wire_quantifiers visit limit id (nnf true source) with
    | None => None
    | Some r => match wire_checked_universals visit limit (supplied_value r) with
        | None => None
        | Some m =>
          let clauses := match cnf_hint a with
            | DistributiveEvidence => wire_distributive_cnf visit budget m
            | DefinitionalEvidence ds root => wire_definitional_cnf (AxiomFuzzer.Clause.Kernel.cached ds) visit wire_atom_equal
                (List.length ds) budget id m root
            end in
          match clauses with
          | None => None
          | Some cs => Some {| source_id := id; source_text := source; source_matrix := m; source_clauses := cs |}
          end
        end
    end
  else None.
Lemma compile_input_checked visit limit budget a input : compile_input visit limit budget a=Some input ->
  input_checked input /\ source_id input=axiom_id (original_axiom a) /\ source_text input=axiom_formula (original_axiom a).
Proof.
  unfold compile_input. destruct (_ && _) eqn:Valid; [|discriminate].
  destruct (wire_quantifiers _ _ _ _) as [r|] eqn:Run; [|discriminate].
  destruct (wire_checked_universals _ _ _) as [m|] eqn:Scope; [|discriminate].
  destruct (cnf_hint a) as [|ds root].
  - destruct (wire_distributive_cnf _ _ _) as [cs|] eqn:CNF; [|discriminate].
    intros H; inversion H; subst. split; [|auto]. split.
    + exists visit,visit,limit,r. auto.
    + left. exists visit,budget; exact CNF.
  - destruct (wire_definitional_cnf _ _ _ _ _ _ _ _) as [cs|] eqn:CNF; [|discriminate].
    intros H; inversion H; subst. split; [|auto]. split.
    + exists visit,visit,limit,r. auto.
    + right. exists (AxiomFuzzer.Clause.Kernel.cached ds),visit,wire_atom_equal,(List.length ds),budget,root.
      split; [exact wire_atom_equal_sound|exact CNF].
Qed.
Fixpoint compile_inputs visit limit budget axioms := match axioms with
  | [] => Some []
  | a::axioms => match compile_input visit limit budget a,compile_inputs visit limit budget axioms with
      | Some input,Some inputs => Some (input::inputs) | _,_ => None end
  end.
Lemma compile_inputs_checked visit limit budget axioms inputs :
  compile_inputs visit limit budget axioms=Some inputs -> Forall input_checked inputs /\
  map source_id inputs=map (fun a => axiom_id (original_axiom a)) axioms /\
  map source_text inputs=map (fun a => axiom_formula (original_axiom a)) axioms.
Proof.
  revert inputs. induction axioms as [|a axioms IH]; intros inputs; simpl.
  - intros H; inversion H; auto.
  - destruct (compile_input _ _ _ _) as [input|] eqn:Head; [|discriminate].
    destruct (compile_inputs _ _ _ _) as [rest|] eqn:Tail; [|discriminate].
    intros H; inversion H; subst. apply compile_input_checked in Head as [Check [Id Text]].
    destruct (IH rest eq_refl) as [Checks [Ids Texts]]. split; [now constructor|]. simpl. split.
    + now rewrite Id, Ids.
    + now rewrite Text, Texts.
Qed.
Fixpoint unique_ids ids := match ids with
  | [] => true | i::ids => negb (existsb (Nat.eqb i) ids) && unique_ids ids end.
Lemma unique_ids_sound ids : unique_ids ids=true -> NoDup ids.
Proof.
  induction ids as [|i ids IH]; simpl; [constructor|]. rewrite andb_true_iff, negb_true_iff.
  intros [Fresh Rest]. constructor; [|now apply IH]. intros In.
  assert (existsb (Nat.eqb i) ids=true) by (apply existsb_exists; exists i; split; [exact In|apply Nat.eqb_refl]). congruence.
Qed.
(* An AVL set of the identifiers seen so far replaces the scan of the rest of the list. *)
Fixpoint unique_from (seen : ClauseMap.t unit) ids := match ids with
  | [] => true
  | i::ids => if ClauseMap.mem i seen then false else unique_from (ClauseMap.add i tt seen) ids
  end.
Definition fast_unique_ids ids := unique_from (ClauseMap.empty unit) ids.
Lemma forallb_andb {A} (f g : A -> bool) xs : forallb (fun x => f x && g x) xs=forallb f xs && forallb g xs.
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity|]. rewrite IH.
  destruct (f x),(g x),(forallb f xs),(forallb g xs); reflexivity.
Qed.
Lemma negb_existsb_forallb {A} (f : A -> bool) xs : negb (existsb f xs)=forallb (fun x => negb (f x)) xs.
Proof. induction xs as [|x xs IH]; simpl; [reflexivity|]. now rewrite negb_orb, IH. Qed.
Lemma forallb_fresh_add i seen ids :
  forallb (fun j => negb (ClauseMap.mem j (ClauseMap.add i tt seen))) ids=
  forallb (fun j => negb (Nat.eqb i j)) ids && forallb (fun j => negb (ClauseMap.mem j seen)) ids.
Proof.
  rewrite <- forallb_andb. induction ids as [|j ids IH]; simpl; [reflexivity|].
  rewrite ClauseFacts.add_b, negb_orb, IH.
  replace (ClauseFacts.eqb i j) with (Nat.eqb i j); [reflexivity|].
  unfold ClauseFacts.eqb. destruct (ClauseFacts.eq_dec i j) as [Same|Different].
  - rewrite Same. apply Nat.eqb_refl.
  - now apply Nat.eqb_neq.
Qed.
Lemma unique_from_correct ids : forall seen,
  unique_from seen ids=unique_ids ids && forallb (fun i => negb (ClauseMap.mem i seen)) ids.
Proof.
  induction ids as [|i ids IH]; intros seen; simpl; [reflexivity|].
  destruct (ClauseMap.mem i seen); simpl.
  - now rewrite !andb_false_r.
  - rewrite IH, forallb_fresh_add, negb_existsb_forallb.
    destruct (forallb (fun j => negb (i =? j)) ids),(unique_ids ids),
      (forallb (fun j => negb (ClauseMap.mem j seen)) ids); reflexivity.
Qed.
Lemma fast_unique_ids_correct ids : fast_unique_ids ids=unique_ids ids.
Proof.
  unfold fast_unique_ids. rewrite unique_from_correct.
  replace (forallb (fun i => negb (ClauseMap.mem i (ClauseMap.empty unit))) ids) with true;
    [apply andb_true_r|].
  symmetry. apply forallb_forall. intros i _. now rewrite ClauseFacts.empty_a.
Qed.

(* Syntactic derivations in the primitive clause calculus. *)
Inductive primitive_derivation (inputs : list AxiomFuzzer.Clause.Kernel.clause) :
    list AxiomFuzzer.Clause.Kernel.clause -> Prop :=
  | DerivationEmpty : primitive_derivation inputs []
  | DerivationStep db rule expected conclusion : primitive_derivation inputs db ->
      infer inputs db rule=Some expected -> included expected conclusion=true ->
      primitive_derivation inputs (db ++ [conclusion]).
Definition primitive_refutation inputs := exists db, primitive_derivation inputs db /\ In [] db.
Lemma replay_derivation inputs steps db result : replay inputs db steps=Some result ->
  primitive_derivation inputs db -> primitive_derivation inputs result.
Proof.
  revert db result. induction steps as [|[rule conclusion] steps IH]; intros db result; simpl.
  - intros H D; inversion H; subst; exact D.
  - destruct (infer inputs db rule) as [expected|] eqn:Step; [|discriminate].
    destruct (included expected conclusion) eqn:Included; [|discriminate].
    intros Run D. eapply IH; [exact Run|]. eapply DerivationStep; eauto.
Qed.
Lemma check_primitive_derivation inputs proof : AxiomFuzzer.Clause.Kernel.check inputs proof=true -> primitive_refutation inputs.
Proof.
  rewrite AxiomFuzzer.Clause.Kernel.check_correct. unfold check_list. destruct (replay inputs [] proof) as [db|] eqn:Run; [|discriminate].
  intros Empty. exists db; split; [eapply replay_derivation; [exact Run|constructor]|].
  apply existsb_exists in Empty as [c [In Empty]]. destruct c; [exact In|discriminate].
Qed.
Lemma replay_append inputs steps : forall db middle suffix,
  replay inputs db steps=Some middle -> replay inputs db (steps ++ suffix)=replay inputs middle suffix.
Proof.
  induction steps as [|[rule conclusion] steps IH]; intros db middle suffix; simpl.
  - intros H; inversion H; subst; reflexivity.
  - destruct (infer inputs db rule); [|discriminate]. destruct (included _ _); [|discriminate]. now apply IH.
Qed.
Lemma derivation_replay inputs db : primitive_derivation inputs db ->
  exists proof, replay inputs [] proof=Some db.
Proof.
  intros D. induction D.
  - exists []; reflexivity.
  - destruct IHD as [proof Run]. exists (proof ++ [(rule,conclusion)]).
    rewrite (replay_append inputs proof [] db _ Run). simpl. now rewrite H,H0.
Qed.
Lemma primitive_refutation_checked inputs : primitive_refutation inputs ->
  exists proof, AxiomFuzzer.Clause.Kernel.check inputs proof=true.
Proof.
  intros [db [D Empty]]. destruct (derivation_replay inputs db D) as [proof Run]. exists proof.
  rewrite AxiomFuzzer.Clause.Kernel.check_correct. unfold check_list. rewrite Run. apply existsb_exists; exists []; auto.
Qed.

Module Kernel (Order : WireOrder with Definition function_name := string with Definition predicate_name := string).
Module Sound := SourceRefutation Order.
Module Normalize := Sound.Normalize.
Fixpoint normalize_inputs limit cs := match cs with
  | [] => Some []
  | c::cs => match Normalize.normalize limit c,normalize_inputs limit cs with
      | Some result,Some results => Some (result::results) | _,_ => None end
  end.
Lemma normalize_inputs_checked limit cs normalized : normalize_inputs limit cs=Some normalized ->
  Forall2 (fun c result => Normalize.normalize limit c=Some result) cs normalized.
Proof.
  revert normalized. induction cs as [|c cs IH]; intros normalized; simpl.
  - intros H; inversion H; constructor.
  - destruct (Normalize.normalize _ _) as [result|] eqn:Head; [|discriminate].
    destruct (normalize_inputs _ _) as [results|] eqn:Tail; [|discriminate].
    intros H; inversion H; subst. constructor; [exact Head|now apply IH].
Qed.

Section Acceptance.
Variable visit : unit -> bool.
Variable limit budget : nat.
Variable encode_variable : (nat * nat) -> nat.
Variable decode_function : nat -> option (wire_symbol string).
Variable decode_predicate : nat -> option (wire_predicate string).
Definition check_sources (c : certificate) :=
  match compile_inputs visit limit budget (certificate_axioms c) with
  | None => false
  | Some inputs => fast_unique_ids (map source_id inputs) &&
      match normalize_inputs limit (flat_map source_clauses inputs) with
      | None => false
      | Some normalized => encoded_inputs String.eqb String.eqb encode_variable decode_function decode_predicate
          normalized (numeric_inputs c) && AxiomFuzzer.Clause.Kernel.check (numeric_inputs c) (numeric_proof c)
      end
  end.
Definition check (t : theory) (c : certificate) :=
  String.eqb (theory_name t) (certificate_theory c) &&
  forallb (fun a => validate_axiom limit t (original_axiom a)) (certificate_axioms c) && check_sources c.

(* The AVATAR certificate replaces only the final refutation check. Source
   authority, fresh axiom identifiers, preprocessing, and numeric encoding are
   checked exactly as on the primitive acceptance path. Components are not
   additional Source axioms. The legacy numeric_proof field is unused here. *)
Definition avatar_check_sources (c : certificate) (proof : AxiomFuzzer.Clause.Avatar.certificate) :=
  match compile_inputs visit limit budget (certificate_axioms c) with
  | None => false
  | Some inputs => fast_unique_ids (map source_id inputs) &&
      match normalize_inputs limit (flat_map source_clauses inputs) with
      | None => false
      | Some normalized => encoded_inputs String.eqb String.eqb encode_variable decode_function decode_predicate
          normalized (numeric_inputs c) && AxiomFuzzer.Clause.Avatar.check (numeric_inputs c) proof
      end
  end.
Definition avatar_check (t : theory) (c : certificate) (proof : AxiomFuzzer.Clause.Avatar.certificate) :=
  String.eqb (theory_name t) (certificate_theory c) &&
  forallb (fun a => validate_axiom limit t (original_axiom a)) (certificate_axioms c) && avatar_check_sources c proof.

(* T |- False in the Source refutation calculus: permitted axioms, checked
   clausification with fresh namespaces, normalization/encoding, and a finite
   primitive derivation of the empty clause. No acceptance result is a premise. *)
Inductive derives_false (t : theory) : Prop :=
  | SourceRefutation inputs normalized numeric :
      Forall (fun input => authorized t (source_text input)) inputs ->
      NoDup (map source_id inputs) -> Forall input_checked inputs ->
      Forall2 (fun c result => Normalize.normalize limit c=Some result)
        (flat_map source_clauses inputs) normalized ->
      encoded_inputs String.eqb String.eqb encode_variable decode_function decode_predicate normalized numeric=true ->
      primitive_refutation numeric -> derives_false t.
Theorem check_derives_false t c : check t c=true -> derives_false t.
Proof.
  unfold check,check_sources. rewrite !andb_true_iff. intros [[Name Axioms] Sources].
  destruct (compile_inputs _ _ _ _) as [inputs|] eqn:Inputs; [|discriminate].
  apply andb_true_iff in Sources as [Unique Rest]. rewrite fast_unique_ids_correct in Unique.
  destruct (normalize_inputs _ _) as [normalized|] eqn:Normalized; [|discriminate].
  apply andb_true_iff in Rest as [Encoded Checked].
  destruct (compile_inputs_checked _ _ _ _ _ Inputs) as [InputChecks [Ids Texts]].
  eapply SourceRefutation with inputs normalized (numeric_inputs c).
  - change (Forall (fun input => authorized t (source_text input)) inputs).
    rewrite <- (Forall_map source_text (authorized t)), Texts, Forall_map, Forall_forall. intros a In.
    apply (validate_axiom_authorized limit). rewrite List.forallb_forall in Axioms. now apply Axioms.
  - now apply unique_ids_sound.
  - exact InputChecks.
  - now apply normalize_inputs_checked.
  - exact Encoded.
  - exact (check_primitive_derivation _ _ Checked).
Qed.

Section Soundness.
Context {U : Type}.
Variable functions : string -> list U -> U.
Variable predicates : string -> list U -> Prop.
Variable default : U.
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.
Hypothesis functional_choice : forall R : list U -> U -> Prop,
  (forall args, exists x, R args x) -> exists g, forall args, R args (g args).
Let holds := source_holds functions predicates (fun _ => default) (fun _ => default).
Theorem derives_false_sound t : derives_false t -> ~ theory_holds functions predicates default t.
Proof.
  intros [inputs normalized numeric Allowed Unique Inputs Normalized Encoded Refuted] Theory.
  destruct (primitive_refutation_checked numeric Refuted) as [proof Checked].
  apply (Sound.source_inputs_check_sound default functions predicates excluded_middle functional_choice
    String.eqb String.eqb (fun x y => proj1 (String.eqb_eq x y)) (fun x y => proj1 (String.eqb_eq x y))
    encode_variable decode_function decode_predicate inputs limit normalized numeric proof
    Unique Inputs Normalized Encoded Checked).
  eapply Forall_impl; [|exact Allowed]. intros input AllowedInput. exact (authorized_sound functions predicates default excluded_middle t _ AllowedInput Theory).
Qed.
Theorem check_sources_sound c : check_sources c=true ->
  ~ Forall (fun a => holds (axiom_formula (original_axiom a))) (certificate_axioms c).
Proof.
  unfold check_sources. destruct (compile_inputs _ _ _ _) as [inputs|] eqn:Inputs; [|discriminate].
  rewrite andb_true_iff. intros [Unique Rest]. rewrite fast_unique_ids_correct in Unique.
  destruct (normalize_inputs _ _) as [normalized|] eqn:Normalized; [|discriminate].
  apply andb_true_iff in Rest as [Encoded Checked]. intros Sources.
  destruct (compile_inputs_checked _ _ _ _ _ Inputs) as [InputChecks [Ids Texts]].
  assert (Model : Forall (source_input_holds functions predicates default) inputs).
  { unfold source_input_holds. change (Forall (fun input => holds (source_text input)) inputs).
    rewrite <- Forall_map, Texts, Forall_map. exact Sources. }
  exact (Sound.source_inputs_check_sound default functions predicates excluded_middle functional_choice
    String.eqb String.eqb (fun x y => proj1 (String.eqb_eq x y)) (fun x y => proj1 (String.eqb_eq x y))
    encode_variable decode_function decode_predicate inputs limit normalized (numeric_inputs c) (numeric_proof c)
    (unique_ids_sound _ Unique) InputChecks (normalize_inputs_checked _ _ _ Normalized) Encoded Checked Model).
Qed.
Theorem check_sound t c : check t c=true -> ~ theory_holds functions predicates default t.
Proof.
  intros Checked. apply derives_false_sound. now apply (check_derives_false t c).
Qed.
Theorem avatar_check_sources_sound c proof : avatar_check_sources c proof=true ->
  ~ Forall (fun a => holds (axiom_formula (original_axiom a))) (certificate_axioms c).
Proof.
  unfold avatar_check_sources. destruct (compile_inputs _ _ _ _) as [inputs|] eqn:Inputs; [|discriminate].
  rewrite andb_true_iff. intros [Unique Rest]. rewrite fast_unique_ids_correct in Unique.
  destruct (normalize_inputs _ _) as [normalized|] eqn:Normalized; [|discriminate].
  apply andb_true_iff in Rest as [Encoded Checked]. intros Sources.
  destruct (compile_inputs_checked _ _ _ _ _ Inputs) as [InputChecks [Ids Texts]].
  assert (Model : Forall (source_input_holds functions predicates default) inputs).
  { unfold source_input_holds. change (Forall (fun input => holds (source_text input)) inputs).
    rewrite <- Forall_map, Texts, Forall_map. exact Sources. }
  exact (Sound.source_inputs_avatar_check_sound default functions predicates excluded_middle functional_choice
    String.eqb String.eqb (fun x y => proj1 (String.eqb_eq x y)) (fun x y => proj1 (String.eqb_eq x y))
    encode_variable decode_function decode_predicate inputs limit normalized (numeric_inputs c) proof
    (unique_ids_sound _ Unique) InputChecks (normalize_inputs_checked _ _ _ Normalized) Encoded Checked Model).
Qed.
Theorem avatar_check_sound t c proof : avatar_check t c proof=true -> ~ theory_holds functions predicates default t.
Proof.
  unfold avatar_check. rewrite !andb_true_iff. intros [[Name Axioms] Checked] Theory.
  apply (avatar_check_sources_sound c proof Checked).
  apply Forall_forall. intros a In.
  eapply (validate_axiom_sound functions predicates default excluded_middle limit t (original_axiom a)); [|exact Theory].
  rewrite List.forallb_forall in Axioms. now apply Axioms.
Qed.
End Soundness.
End Acceptance.
Print Assumptions check_sources_sound.
Print Assumptions check_derives_false.
Print Assumptions check_sound.
Print Assumptions avatar_check_sources_sound.
Print Assumptions avatar_check_sound.
End Kernel.

(* Exported proofs carry a finite literal ranking. Its totality and equality
   laws are proved here; a generated file never assumes OCaml's comparison. *)
Module Type LiteralRanking.
  Parameter literals : list (wire_literal string string).
End LiteralRanking.
Module RankedOrder (Ranking : LiteralRanking) <: WireOrder.
Definition function_name := string.
Definition predicate_name := string.
Fixpoint rank l xs := match xs with
  | [] => 0 | x::xs => if wire_literal_equal l x then 0 else S (rank l xs) end.
Definition leb a b := rank a Ranking.literals <=? rank b Ranking.literals.
Lemma leb_total a b : leb a b=true \/ leb b a=true.
Proof. unfold leb. destruct (Nat.le_ge_cases (rank a Ranking.literals) (rank b Ranking.literals));
  [left|right]; now apply Nat.leb_le. Qed.
Definition equal := wire_literal_equal.
Lemma equal_sound a b : equal a b=true -> a=b. Proof. apply wire_literal_equal_sound. Qed.
End RankedOrder.
