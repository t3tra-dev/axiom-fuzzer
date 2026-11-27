(* SourceTheory *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Require Import AxiomFuzzer.Preprocess.Quantifiers.
Require Import AxiomFuzzer.Wire.Syntax.
Require Import AxiomFuzzer.Wire.Preprocess.
Import ListNotations.

(* The successful intermediate results of one Source axiom. A group may use
   either accepted CNF path; hybrid's choice does not affect this theorem. *)
Record source_input (F PT : Type) := {
  source_id : nat;
  source_text : source_formula F PT;
  source_matrix : matrix (bool * wire_atom F PT);
  source_clauses : list (@wire_clause F PT)
}.
Arguments source_id {F PT} _.
Arguments source_text {F PT} _.
Arguments source_matrix {F PT} _.
Arguments source_clauses {F PT} _.
Section Inputs.
Context {F PT : Type}.
Definition input_quantifiers (input : source_input F PT) := exists visit scope_visit limit r,
  wire_quantifiers visit limit (source_id input) (nnf true (source_text input))=Some r /\
  wire_checked_universals scope_visit limit (supplied_value r)=Some (source_matrix input).
Definition input_cnf (input : source_input F PT) :=
  (exists visit budget, wire_distributive_cnf visit budget (source_matrix input)=Some (source_clauses input)) \/
  (exists lookup visit equal size budget root,
    (forall a b, equal a b=true -> a=b) /\
    wire_definitional_cnf lookup visit equal size budget (source_id input) (source_matrix input) root=Some (source_clauses input)).
Definition input_checked input := input_quantifiers input /\ input_cnf input.
Lemma input_matrix_owned input : input_quantifiers input ->
  matrix_all (fun l => owned_base (source_id input) (snd l)) (source_matrix input).
Proof. intros [visit [scope_visit [limit [r [Run Scope]]]]]. eapply wire_matrix_owned; eauto. Qed.
Lemma input_matrix_local input : input_quantifiers input ->
  matrix_all (fun l => local_atom (snd l)) (source_matrix input).
Proof. intros [visit [scope_visit [limit [r [Run Scope]]]]]. eapply wire_matrix_local; exact Scope. Qed.
Lemma input_clauses_local input : input_checked input -> Forall local_clause (source_clauses input).
Proof.
  intros [Quantifiers [[visit [budget CNF]]|[lookup [visit [equal [size [budget [root [Equal CNF]]]]]]]]].
  - eapply wire_distributive_local; [exact (input_matrix_local input Quantifiers)|exact CNF].
  - eapply wire_definitional_local; exact CNF.
Qed.
Lemma input_clauses_auxiliary input : input_checked input ->
  Forall (Forall (auxiliary_at (source_id input))) (source_clauses input).
Proof.
  intros [Quantifiers [[visit [budget CNF]]|[lookup [visit [equal [size [budget [root [Equal CNF]]]]]]]]].
  - eapply distributive_auxiliary_at; [exact (input_matrix_owned input Quantifiers)|exact CNF].
  - eapply definitional_auxiliary_at; exact CNF.
Qed.
End Inputs.

Section Models.
Context {F PT U : Type}.
Variable functions : F -> list U -> U.
Variable predicates : PT -> list U -> Prop.
Variable default : U.
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.
Hypothesis functional_choice : forall R : list U -> U -> Prop,
  (forall args, exists x, R args x) -> exists g, forall args, R args (g args).
Definition source_input_holds (input : source_input F PT) :=
  source_holds functions predicates (fun _ => default) (fun _ => default) (source_text input).
Definition input_matrix_holds sk defs input := forall rho : nat -> U,
  wire_matrix_holds functions predicates sk defs (fun v => rho (snd v)) (source_matrix input).
Let no_definitions (_ : nat * nat) (_ : list U) := False.

(* First fix one Skolem interpretation for all axioms. No auxiliary predicates
   are chosen yet: unused declarations can mention another axiom's Skolem. *)
Theorem source_matrices_model inputs : NoDup (map source_id inputs) -> Forall input_quantifiers inputs ->
  Forall source_input_holds inputs -> exists sk, Forall (input_matrix_holds sk no_definitions) inputs.
Proof.
  induction inputs as [|input inputs IH]; intros Unique Quantifiers Sources.
  - exists (fun _ _ => default); constructor.
  - inversion Unique as [|id ids Fresh RestUnique]; subst.
    inversion Quantifiers as [|i items HeadQuant TailQuant]; subst.
    inversion Sources as [|i items HeadSource TailSource]; subst.
    destruct (IH RestUnique TailQuant TailSource) as [sk TailModel].
    destruct HeadQuant as [visit [scope_visit [limit [r [Run Scope]]]]].
    destruct (proj1 (wire_source_matrix_equisat functions predicates default sk no_definitions (source_id input)
      excluded_middle functional_choice visit scope_visit limit (source_text input) r (source_matrix input) Run Scope)
      HeadSource) as [fresh HeadModel].
    exists (axiom_symbols sk (source_id input) fresh). constructor; [exact HeadModel|].
    rewrite Forall_forall in TailQuant, TailModel |- *. intros other In rho.
    assert (Agree : forall id args, sk (source_id other,id) args=
      axiom_symbols sk (source_id input) fresh (source_id other,id) args).
    { intros id args. rewrite axiom_symbols_other; [reflexivity|]. simpl. intros Eq.
      apply Fresh. rewrite <- Eq. apply in_map; exact In. }
    apply (proj1 (owned_matrix_holds functions predicates (source_id other) (source_matrix other) sk
      (axiom_symbols sk (source_id input) fresh) no_definitions no_definitions (fun v => rho (snd v))
      (input_matrix_owned other (TailQuant other In)) Agree)).
    apply (TailModel other In).
Qed.

Lemma matrix_definitions_change sk defs other input : input_quantifiers input ->
  input_matrix_holds sk defs input -> input_matrix_holds sk other input.
Proof.
  intros Quantifiers Model rho. apply (proj1 (owned_matrix_holds functions predicates (source_id input) (source_matrix input)
    sk sk defs other (fun v => rho (snd v)) (input_matrix_owned input Quantifiers) (fun _ _ => eq_refl))).
  apply Model.
Qed.
Lemma packed_literals_model sk defs rho raw :
  AxiomFuzzer.Preprocess.NormalForms.clauses_hold (fun l => signed (fst l) (wire_atom_holds functions predicates sk defs (fun v => rho (snd v)) (snd l))) raw <->
  AxiomFuzzer.Preprocess.NormalForms.clauses_hold (wire_literal_holds functions predicates sk defs (fun v => rho (snd v))) (map (map pack_literal) raw).
Proof.
  induction raw as [|c raw IH]; simpl; [tauto|]. rewrite <- IH.
  assert (Clause : AxiomFuzzer.Preprocess.NormalForms.clause_holds (fun l => signed (fst l) (wire_atom_holds functions predicates sk defs (fun v => rho (snd v)) (snd l))) c <->
    AxiomFuzzer.Preprocess.NormalForms.clause_holds (wire_literal_holds functions predicates sk defs (fun v => rho (snd v))) (map pack_literal c)).
  { induction c as [|[sign a] c Hc]; simpl; [tauto|]. destruct sign; simpl in *; now rewrite Hc. }
  tauto.
Qed.
Lemma packed_definitions_model sk defs ax aux rho raw : Forall (Forall (fun l => definition_is_base l=true)) raw ->
  (AxiomFuzzer.Preprocess.NormalForms.clauses_hold (definition_holds (fun a rho => wire_atom_holds functions predicates sk defs (fun v => rho (snd v)) a) aux rho) raw <->
   AxiomFuzzer.Preprocess.NormalForms.clauses_hold (wire_literal_holds functions predicates sk (axiom_symbols defs ax aux) (fun v => rho (snd v)))
     (map (map (pack_definition ax)) raw)).
Proof.
  assert (Literal : forall l, definition_is_base l=true ->
    (definition_holds (fun a rho => wire_atom_holds functions predicates sk defs (fun v => rho (snd v)) a) aux rho l <->
     wire_literal_holds functions predicates sk (axiom_symbols defs ax aux) (fun v => rho (snd v)) (pack_definition ax l))).
  { intros [sign a|sign id vars]; simpl.
    - destruct a; try discriminate; intros _; destruct sign; reflexivity.
    - intros _. unfold wire_literal_holds, pack_definition; simpl. rewrite axiom_symbols_here.
      assert (Args : map (wire_eval functions sk (fun v => rho (snd v))) (map (fun i => V (0,i)) vars)=map rho vars)
        by (rewrite map_map; reflexivity).
      rewrite Args. destruct sign; reflexivity. }
  intros All. induction All as [|c cs Head Tail IH]; simpl; [tauto|]. rewrite <- IH.
  assert (Clause : AxiomFuzzer.Preprocess.NormalForms.clause_holds (definition_holds (fun a rho => wire_atom_holds functions predicates sk defs (fun v => rho (snd v)) a) aux rho) c <->
    AxiomFuzzer.Preprocess.NormalForms.clause_holds (wire_literal_holds functions predicates sk (axiom_symbols defs ax aux) (fun v => rho (snd v))) (map (pack_definition ax) c)).
  { induction Head as [|l c Base Rest HC]; simpl; [tauto|]. now rewrite (Literal l Base), HC. }
  tauto.
Qed.

Lemma input_cnf_extension sk old_definitions input : input_checked input ->
  input_matrix_holds sk no_definitions input ->
  exists aux, Forall (wire_valid functions predicates sk (axiom_symbols old_definitions (source_id input) aux)) (source_clauses input).
Proof.
  intros Checked Matrix. pose proof (input_clauses_local input Checked) as Local.
  destruct Checked as [Quantifiers CNF].
  destruct CNF as [[visit [budget CNF]]|[lookup [visit [equal [size [budget [root [Equal CNF]]]]]]]].
  - exists (fun _ _ => False). apply (proj1 (local_clauses_model functions predicates sk
      (axiom_symbols old_definitions (source_id input) (fun _ _ => False)) (source_clauses input) Local)).
    intros rho. unfold wire_distributive_cnf in CNF.
    destruct (bounded_cnf visit budget (source_matrix input)) as [raw|] eqn:Raw; [|discriminate].
    inversion CNF. apply packed_literals_model.
    apply (bounded_cnf_correct _ (source_matrix input) visit budget raw Raw).
    eapply matrix_definitions_change; eauto.
  - apply wire_definitional_parts in CNF as [raw [Raw [Output Base]]].
    assert (Model : forall rho, matrix_holds
      (fun l => signed (fst l) (wire_atom_holds functions predicates sk old_definitions (fun v => rho (snd v)) (snd l)))
      (source_matrix input)).
    { eapply matrix_definitions_change; eauto. }
    destruct (proj1 (checked_definitions_equisat
      (fun a rho => wire_atom_holds functions predicates sk old_definitions (fun v => rho (snd v)) a)
      excluded_middle lookup equal Equal wire_support (wire_local_support functions predicates sk old_definitions)
      default visit size budget (source_matrix input) root raw Raw) Model) as [aux Clauses].
    exists aux. apply (proj1 (local_clauses_model functions predicates sk
      (axiom_symbols old_definitions (source_id input) aux) (source_clauses input) Local)).
    intros rho. rewrite Output. apply packed_definitions_model; [exact Base|apply Clauses].
Qed.

(* Then choose the auxiliaries with the entire Skolem interpretation fixed.
   Every emitted D belongs to its axiom, even in an unused declaration. *)
Theorem source_cnf_models inputs sk : NoDup (map source_id inputs) -> Forall input_checked inputs ->
  Forall (input_matrix_holds sk no_definitions) inputs ->
  exists aux, Forall (fun input => Forall (wire_valid functions predicates sk aux) (source_clauses input)) inputs.
Proof.
  induction inputs as [|input inputs IH]; intros Unique Checked Matrices.
  - exists no_definitions; constructor.
  - inversion Unique as [|id ids Fresh RestUnique]; subst.
    inversion Checked as [|i items HeadCheck TailCheck]; subst.
    inversion Matrices as [|i items HeadMatrix TailMatrix]; subst.
    destruct (IH RestUnique TailCheck TailMatrix) as [aux TailModel].
    destruct (input_cnf_extension sk aux input HeadCheck HeadMatrix) as [fresh HeadModel].
    exists (axiom_symbols aux (source_id input) fresh). constructor; [exact HeadModel|].
    rewrite Forall_forall in TailCheck, TailModel |- *. intros other In.
    pose proof (input_clauses_auxiliary other (TailCheck other In)) as Owned.
    specialize (TailModel other In). rewrite Forall_forall in Owned, TailModel |- *. intros c Hc.
    assert (Agree : forall id args, aux (source_id other,id) args <->
      axiom_symbols aux (source_id input) fresh (source_id other,id) args).
    { intros id args. rewrite axiom_symbols_other; [reflexivity|]. simpl. intros Eq.
      apply Fresh. rewrite <- Eq. apply in_map; exact In. }
    apply (proj1 (auxiliary_valid_agree functions predicates (source_id other) c sk aux
      (axiom_symbols aux (source_id input) fresh) (Owned c Hc) Agree)).
    exact (TailModel c Hc).
Qed.
Theorem source_inputs_model inputs : NoDup (map source_id inputs) -> Forall input_checked inputs ->
  Forall source_input_holds inputs -> exists sk aux,
  Forall (wire_valid functions predicates sk aux) (flat_map source_clauses inputs).
Proof.
  intros Unique Checked Sources. assert (Quantifiers : Forall input_quantifiers inputs).
  { eapply Forall_impl; [|exact Checked]. intros input [Run _]; exact Run. }
  destruct (source_matrices_model inputs Unique Quantifiers Sources) as [sk Matrices].
  destruct (source_cnf_models inputs sk Unique Checked Matrices) as [aux Clauses].
  exists sk, aux. clear Unique Checked Sources Quantifiers Matrices.
  induction Clauses; simpl; [constructor|]. apply Forall_app; split; assumption.
Qed.
End Models.
Print Assumptions source_matrices_model.
Print Assumptions source_cnf_models.
Print Assumptions source_inputs_model.

(* SourceRefutation *)
From Stdlib Require Import List.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Require Import AxiomFuzzer.Preprocess.Quantifiers.
Require Import AxiomFuzzer.Wire.Syntax.
Require Import AxiomFuzzer.Wire.Preprocess.
Require Import AxiomFuzzer.Wire.Refutation.
Require Import AxiomFuzzer.Clause.Kernel.
Require AxiomFuzzer.Clause.Avatar.
Import ListNotations.

Module SourceRefutation (Order : WireOrder).
Module Refutation := WireRefutation Order.
Module Normalize := Refutation.Normalize.
Section Soundness.
Context {U : Type}.
Variable default : U.
Variable functions : Order.function_name -> list U -> U.
Variable predicates : Order.predicate_name -> list U -> Prop.
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.
Hypothesis functional_choice : forall R : list U -> U -> Prop,
  (forall args, exists x, R args x) -> exists g, forall args, R args (g args).
Variable equal_function : Order.function_name -> Order.function_name -> bool.
Variable equal_predicate : Order.predicate_name -> Order.predicate_name -> bool.
Hypothesis equal_function_sound : forall f g, equal_function f g=true -> f=g.
Hypothesis equal_predicate_sound : forall p q, equal_predicate p q=true -> p=q.
Variable encode_variable : (nat * nat) -> nat.
Variable decode_function : nat -> option (wire_symbol Order.function_name).
Variable decode_predicate : nat -> option (wire_predicate Order.predicate_name).
Let initial_skolem (_ : nat * nat) (_ : list U) := default.
Let initial_definitions (_ : nat * nat) (_ : list U) := False.

Theorem source_distributive_check_sound ax visit scope_visit limit source r m cnf_visit budget cs
    variable_limit normalized numeric proof :
  wire_quantifiers visit limit ax (nnf true source)=Some r ->
  wire_checked_universals scope_visit limit (supplied_value r)=Some m ->
  wire_distributive_cnf cnf_visit budget m=Some cs ->
  Forall2 (fun c result => Normalize.normalize variable_limit c=Some result) cs normalized ->
  encoded_inputs equal_function equal_predicate encode_variable decode_function decode_predicate normalized numeric=true ->
  AxiomFuzzer.Clause.Kernel.check numeric proof=true ->
  ~ source_holds functions predicates (fun _ => default) (fun _ => default) source.
Proof.
  intros Run Scope CNF Normalized Encoded Checked Source.
  destruct (proj1 (wire_source_distributive_equisat functions predicates default initial_skolem initial_definitions ax
    excluded_middle functional_choice visit scope_visit limit source r m cnf_visit budget cs Run Scope CNF) Source) as [sk Model].
  assert (Local : Forall local_clause cs).
  { eapply wire_distributive_local; [eapply wire_matrix_local; exact Scope|exact CNF]. }
  pose proof (proj1 (local_clauses_model functions predicates (axiom_symbols initial_skolem ax sk)
    initial_definitions cs Local) Model) as Valid.
  exact (Refutation.normalized_wire_check_sound default functions predicates (axiom_symbols initial_skolem ax sk)
    initial_definitions equal_function equal_predicate equal_function_sound equal_predicate_sound
    encode_variable decode_function decode_predicate variable_limit cs normalized numeric proof Normalized Encoded Checked Valid).
Qed.

Theorem source_definitional_check_sound ax visit scope_visit limit source r m lookup equal size budget root cs cnf_visit
    variable_limit normalized numeric proof :
  (forall a b, equal a b=true -> a=b) ->
  wire_quantifiers visit limit ax (nnf true source)=Some r ->
  wire_checked_universals scope_visit limit (supplied_value r)=Some m ->
  wire_definitional_cnf lookup cnf_visit equal size budget ax m root=Some cs ->
  Forall2 (fun c result => Normalize.normalize variable_limit c=Some result) cs normalized ->
  encoded_inputs equal_function equal_predicate encode_variable decode_function decode_predicate normalized numeric=true ->
  AxiomFuzzer.Clause.Kernel.check numeric proof=true ->
  ~ source_holds functions predicates (fun _ => default) (fun _ => default) source.
Proof.
  intros Equal Run Scope CNF Normalized Encoded Checked Source.
  destruct (proj1 (wire_source_definitional_equisat functions predicates default initial_skolem initial_definitions ax
    excluded_middle functional_choice visit scope_visit limit source r m lookup equal size budget root cs cnf_visit
    Equal Run Scope CNF) Source) as [sk [aux Model]].
  pose proof (wire_definitional_local lookup cnf_visit equal size budget ax m root cs CNF) as Local.
  pose proof (proj1 (local_clauses_model functions predicates (axiom_symbols initial_skolem ax sk)
    (axiom_symbols initial_definitions ax aux) cs Local) Model) as Valid.
  exact (Refutation.normalized_wire_check_sound default functions predicates (axiom_symbols initial_skolem ax sk)
    (axiom_symbols initial_definitions ax aux) equal_function equal_predicate equal_function_sound equal_predicate_sound
    encode_variable decode_function decode_predicate variable_limit cs normalized numeric proof Normalized Encoded Checked Valid).
Qed.
Theorem source_inputs_check_sound inputs variable_limit normalized numeric proof :
  NoDup (map source_id inputs) -> Forall input_checked inputs ->
  Forall2 (fun c result => Normalize.normalize variable_limit c=Some result)
    (flat_map source_clauses inputs) normalized ->
  encoded_inputs equal_function equal_predicate encode_variable decode_function decode_predicate normalized numeric=true ->
  AxiomFuzzer.Clause.Kernel.check numeric proof=true ->
  ~ Forall (source_input_holds functions predicates default) inputs.
Proof.
  intros Unique Inputs Normalized Encoded Checked Sources.
  destruct (source_inputs_model functions predicates default excluded_middle functional_choice inputs Unique Inputs Sources)
    as [sk [aux Model]].
  exact (Refutation.normalized_wire_check_sound default functions predicates sk aux equal_function equal_predicate
    equal_function_sound equal_predicate_sound encode_variable decode_function decode_predicate
    variable_limit (flat_map source_clauses inputs) normalized numeric proof Normalized Encoded Checked Model).
Qed.
Theorem source_inputs_avatar_check_sound inputs variable_limit normalized numeric proof :
  NoDup (map source_id inputs) -> Forall input_checked inputs ->
  Forall2 (fun c result => Normalize.normalize variable_limit c=Some result)
    (flat_map source_clauses inputs) normalized ->
  encoded_inputs equal_function equal_predicate encode_variable decode_function decode_predicate normalized numeric=true ->
  AxiomFuzzer.Clause.Avatar.check numeric proof=true ->
  ~ Forall (source_input_holds functions predicates default) inputs.
Proof.
  intros Unique Inputs Normalized Encoded Checked Sources.
  destruct (source_inputs_model functions predicates default excluded_middle functional_choice inputs Unique Inputs Sources)
    as [sk [aux Model]].
  assert (NormalizedModel : Forall (wire_valid functions predicates sk aux) normalized).
  { clear Encoded Checked. revert Model.
    induction Normalized as [|c result original normalized Here Rest IH]; intros Model; [constructor|].
    inversion Model; subst. constructor.
    - now apply (Normalize.normalize_forward functions predicates sk aux variable_limit c result Here).
    - now apply IH. }
  pose proof (encoded_inputs_valid equal_function equal_predicate encode_variable decode_function decode_predicate
    equal_function_sound equal_predicate_sound default functions predicates sk aux normalized numeric Encoded NormalizedModel)
    as NumericModel.
  eapply (AxiomFuzzer.Clause.Avatar.check_sound _ _ excluded_middle numeric proof Checked default).
  exact NumericModel.
Qed.
End Soundness.
Print Assumptions source_distributive_check_sound.
Print Assumptions source_definitional_check_sound.
Print Assumptions source_inputs_check_sound.
Print Assumptions source_inputs_avatar_check_sound.
End SourceRefutation.
