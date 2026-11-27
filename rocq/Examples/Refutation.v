(* SourceRefutationExamples *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Require Import AxiomFuzzer.Preprocess.Quantifiers.
Require Import AxiomFuzzer.Wire.Syntax.
Require Import AxiomFuzzer.Wire.Preprocess.
Require Import AxiomFuzzer.Wire.Refutation.
Require Import AxiomFuzzer.Source.Refutation.
Require Import AxiomFuzzer.Clause.Kernel.
Import ListNotations.

(* A concrete, deliberately simple order instance. Sorting may preserve any
   order; only equality soundness matters for the refutation theorem. These
   examples discharge the interface laws rather than assuming native compare. *)
Module ExampleOrder <: WireOrder.
Definition function_name := nat.
Definition predicate_name := nat.
Definition leb (_ _ : wire_literal nat nat) := true.
Lemma leb_total a b : leb a b=true \/ leb b a=true. Proof. now left. Qed.
Definition equal (_ _ : wire_literal nat nat) := false.
Lemma equal_sound a b : equal a b=true -> a=b. Proof. discriminate. Qed.
End ExampleOrder.
Module Sound := SourceRefutation ExampleOrder.

Definition visit (_ : unit) := true.
Definition positive_source : source_formula nat nat := SAll (SPred 0 [SBound 0]).
Definition negative_source : source_formula nat nat := SEx (SConj [SNeg (SPred 0 [SBound 0]); SEq (SBound 0) (SBound 0)]).
Definition whole_source := SConj [positive_source;negative_source].
Definition witness : wire_term nat := Fn (Skolem 2 0) [].
Definition positive_matrix : matrix (bool * wire_atom nat nat) := MLiteral (true,P 0 [V (0,0)]).
Definition negative_matrix : matrix (bool * wire_atom nat nat) := MConj [MLiteral (false,P 0 [witness]); MLiteral (true,E witness witness)].
Definition whole_matrix := MConj [positive_matrix;negative_matrix].
Definition false_definition : definition (wire_atom nat nat) :=
  {| conjunction := true; arguments := []; children := [DBase false (P 0 [witness]);DBase true (E witness witness)] |}.
Definition whole_definition : definition (wire_atom nat nat) :=
  {| conjunction := true; arguments := [0]; children := [DBase true (P 0 [V (0,0)]);DAux true 0 []] |}.
Definition negative_lookup id := match id with 0 => Some false_definition | _ => None end.
Definition whole_lookup id := match id with 0 => Some false_definition | 1 => Some whole_definition | _ => None end.

(* Structural equality for the small fixture's base atoms; the positive result
   is justified by decidable equality, not an external equality oracle. *)
Fixpoint term_equal_dec (x y : wire_term nat) : {x=y}+{x<>y}.
Proof. decide equality; try (apply list_eq_dec; apply term_equal_dec); decide equality; apply Nat.eq_dec. Defined.
Definition atom_equal_dec (x y : wire_atom nat nat) : {x=y}+{x<>y}.
Proof. decide equality; try apply Nat.eq_dec; try (decide equality; apply Nat.eq_dec); try apply term_equal_dec; apply list_eq_dec; apply term_equal_dec. Defined.
Definition atom_equal x y := if atom_equal_dec x y then true else false.
Lemma atom_equal_sound x y : atom_equal x y=true -> x=y.
Proof. unfold atom_equal; destruct atom_equal_dec; auto; discriminate. Qed.

Definition output_or_empty {X} (value : option (list X)) := match value with Some xs => xs | None => [] end.
Definition positive_clauses := output_or_empty (wire_distributive_cnf visit 20 positive_matrix).
Definition negative_clauses := output_or_empty (wire_definitional_cnf negative_lookup visit atom_equal 1 20 2 negative_matrix (DAux true 0 [])).
Definition whole_distributive := output_or_empty (wire_distributive_cnf visit 20 whole_matrix).
Definition whole_definitional := output_or_empty (wire_definitional_cnf whole_lookup visit atom_equal 2 20 2 whole_matrix (DAux true 1 [0])).
Definition positive_input : source_input nat nat :=
  {| source_id := 1; source_text := positive_source; source_matrix := positive_matrix; source_clauses := positive_clauses |}.
Definition negative_input : source_input nat nat :=
  {| source_id := 2; source_text := negative_source; source_matrix := negative_matrix; source_clauses := negative_clauses |}.
Definition mixed_inputs := [positive_input;negative_input].
Definition normalizations cs := map (fun c => match Sound.Normalize.normalize 20 c with Some out => out | None => [] end) cs.
Fixpoint encode_term (t : wire_term nat) := match t with V (_,i) => Var i | Fn _ ts => Fun 0 (map encode_term ts) end.
Definition encode_atom (a : wire_atom nat nat) := match a with
  | P p ts => Pred p (map encode_term ts) | E x y => Eq (encode_term x) (encode_term y)
  | D (_,id) ts => Pred (S id) (map encode_term ts) end.
Definition encode_clauses := map (map (fun l : wire_literal nat nat => (positive l,encode_atom (AxiomFuzzer.Wire.Syntax.atom l)))).
Definition decode_function id : option (wire_symbol nat) := match id with 0 => Some (Skolem 2 0) | _ => None end.
Definition decode_predicate id : option (wire_predicate nat) := match id with 0 => Some (Named 0) | S id => Some (Auxiliary (2,id)) end.

Fixpoint propose inputs db rules : option certificate := match rules with
  | [] => Some []
  | rule::rest => match infer inputs db rule with None => None | Some c =>
      match propose inputs (db++[c]) rest with None => None | Some proof => Some ((rule,c)::proof) end end end.
Definition proof_for inputs rules := output_or_empty (propose inputs [] rules).
Definition ground := Fun 0 [].
Definition mixed_normalized := normalizations (flat_map source_clauses mixed_inputs).
Definition mixed_numeric := encode_clauses mixed_normalized.
Definition mixed_proof := proof_for mixed_numeric
  [Input 0;Instance 0 [(0,ground)];Input 1;Resolve 1 0 2 1;Input 4;Resolve 3 0 4 0].
Definition distributive_normalized := normalizations whole_distributive.
Definition distributive_numeric := encode_clauses distributive_normalized.
Definition distributive_proof := proof_for distributive_numeric
  [Input 0;Instance 0 [(0,ground)];Input 1;Resolve 1 0 2 0].
Definition definitional_normalized := normalizations whole_definitional.
Definition definitional_numeric := encode_clauses definitional_normalized.
Definition definitional_proof := proof_for definitional_numeric
  [Input 6;Instance 0 [(0,ground)];Input 3;Instance 2 [(0,ground)];Resolve 1 0 3 0;
   Input 4;Instance 5 [(0,ground)];Resolve 1 0 6 0;Input 0;Resolve 7 0 8 0;Resolve 4 0 9 0].

Example mixed_refutation_checked : check mixed_numeric mixed_proof=true.
Proof. vm_compute; reflexivity. Qed.
Example distributive_refutation_checked : check distributive_numeric distributive_proof=true.
Proof. vm_compute; reflexivity. Qed.
Example definitional_refutation_checked : check definitional_numeric definitional_proof=true.
Proof. vm_compute; reflexivity. Qed.

Lemma mixed_inputs_checked : Forall input_checked mixed_inputs.
Proof.
  constructor.
  - split.
    + exists visit,visit,20,(supply (AxiomFuzzer.Preprocess.Quantifiers.UAll 0 (AxiomFuzzer.Preprocess.Quantifiers.ULiteral (true,P 0 [V (0,0)]))) 1 0).
      split; vm_compute; reflexivity.
    + left. exists visit,20. vm_compute; reflexivity.
  - constructor; [|constructor]. split.
    + exists visit,visit,20,(supply (AxiomFuzzer.Preprocess.Quantifiers.UConj [AxiomFuzzer.Preprocess.Quantifiers.ULiteral (false,P 0 [witness]);AxiomFuzzer.Preprocess.Quantifiers.ULiteral (true,E witness witness)]) 0 1).
      split; vm_compute; reflexivity.
    + right. exists negative_lookup,visit,atom_equal,1,20,(DAux true 0 []).
      split; [exact atom_equal_sound|vm_compute; reflexivity].
Qed.

Section SourceTheorems.
Context {U : Type}.
Variable default : U.
Variable functions : nat -> list U -> U.
Variable predicates : nat -> list U -> Prop.
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.
Hypothesis functional_choice : forall R : list U -> U -> Prop,
  (forall args, exists x, R args x) -> exists g, forall args, R args (g args).

Theorem mixed_source_refutation : ~ Forall (source_input_holds functions predicates default) mixed_inputs.
Proof.
  eapply (Sound.source_inputs_check_sound default functions predicates excluded_middle functional_choice
    Nat.eqb Nat.eqb (fun x y => proj1 (Nat.eqb_eq x y)) (fun x y => proj1 (Nat.eqb_eq x y))
    (@snd nat nat) decode_function decode_predicate mixed_inputs 20 mixed_normalized mixed_numeric mixed_proof).
  - repeat constructor; simpl; intuition discriminate.
  - exact mixed_inputs_checked.
  - vm_compute. repeat constructor.
  - vm_compute; reflexivity.
  - exact mixed_refutation_checked.
Qed.
Theorem distributive_source_refutation :
  ~ source_holds functions predicates (fun _ => default) (fun _ => default) whole_source.
Proof.
  eapply (Sound.source_distributive_check_sound default functions predicates excluded_middle functional_choice
    Nat.eqb Nat.eqb (fun x y => proj1 (Nat.eqb_eq x y)) (fun x y => proj1 (Nat.eqb_eq x y))
    (@snd nat nat) decode_function decode_predicate 2 visit visit 20 whole_source
    (supply (AxiomFuzzer.Preprocess.Quantifiers.UConj [AxiomFuzzer.Preprocess.Quantifiers.UAll 0 (AxiomFuzzer.Preprocess.Quantifiers.ULiteral (true,P 0 [V (0,0)]));
      AxiomFuzzer.Preprocess.Quantifiers.UConj [AxiomFuzzer.Preprocess.Quantifiers.ULiteral (false,P 0 [witness]);AxiomFuzzer.Preprocess.Quantifiers.ULiteral (true,E witness witness)]]) 1 1)
    whole_matrix visit 20 whole_distributive 20 distributive_normalized distributive_numeric distributive_proof);
    try (vm_compute; reflexivity); try (vm_compute; repeat constructor).
Qed.
Theorem definitional_source_refutation :
  ~ source_holds functions predicates (fun _ => default) (fun _ => default) whole_source.
Proof.
  eapply (Sound.source_definitional_check_sound default functions predicates excluded_middle functional_choice
    Nat.eqb Nat.eqb (fun x y => proj1 (Nat.eqb_eq x y)) (fun x y => proj1 (Nat.eqb_eq x y))
    (@snd nat nat) decode_function decode_predicate 2 visit visit 20 whole_source
    (supply (AxiomFuzzer.Preprocess.Quantifiers.UConj [AxiomFuzzer.Preprocess.Quantifiers.UAll 0 (AxiomFuzzer.Preprocess.Quantifiers.ULiteral (true,P 0 [V (0,0)]));
      AxiomFuzzer.Preprocess.Quantifiers.UConj [AxiomFuzzer.Preprocess.Quantifiers.ULiteral (false,P 0 [witness]);AxiomFuzzer.Preprocess.Quantifiers.ULiteral (true,E witness witness)]]) 1 1)
    whole_matrix whole_lookup atom_equal 2 20 (DAux true 1 [0]) whole_definitional visit
    20 definitional_normalized definitional_numeric definitional_proof);
    try exact atom_equal_sound; try (vm_compute; reflexivity); try (vm_compute; repeat constructor).
Qed.
End SourceTheorems.
Print Assumptions mixed_source_refutation.
Print Assumptions distributive_source_refutation.
Print Assumptions definitional_source_refutation.
