(* Extraction *)
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlNativeString.
From Stdlib Require Import ExtrOcamlZInt.
Require Import AxiomFuzzer.Clause.Kernel.
Require Import AxiomFuzzer.Clause.Avatar.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Require Import AxiomFuzzer.Preprocess.Quantifiers.
Require Import AxiomFuzzer.Preprocess.SkolemModel.
Require Import AxiomFuzzer.Wire.Syntax.
Require Import AxiomFuzzer.Wire.Preprocess.
Require Import AxiomFuzzer.Wire.Refutation.
Require Import AxiomFuzzer.Source.Refutation.
Require Import AxiomFuzzer.Source.Validation.
Require Import AxiomFuzzer.Source.Kernel.
Require Import AxiomFuzzer.Source.Definitions.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction Inline Nat.compare.
Extraction "rocq_checker.ml" AxiomFuzzer.Clause.Kernel.check AxiomFuzzer.Clause.Kernel.check_list.
(* Inline the Stdlib integer realizers so extraction does not emit unused
   [rec] flags for (+) and truncated subtraction. *)
Extraction Inline Nat.add.
Extraction Inline Nat.compare.
(* Parenthesize the Stdlib subtraction realizer when it occurs inline. *)
Extract Inlined Constant Nat.sub => "(fun n m -> Stdlib.max 0 (n-m))".
Extract Inductive source_term => "Wire_types.source_term" ["Wire_types.B" "Wire_types.F" "Wire_types.App"].
Extract Inductive source_formula => "Wire_types.source_formula" ["Wire_types.Top" "Wire_types.Bot" "Wire_types.Pred" "Wire_types.Eq" "Wire_types.Neg" "Wire_types.Conj" "Wire_types.Disj" "Wire_types.All" "Wire_types.Ex"].
Extract Inductive schema => "Wire_types.schema" ["Wire_types.Comprehension" "Wire_types.Separation" "Wire_types.Replacement" "Wire_types.Unrestricted_separation" "Wire_types.Registered"].
Extract Inductive provenance => "Wire_types.origin" ["Wire_types.Fixed" "Wire_types.Imported" "Wire_types.Instance" "Wire_types.Registered_instance"].
Extract Inductive axiom => "Wire_types.axiom" ["(fun axiom_id name origin formula -> { Wire_types.axiom_id; name; origin; formula })"].
Extract Inlined Constant axiom_id => "(fun a -> a.Wire_types.axiom_id)".
Extract Inlined Constant axiom_name => "(fun a -> a.Wire_types.name)".
Extract Inlined Constant axiom_origin => "(fun a -> a.Wire_types.origin)".
Extract Inlined Constant axiom_formula => "(fun a -> a.Wire_types.formula)".
Extraction "source_checker.ml" formula_scoped bind_formula substitute_formula boolean_not boolean_and boolean_or checked_schema nnf normal_scoped bounded_cnf definition_variables checked_definitions instantiate_bound checked_universals eliminate_quantifiers wire_literal wire_predicate wire_support checked_wire_support wire_quantifiers wire_checked_universals wire_distributive_cnf wire_definitional_cnf theory validate_axiom expand_formula expansions_match.

(* The bridge checks the actual shared Wire and numeric checker values. These
   type aliases avoid a second translation or duplicate runtime representations. *)
Extract Inductive AxiomFuzzer.Clause.Kernel.term => "Rocq_checker.term" ["Rocq_checker.Var" "Rocq_checker.Fun"].
(* Stdlib's AVL comparison introduces Eq; extraction names the atom Eq0. *)
Extract Inductive AxiomFuzzer.Clause.Kernel.atom => "Rocq_checker.atom" ["Rocq_checker.Pred" "Rocq_checker.Eq0"].
Extract Inductive wire_symbol => "Source_checker.wire_symbol" ["Source_checker.Original" "Source_checker.Skolem"].
Extract Inductive wire_predicate => "Source_checker.wire_predicate" ["Source_checker.Named" "Source_checker.Auxiliary"].
Extract Inductive wire_term => "Source_checker.wire_term" ["Source_checker.V" "Source_checker.Fn"].
Extract Inductive wire_atom => "Source_checker.wire_atom" ["Source_checker.P" "Source_checker.E" "Source_checker.D"].
Extract Inductive wire_literal => "Source_checker.wire_literal" ["(fun (positive, atom) -> { Source_checker.positive; atom })"].
Extract Inlined Constant positive => "(fun l -> l.Source_checker.positive)".
Extract Inlined Constant atom => "(fun l -> l.Source_checker.atom)".
(* ExtrOcamlZInt, imported at the top for every extraction, realizes AVL heights
   as bounded machine integers; repeating the import here changes nothing. Extract
   the normalizer separately so the existing Wire record field names stay stable. *)
From Stdlib Require Import ExtrOcamlZInt.
Extraction "wire_normalizer.ml" AxiomFuzzer.Wire.Refutation.WireNormalize.
Extraction "wire_checker.ml" encoded_inputs.

(* Reuse all existing extracted representations in the final authority checker. *)
Extract Inductive AxiomFuzzer.Clause.Kernel.rule => "Rocq_checker.rule" ["Rocq_checker.Input" "Rocq_checker.Instance" "Rocq_checker.Copy" "Rocq_checker.Resolve" "Rocq_checker.Equality_resolve" "Rocq_checker.Paramodulate" "Rocq_checker.Equality_factor"].
Extract Inductive term_context => "Rocq_checker.term_context" ["Rocq_checker.Hole" "Rocq_checker.Under"].
Extract Inductive atom_context => "Rocq_checker.atom_context" ["Rocq_checker.In_pred" "Rocq_checker.In_eq_left" "Rocq_checker.In_eq_right"].
Extraction "avatar_checker.ml" AxiomFuzzer.Clause.Avatar.check.
Extract Inductive AxiomFuzzer.Clause.Avatar.fo_rule => "Avatar_checker.fo_rule" ["Avatar_checker.Ordinary" "Avatar_checker.Component"].
Extract Inductive AxiomFuzzer.Clause.Avatar.sat_rule => "Avatar_checker.sat_rule" ["Avatar_checker.Split" "Avatar_checker.Conflict" "Avatar_checker.Boolean_resolve"].
Extract Inductive AxiomFuzzer.Clause.Avatar.certificate => "Avatar_checker.certificate"
  ["(fun components fo_steps splits boolean_steps boolean_root -> { Avatar_checker.components; fo_steps; splits; boolean_steps; boolean_root })"].
Extract Inlined Constant AxiomFuzzer.Clause.Avatar.components => "(fun c -> c.Avatar_checker.components)".
Extract Inlined Constant AxiomFuzzer.Clause.Avatar.fo_steps => "(fun c -> c.Avatar_checker.fo_steps)".
Extract Inlined Constant AxiomFuzzer.Clause.Avatar.splits => "(fun c -> c.Avatar_checker.splits)".
Extract Inlined Constant AxiomFuzzer.Clause.Avatar.boolean_steps => "(fun c -> c.Avatar_checker.boolean_steps)".
Extract Inlined Constant AxiomFuzzer.Clause.Avatar.boolean_root => "(fun c -> c.Avatar_checker.boolean_root)".
Extract Inlined Constant AxiomFuzzer.Clause.Avatar.check => "Avatar_checker.check".
Extract Inductive matrix => "Source_checker.matrix" ["Source_checker.MLiteral" "Source_checker.MConj" "Source_checker.MDisj"].
Extract Inductive definition_literal => "Source_checker.definition_literal" ["Source_checker.DBase" "Source_checker.DAux"].
Extract Inductive definition => "Source_checker.definition" ["(fun conjunction arguments children -> { Source_checker.conjunction; arguments; children })"].
Extract Inlined Constant conjunction => "(fun d -> d.Source_checker.conjunction)".
Extract Inlined Constant arguments => "(fun d -> d.Source_checker.arguments)".
Extract Inlined Constant children => "(fun d -> d.Source_checker.children)".
Extract Inductive theory => "Source_checker.theory" ["(fun theory_name unrestricted_signature function_symbols predicate_symbols fixed_axioms allowed_schemas registered_check -> { Source_checker.theory_name; unrestricted_signature; function_symbols; predicate_symbols; fixed_axioms; allowed_schemas; registered_check })"].
Extract Inlined Constant unrestricted_signature => "(fun t -> t.Source_checker.unrestricted_signature)".
Extract Inlined Constant theory_name => "(fun t -> t.Source_checker.theory_name)".
Extract Inlined Constant function_symbols => "(fun t -> t.Source_checker.function_symbols)".
Extract Inlined Constant predicate_symbols => "(fun t -> t.Source_checker.predicate_symbols)".
Extract Inlined Constant fixed_axioms => "(fun t -> t.Source_checker.fixed_axioms)".
Extract Inlined Constant allowed_schemas => "(fun t -> t.Source_checker.allowed_schemas)".
Extract Inlined Constant registered_check => "(fun t -> t.Source_checker.registered_check)".
Extraction "kernel_checker.ml" AxiomFuzzer.Source.Kernel.Kernel.

Require Import AxiomFuzzer.Reference.Certificate.
Require Import AxiomFuzzer.Reference.Theory.
Require Import AxiomFuzzer.Reference.Progress.
Extract Inductive AxiomFuzzer.Reference.Encoding.code => "Wire_types.code" ["Wire_types.Number" "Wire_types.Pair"].
Extraction "natural_checker.ml" direct_check reference_search reference_run certificate_value certificate_code
  proof_code permission_code equality_code axiom_at
  index_text index_value enumeration_name enumerated_check
  Progress.initial Progress.tick.
