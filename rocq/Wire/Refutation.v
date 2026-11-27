(* WireNormalize *)
From Stdlib Require Import List Bool Arith.PeanoNat Sorting.Mergesort Sorting.Permutation Lia FMapAVL FMapFacts OrderedTypeEx.
Require Import AxiomFuzzer.Wire.Syntax.
Import ListNotations.

Definition variable_equal (x y : nat * nat) := (fst x =? fst y) && (snd x =? snd y).
Lemma variable_equal_spec x y : variable_equal x y=true <-> x=y.
Proof. destruct x,y; unfold variable_equal; simpl. rewrite andb_true_iff, !Nat.eqb_eq. split; intros H; [destruct H; now subst|now inversion H]. Qed.
Fixpoint first_variables_acc vars seen :=
  match vars with
  | [] => seen
  | v::vars => first_variables_acc vars (if existsb (variable_equal v) seen then seen else v::seen)
  end.
Definition first_variables vars := rev (first_variables_acc vars []).
Lemma first_variables_acc_members vars : forall seen v,
  In v (first_variables_acc vars seen) <-> In v vars \/ In v seen.
Proof.
  induction vars as [|x vars IH]; intros seen v; simpl; [tauto|].
  destruct (existsb (variable_equal x) seen) eqn:Found; rewrite IH; simpl.
  - apply existsb_exists in Found as [y [Hy Eq]]. apply variable_equal_spec in Eq; subst y.
    split; [tauto|]. intros [[Eq|In]|In]; [subst v; auto|auto|auto].
  - tauto.
Qed.
Lemma first_variables_members vars v : In v (first_variables vars) <-> In v vars.
Proof. unfold first_variables. rewrite <- in_rev, first_variables_acc_members. simpl; tauto. Qed.
Fixpoint variable_index v vars :=
  match vars with
  | [] => None
  | x::vars => if variable_equal v x then Some 0 else option_map S (variable_index v vars)
  end.
Lemma variable_index_hit v vars : forall i, variable_index v vars=Some i -> nth_error vars i=Some v.
Proof.
  induction vars as [|x vars IH]; intros i; simpl; [discriminate|].
  destruct (variable_equal v x) eqn:Eq.
  - apply variable_equal_spec in Eq; subst x. intros H; inversion H; reflexivity.
  - destruct (variable_index v vars) as [j|] eqn:Found; [|discriminate].
    intros H; inversion H; subst i; simpl. now apply IH.
Qed.
Lemma variable_index_present v vars : In v vars -> exists i, variable_index v vars=Some i.
Proof.
  induction vars as [|x vars IH]; simpl; [tauto|].
  destruct (variable_equal v x) eqn:Eq; [eauto|].
  intros [Same|In].
  - subst x. assert (variable_equal v v=true) by (apply variable_equal_spec; reflexivity). congruence.
  - destruct (IH In) as [i Found]. rewrite Found; simpl; eauto.
Qed.
Lemma variable_index_bound v vars i : variable_index v vars=Some i -> i<length vars.
Proof. intros H. apply variable_index_hit in H. apply nth_error_Some. now rewrite H. Qed.
Definition local_name vars v := (0, match variable_index v vars with Some i => i | None => 0 end).

(* AVL lookup preserves first-occurrence numbering without scanning the full
   variable list for every occurrence. The list version above is the spec. *)
Module VariableOrder := PairOrderedType Nat_as_OT Nat_as_OT.
Module VariableMap := FMapAVL.Make VariableOrder.
Module VariableFacts := FMapFacts.WFacts_fun VariableOrder VariableMap.
Lemma variable_order_eq x y : VariableOrder.eq x y <-> x=y.
Proof. destruct x,y; unfold VariableOrder.eq; simpl; unfold Nat_as_OT.eq; split; [intros [H K]; now subst|intros H; now inversion H]. Qed.
Fixpoint collect_variables vars (known : VariableMap.t unit) seen :=
  match vars with
  | [] => seen
  | v::rest => if VariableMap.mem v known then collect_variables rest known seen
      else collect_variables rest (VariableMap.add v tt known) (v::seen)
  end.
Lemma collect_variables_correct vars : forall known seen,
  (forall v, VariableMap.In v known <-> In v seen) ->
  collect_variables vars known seen=first_variables_acc vars seen.
Proof.
  induction vars as [|v vars IH]; intros known seen Known; simpl; [reflexivity|].
  assert (Same : VariableMap.mem v known=existsb (variable_equal v) seen).
  { apply VariableFacts.eq_bool_alt. rewrite <- VariableFacts.mem_in_iff, Known, existsb_exists.
    split.
    - intros In. exists v. split; [exact In|apply variable_equal_spec; reflexivity].
    - intros [x [In Eq]]. apply variable_equal_spec in Eq; now subst x. }
  rewrite Same. destruct (existsb (variable_equal v) seen); apply IH; [exact Known|].
  intros x. rewrite VariableFacts.add_in_iff.
  change (VariableOrder.eq v x \/ VariableMap.In x known <-> In x (v::seen)).
  rewrite variable_order_eq, Known; reflexivity.
Qed.
Definition collected_variables vars := rev_append (collect_variables vars (VariableMap.empty unit) []) [].
Lemma collected_variables_correct vars : collected_variables vars=first_variables vars.
Proof.
  unfold collected_variables, first_variables. rewrite <- rev_alt. f_equal. apply collect_variables_correct.
  intros v. rewrite VariableFacts.empty_in_iff; reflexivity.
Qed.
Fixpoint index_variables vars offset :=
  match vars with
  | [] => VariableMap.empty nat
  | v::rest => VariableMap.add v offset (index_variables rest (S offset))
  end.
Lemma index_variables_correct vars : forall offset v,
  VariableMap.find v (index_variables vars offset)=option_map (fun i => offset+i) (variable_index v vars).
Proof.
  induction vars as [|x vars IH]; intros offset v; simpl; [apply VariableFacts.empty_o|].
  destruct (variable_equal v x) eqn:Eq.
  - apply variable_equal_spec in Eq; subst x. rewrite VariableFacts.add_eq_o by (apply variable_order_eq; reflexivity).
    simpl; now rewrite Nat.add_0_r.
  - rewrite VariableFacts.add_neq_o.
    + rewrite IH. destruct (variable_index v vars); simpl; [f_equal; lia|reflexivity].
    + intros Equal. apply variable_order_eq in Equal; subst x.
      assert (variable_equal v v=true) by (apply variable_equal_spec; reflexivity). congruence.
Qed.
Definition indexed_name names v := (0,match VariableMap.find v names with Some i => i | None => 0 end).
Lemma indexed_name_correct vars v : indexed_name (index_variables vars 0) v=local_name vars v.
Proof. unfold indexed_name, local_name. rewrite index_variables_correct. now destruct (variable_index v vars). Qed.

Module Type WireOrder.
  Parameter function_name predicate_name : Type.
  Parameter leb : wire_literal function_name predicate_name -> wire_literal function_name predicate_name -> bool.
  Parameter leb_total : forall a b, leb a b=true \/ leb b a=true.
  Parameter equal : wire_literal function_name predicate_name -> wire_literal function_name predicate_name -> bool.
  Parameter equal_sound : forall a b, equal a b=true -> a=b.
End WireOrder.

Module WireNormalize (Order : WireOrder).
Module LiteralOrder <: Orders.TotalLeBool'.
  Definition t := wire_literal Order.function_name Order.predicate_name.
  Definition leb := Order.leb.
  Lemma leb_total x y : leb x y=true \/ leb y x=true.
  Proof. apply Order.leb_total. Qed.
End LiteralOrder.
Module LiteralSort := Mergesort.Sort LiteralOrder.
Fixpoint unique_after previous literals :=
  match literals with
  | [] => []
  | l::rest => if Order.equal previous l then unique_after previous rest else l::unique_after l rest
  end.
Definition unique_sorted literals := match literals with [] => [] | l::rest => l::unique_after l rest end.
Definition sort_clause literals := unique_sorted (LiteralSort.sort literals).
Definition normalize limit c :=
  let ordered := sort_clause c in
  let occurrences := clause_variables ordered in
  (* Small clauses avoid allocating two balanced trees. Both branches have
     exactly the same first-occurrence numbering, proved below. *)
  if length occurrences <=? 32 then
    let vars := first_variables occurrences in
    if length vars <=? limit then Some (sort_clause (rename_clause (local_name vars) ordered)) else None
  else
    let vars := collected_variables occurrences in
    if length vars <=? limit then
      let names := index_variables vars 0 in
      Some (sort_clause (rename_clause (indexed_name names) ordered)) else None.
Lemma normalize_spec limit c : normalize limit c=
  let ordered := sort_clause c in
  let vars := first_variables (clause_variables ordered) in
  if length vars <=? limit then Some (sort_clause (rename_clause (local_name vars) ordered)) else None.
Proof.
  unfold normalize. cbn zeta.
  destruct (length (clause_variables (sort_clause c)) <=? 32); [reflexivity|].
  rewrite collected_variables_correct.
  change (@length VariableMap.key) with (@length (nat * nat)).
  destruct (length (first_variables (clause_variables (sort_clause c))) <=? limit); [|reflexivity].
  do 2 f_equal. apply rename_clause_ext. intros v; apply indexed_name_correct.
Qed.

Lemma unique_after_members : forall literals previous l,
  In l (previous::unique_after previous literals) <-> In l (previous::literals).
Proof.
  induction literals as [|x rest IH]; intros previous l; simpl; [tauto|].
  destruct (Order.equal previous x) eqn:Eq.
  - apply Order.equal_sound in Eq; subst x.
    change (In l (previous::unique_after previous rest) <-> previous=l \/ previous=l \/ In l rest).
    rewrite IH; simpl; tauto.
  - specialize (IH x l). simpl in IH. simpl; tauto.
Qed.
Theorem sort_clause_members c l : In l (sort_clause c) <-> In l c.
Proof.
  unfold sort_clause.
  assert (Unique : forall ls, In l (unique_sorted ls) <-> In l ls).
  { intros [|x xs]; simpl; [tauto|apply unique_after_members]. }
  rewrite Unique. split; apply Permutation_in; [apply Permutation_sym|]; apply LiteralSort.Permuted_sort.
Qed.

Section Semantics.
Context {U : Type}.
Variable functions : Order.function_name -> list U -> U.
Variable predicates : Order.predicate_name -> list U -> Prop.
Variable skolem : (nat * nat) -> list U -> U.
Variable definitions : (nat * nat) -> list U -> Prop.
Let holds := wire_clause_holds functions predicates skolem definitions.
Let valid := wire_valid functions predicates skolem definitions.
Lemma sort_clause_holds rho c : holds rho (sort_clause c) <-> holds rho c.
Proof. unfold holds. rewrite !wire_clause_member. setoid_rewrite sort_clause_members. reflexivity. Qed.
Theorem normalize_forward limit c result : normalize limit c=Some result -> valid c -> valid result.
Proof.
  rewrite normalize_spec. cbn zeta.
  destruct (length (first_variables (clause_variables (sort_clause c))) <=? limit); [|discriminate].
  intros Accepted Model. inversion Accepted; subst result. intros rho. apply sort_clause_holds.
  apply rename_clause_holds, sort_clause_holds, Model.
Qed.
Theorem normalize_correct (default : U) limit c result : normalize limit c=Some result -> (valid c <-> valid result).
Proof.
  intros Accepted. split; [exact (normalize_forward limit c result Accepted)|].
  rewrite normalize_spec in Accepted. cbn zeta in Accepted.
  set (ordered:=sort_clause c) in *.
  set (vars:=first_variables (clause_variables ordered)) in *.
  destruct (length vars <=? limit); [|discriminate].
  inversion Accepted; subst result. intros Model rho. apply sort_clause_holds.
  let out := constr:(fun v : nat * nat => match nth_error vars (snd v) with Some old => rho old | None => default end) in
    specialize (Model out).
  apply sort_clause_holds, rename_clause_holds in Model.
  apply (wire_clause_support functions predicates skolem definitions ordered _ rho) in Model; [exact Model|].
  intros v Hvar. unfold local_name. assert (Present : In v vars) by (apply first_variables_members; exact Hvar).
  destruct (variable_index_present v vars Present) as [i Found]. rewrite Found; simpl.
  now rewrite (variable_index_hit v vars i Found).
Qed.
End Semantics.
Print Assumptions normalize_forward.
Print Assumptions normalize_correct.
End WireNormalize.

(* WireEncoding *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Require Import AxiomFuzzer.Clause.Kernel.
Require Import AxiomFuzzer.Wire.Syntax.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Import ListNotations.

Section Encoding.
Context {F PT : Type}.
Variable equal_function : F -> F -> bool.
Variable equal_predicate : PT -> PT -> bool.
Definition symbol_equal (x y : wire_symbol F) :=
  match x,y with
  | Original f,Original g => equal_function f g
  | Skolem a i,Skolem b j => (0 <=? a) && (0 <=? i) && variable_equal (a,i) (b,j)
  | _,_ => false
  end.
Definition predicate_equal (x y : wire_predicate PT) :=
  match x,y with
  | Named p,Named q => equal_predicate p q
  | Auxiliary i,Auxiliary j => (0 <=? fst i) && (0 <=? snd i) && variable_equal i j
  | _,_ => false
  end.
Variable encode_variable : (nat * nat) -> nat.
Variable decode_function : nat -> option (wire_symbol F).
Variable decode_predicate : nat -> option (wire_predicate PT).
Fixpoint encoded_term (t : wire_term F) (numeric : AxiomFuzzer.Clause.Kernel.term) : bool :=
  match t,numeric with
  | V v,AxiomFuzzer.Clause.Kernel.Var n => (0 <=? fst v) && (0 <=? snd v) && (0 <=? n) && (encode_variable v =? n)
  | Fn s ts,AxiomFuzzer.Clause.Kernel.Fun n args => (0 <=? n) && match decode_function n with
      | Some decoded => symbol_equal s decoded && forallb2 encoded_term ts args | None => false end
  | _,_ => false
  end.
Definition encoded_predicate p n := (0 <=? n) && match decode_predicate n with
  | Some decoded => predicate_equal p decoded | None => false end.
Definition encoded_atom (a : wire_atom F PT) numeric :=
  match a,numeric with
  | P p ts,AxiomFuzzer.Clause.Kernel.Pred n args => encoded_predicate (Named p) n && forallb2 encoded_term ts args
  | E x y,AxiomFuzzer.Clause.Kernel.Eq u v => encoded_term x u && encoded_term y v
  | D id ts,AxiomFuzzer.Clause.Kernel.Pred n args => encoded_predicate (Auxiliary id) n && forallb2 encoded_term ts args
  | _,_ => false
  end.
Definition encoded_literal (l : wire_literal F PT) (numeric : AxiomFuzzer.Clause.Kernel.literal) :=
  Bool.eqb (positive l) (fst numeric) && encoded_atom (atom l) (snd numeric).
Definition encoded_clause := forallb2 encoded_literal.
Definition encoded_inputs := forallb2 encoded_clause.

Hypothesis equal_function_sound : forall f g, equal_function f g=true -> f=g.
Hypothesis equal_predicate_sound : forall p q, equal_predicate p q=true -> p=q.
Lemma symbol_equal_sound x y : symbol_equal x y=true -> x=y.
Proof.
  destruct x,y; simpl; try discriminate.
  - intros H. apply equal_function_sound in H. now subst.
  - intros H. apply variable_equal_spec in H. inversion H. reflexivity.
Qed.
Lemma predicate_equal_sound x y : predicate_equal x y=true -> x=y.
Proof.
  destruct x,y; simpl; try discriminate.
  - intros H. apply equal_predicate_sound in H. now subst.
  - intros H. apply variable_equal_spec in H. now subst.
Qed.

Section Semantics.
Context {U : Type}.
Variable default : U.
Variable functions : F -> list U -> U.
Variable predicates : PT -> list U -> Prop.
Variable skolem : (nat * nat) -> list U -> U.
Variable definitions : (nat * nat) -> list U -> Prop.
Definition numeric_functions n args := match decode_function n with
  | Some (Original f) => functions f args
  | Some (Skolem ax id) => skolem (ax,id) args
  | None => default end.
Definition numeric_predicates n args := match decode_predicate n with
  | Some (Named p) => predicates p args
  | Some (Auxiliary id) => definitions id args
  | None => False end.
Let pulled (rho : nat -> U) := fun v => rho (encode_variable v).

Theorem encoded_term_correct : forall t numeric rho, encoded_term t numeric=true ->
  AxiomFuzzer.Clause.Kernel.eval numeric_functions rho numeric=wire_eval functions skolem (pulled rho) t.
Proof.
  fix IH 1. intros [v|s ts] [n|n args] rho; simpl; try discriminate.
  - intros Eq. apply Nat.eqb_eq in Eq. now subst n.
  - destruct (decode_function n) as [decoded|] eqn:Decoded; [|discriminate].
    rewrite andb_true_iff. intros [Symbol Args]. apply symbol_equal_sound in Symbol; subst decoded.
    assert (Values : map (AxiomFuzzer.Clause.Kernel.eval numeric_functions rho) args=map (wire_eval functions skolem (pulled rho)) ts).
    { revert args Args. induction ts as [|t ts Hts]; intros [|a args] Args; simpl in *; try discriminate; [reflexivity|].
      apply andb_true_iff in Args as [Head Tail]. rewrite (IH t a rho Head), (Hts args Tail). reflexivity. }
    rewrite Values. unfold numeric_functions. rewrite Decoded. destruct s; reflexivity.
Qed.
Lemma encoded_arguments_correct ts args rho : forallb2 encoded_term ts args=true ->
  map (AxiomFuzzer.Clause.Kernel.eval numeric_functions rho) args=map (wire_eval functions skolem (pulled rho)) ts.
Proof.
  revert args. induction ts as [|t ts IH]; intros [|a args]; simpl; try discriminate; [reflexivity|].
  rewrite andb_true_iff. intros [Head Tail]. now rewrite (encoded_term_correct t a rho Head), (IH args Tail).
Qed.
Theorem encoded_atom_correct a numeric rho : encoded_atom a numeric=true ->
  (AxiomFuzzer.Clause.Kernel.atom_holds numeric_functions numeric_predicates rho numeric <->
    wire_atom_holds functions predicates skolem definitions (pulled rho) a).
Proof.
  destruct a as [p ts|x y|id ts], numeric as [n args|u v]; simpl; try discriminate.
  - rewrite andb_true_iff. intros [Pred Args]. unfold encoded_predicate in Pred; simpl in Pred.
    destruct (decode_predicate n) as [decoded|] eqn:Decoded; [|discriminate].
    change (predicate_equal (Named p) decoded=true) in Pred.
    apply predicate_equal_sound in Pred; subst decoded. unfold numeric_predicates. rewrite Decoded.
    now rewrite (encoded_arguments_correct ts args rho Args).
  - rewrite andb_true_iff. intros [X Y]. now rewrite (encoded_term_correct x u rho X), (encoded_term_correct y v rho Y).
  - rewrite andb_true_iff. intros [Pred Args]. unfold encoded_predicate in Pred; simpl in Pred.
    destruct (decode_predicate n) as [decoded|] eqn:Decoded; [|discriminate].
    change (predicate_equal (Auxiliary id) decoded=true) in Pred.
    apply predicate_equal_sound in Pred; subst decoded. unfold numeric_predicates. rewrite Decoded.
    now rewrite (encoded_arguments_correct ts args rho Args).
Qed.
Theorem encoded_literal_correct l numeric rho : encoded_literal l numeric=true ->
  (AxiomFuzzer.Clause.Kernel.literal_holds numeric_functions numeric_predicates rho numeric <->
    wire_literal_holds functions predicates skolem definitions (pulled rho) l).
Proof.
  destruct l as [sign a], numeric as [b numeric]. unfold encoded_literal; simpl.
  rewrite andb_true_iff. intros [Sign Atom]. apply Bool.eqb_prop in Sign; subst b.
  unfold AxiomFuzzer.Clause.Kernel.literal_holds, wire_literal_holds; simpl. destruct sign; now rewrite (encoded_atom_correct a numeric rho Atom).
Qed.
Lemma numeric_clause_member rho c : AxiomFuzzer.Clause.Kernel.clause_holds numeric_functions numeric_predicates rho c <->
  AxiomFuzzer.Preprocess.NormalForms.clause_holds (AxiomFuzzer.Clause.Kernel.literal_holds numeric_functions numeric_predicates rho) c.
Proof.
  unfold AxiomFuzzer.Clause.Kernel.clause_holds. induction c as [|l c IH]; simpl; [firstorder|]. rewrite <- IH.
  split.
  - intros [k [[Eq|In] Holds]]; [subst k; now left|right; exists k; auto].
  - intros [Head|[k [In Holds]]]; [exists l|exists k]; auto.
Qed.
Theorem encoded_clause_correct c numeric rho : encoded_clause c numeric=true ->
  (AxiomFuzzer.Clause.Kernel.clause_holds numeric_functions numeric_predicates rho numeric <->
    wire_clause_holds functions predicates skolem definitions (pulled rho) c).
Proof.
  rewrite numeric_clause_member. unfold encoded_clause, wire_clause_holds.
  revert numeric. induction c as [|l c IH]; intros [|n numeric]; simpl; try discriminate; [tauto|].
  rewrite andb_true_iff. intros [Head Tail]. rewrite (encoded_literal_correct l n rho Head), (IH numeric Tail). reflexivity.
Qed.
Theorem encoded_inputs_valid inputs numeric : encoded_inputs inputs numeric=true ->
  Forall (wire_valid functions predicates skolem definitions) inputs ->
  Forall (AxiomFuzzer.Clause.Kernel.valid numeric_functions numeric_predicates) numeric.
Proof.
  unfold encoded_inputs. revert numeric. induction inputs as [|c inputs IH]; intros [|n numeric]; simpl; try discriminate.
  - intros; constructor.
  - rewrite andb_true_iff. intros [Head Tail] All. inversion All; subst. constructor.
    + intros rho. apply (encoded_clause_correct c n rho Head). auto.
    + apply IH; assumption.
Qed.
Theorem wire_check_sound inputs numeric proof :
  encoded_inputs inputs numeric=true -> AxiomFuzzer.Clause.Kernel.check numeric proof=true ->
  ~ Forall (wire_valid functions predicates skolem definitions) inputs.
Proof.
  intros Encoded Checked Model.
  apply (check_sound numeric_functions numeric_predicates numeric proof Checked default).
  now apply (encoded_inputs_valid inputs numeric Encoded).
Qed.
End Semantics.
End Encoding.
Print Assumptions wire_check_sound.

(* WireRefutation *)
From Stdlib Require Import List.
Require Import AxiomFuzzer.Wire.Syntax.
Require Import AxiomFuzzer.Clause.Kernel.
Import ListNotations.

Module WireRefutation (Order : WireOrder).
Module Normalize := WireNormalize Order.
Section Soundness.
Context {U : Type}.
Variable default : U.
Variable functions : Order.function_name -> list U -> U.
Variable predicates : Order.predicate_name -> list U -> Prop.
Variable skolem : (nat * nat) -> list U -> U.
Variable definitions : (nat * nat) -> list U -> Prop.
Variable equal_function : Order.function_name -> Order.function_name -> bool.
Variable equal_predicate : Order.predicate_name -> Order.predicate_name -> bool.
Hypothesis equal_function_sound : forall f g, equal_function f g=true -> f=g.
Hypothesis equal_predicate_sound : forall p q, equal_predicate p q=true -> p=q.
Variable encode_variable : (nat * nat) -> nat.
Variable decode_function : nat -> option (wire_symbol Order.function_name).
Variable decode_predicate : nat -> option (wire_predicate Order.predicate_name).

Theorem normalized_wire_check_sound limit original normalized numeric proof :
  Forall2 (fun c result => Normalize.normalize limit c=Some result) original normalized ->
  encoded_inputs equal_function equal_predicate encode_variable decode_function decode_predicate normalized numeric=true ->
  AxiomFuzzer.Clause.Kernel.check numeric proof=true ->
  ~ Forall (wire_valid functions predicates skolem definitions) original.
Proof.
  intros Normalized Encoded Checked Model.
  apply (wire_check_sound equal_function equal_predicate encode_variable decode_function decode_predicate
    equal_function_sound equal_predicate_sound default functions predicates skolem definitions normalized numeric proof Encoded Checked).
  clear Encoded Checked.
  revert Model. induction Normalized as [|c result original normalized Here Rest IH]; intros Model; [constructor|].
  inversion Model; subst. constructor.
  - now apply (Normalize.normalize_forward functions predicates skolem definitions limit c result Here).
  - now apply IH.
Qed.
End Soundness.
Print Assumptions normalized_wire_check_sound.
End WireRefutation.
