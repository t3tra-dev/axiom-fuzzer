(* Nnf *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Require Import AxiomFuzzer.Source.Language.
Import ListNotations.

(* Negation is restricted to atoms by construction. Empty conjunction and
   disjunction represent truth and falsity, respectively. *)
Inductive normal (F P : Type) : Type :=
| NPred : bool -> P -> list (source_term F) -> normal F P
| NEqual : bool -> source_term F -> source_term F -> normal F P
| NConj : list (normal F P) -> normal F P
| NDisj : list (normal F P) -> normal F P
| NAll : normal F P -> normal F P
| NEx : normal F P -> normal F P.
Arguments NPred {F P} _ _ _.
Arguments NEqual {F P} _ _ _.
Arguments NConj {F P} _.
Arguments NDisj {F P} _.
Arguments NAll {F P} _.
Arguments NEx {F P} _.

Section Conversion.
Context {F P : Type}.
Fixpoint nnf (positive : bool) (f : source_formula F P) : normal F P :=
  match f with
  | STop => if positive then NConj [] else NDisj []
  | SBot => if positive then NDisj [] else NConj []
  | SPred p ts => NPred positive p ts
  | SEq x y => NEqual positive x y
  | SNeg f => nnf (negb positive) f
  | SConj fs => if positive then NConj (map (nnf positive) fs) else NDisj (map (nnf positive) fs)
  | SDisj fs => if positive then NDisj (map (nnf positive) fs) else NConj (map (nnf positive) fs)
  | SAll f => if positive then NAll (nnf true f) else NEx (nnf false f)
  | SEx f => if positive then NEx (nnf true f) else NAll (nnf false f)
  end.
Fixpoint normal_scoped depth closed (f : normal F P) : bool :=
  match f with
  | NPred _ _ ts => forallb (term_scoped depth closed) ts
  | NEqual _ x y => term_scoped depth closed x && term_scoped depth closed y
  | NConj fs | NDisj fs => forallb (normal_scoped depth closed) fs
  | NAll f | NEx f => normal_scoped (S depth) closed f
  end.
Theorem nnf_scope : forall f positive depth closed,
  normal_scoped depth closed (nnf positive f) = formula_scoped depth closed f.
Proof.
  fix IH 1. intros [| |p ts|x y|f|fs|fs|f|f] positive depth closed; simpl.
  - destruct positive; reflexivity.
  - destruct positive; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IH.
  - destruct positive; simpl; induction fs; simpl; [reflexivity| |reflexivity|]; rewrite IH, IHfs; reflexivity.
  - destruct positive; simpl; induction fs; simpl; [reflexivity| |reflexivity|]; rewrite IH, IHfs; reflexivity.
  - destruct positive; simpl; apply IH.
  - destruct positive; simpl; apply IH.
Qed.
End Conversion.

Definition signed (positive : bool) (A : Prop) := if positive then A else ~ A.
Section Semantics.
Context {F P D : Type} (functions : F -> list D -> D) (predicates : P -> list D -> Prop).
Fixpoint normal_holds bound free (f : normal F P) : Prop :=
  match f with
  | NPred positive p ts => signed positive (predicates p (map (source_eval functions bound free) ts))
  | NEqual positive x y => signed positive (source_eval functions bound free x = source_eval functions bound free y)
  | NConj fs => (fix every fs := match fs with [] => True | f::fs => normal_holds bound free f /\ every fs end) fs
  | NDisj fs => (fix some fs := match fs with [] => False | f::fs => normal_holds bound free f \/ some fs end) fs
  | NAll f => forall x, normal_holds (push x bound) free f
  | NEx f => exists x, normal_holds (push x bound) free f
  end.

(* Full NNF equivalence, including ~forall -> exists~, needs classical
   semantics. Keep this premise visible in the theorem type; do not import a
   global classical axiom or change the constructive clause-checker theorem. *)
Hypothesis excluded_middle : forall A : Prop, A \/ ~ A.
Lemma double_negation (A : Prop) : ~ ~ A -> A.
Proof. destruct (excluded_middle A); tauto. Qed.
Lemma negated_conjunction (A B : Prop) : (~ A \/ ~ B) <-> ~ (A /\ B).
Proof. destruct (excluded_middle A); tauto. Qed.
Lemma negated_universal (R : D -> Prop) : ~ (forall x, R x) -> exists x, ~ R x.
Proof.
  intros H. apply double_negation. intros N. apply H. intros x.
  apply double_negation. intros Rx. apply N. exists x. exact Rx.
Qed.

Theorem nnf_correct : forall f positive bound free,
  normal_holds bound free (nnf positive f) <->
  signed positive (source_holds functions predicates bound free f).
Proof.
  fix IH 1. intros [| |p ts|x y|f|fs|fs|f|f] positive bound free; simpl.
  - destruct positive; simpl; unfold signed; tauto.
  - destruct positive; simpl; unfold signed; tauto.
  - reflexivity.
  - reflexivity.
  - rewrite IH. destruct positive; simpl; unfold signed; simpl.
    + reflexivity.
    + split; [tauto|apply double_negation].
  - destruct positive; simpl; unfold signed; simpl.
    + induction fs as [|f fs Hfs]; simpl; [tauto|]. rewrite IH, Hfs. reflexivity.
    + induction fs as [|f fs Hfs]; simpl; [tauto|]. rewrite IH, Hfs. apply negated_conjunction.
  - destruct positive; simpl; unfold signed; simpl.
    + induction fs as [|f fs Hfs]; simpl; [tauto|]. rewrite IH, Hfs. reflexivity.
    + induction fs as [|f fs Hfs]; simpl; [tauto|]. rewrite IH, Hfs. unfold signed. tauto.
  - destruct positive; simpl; unfold signed; simpl.
    + split; intros H x; apply (IH f true (push x bound) free); apply H.
    + split.
      * intros [x H] A. apply (proj1 (IH f false (push x bound) free)) in H. apply H. apply A.
      * intros H. apply negated_universal in H. destruct H as [x H]. exists x.
        apply (proj2 (IH f false (push x bound) free)). exact H.
  - destruct positive; simpl; unfold signed; simpl.
    + split; intros [x H]; exists x; apply (IH f true (push x bound) free); exact H.
    + split.
      * intros H [x A]. apply (proj1 (IH f false (push x bound) free) (H x)). exact A.
      * intros H x. apply (proj2 (IH f false (push x bound) free)). intros A. apply H. exists x. exact A.
Qed.
End Semantics.
Print Assumptions nnf_scope.
Check nnf_correct.
Print Assumptions nnf_correct.

(* Cnf *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
Scheme All for list.

(* The quantifier-free matrix is polymorphic in literals. In the OCaml kernel
   these are Wire literals, after the separately implemented Skolem pass. *)
Inductive matrix (L : Type) : Type :=
| MLiteral : L -> matrix L
| MConj : list (matrix L) -> matrix L
| MDisj : list (matrix L) -> matrix L.
Arguments MLiteral {L} _.
Arguments MConj {L} _.
Arguments MDisj {L} _.

Section Conversion.
Context {L : Type}.
Definition distribute (xs ys : list (list L)) :=
  flat_map (fun x => map (app x) ys) xs.
Fixpoint cnf (m : matrix L) : list (list L) :=
  match m with
  | MLiteral l => [[l]]
  | MConj ms => flat_map cnf ms
  | MDisj ms => fold_left (fun acc m => distribute acc (cnf m)) ms [[]]
  end.

(* Check arithmetic BEFORE allocating a cross product or concatenation. No
   potentially overflowing product is evaluated in the extracted bound check. *)
Fixpoint product_fits remaining rows width :=
  match rows with
  | 0 => true
  | S rows => (width <=? remaining) && product_fits (remaining - width) rows width
  end.
Definition bounded_distribute limit (xs ys : list (list L)) :=
  if product_fits limit (length xs) (length ys)
  then Some (distribute xs ys) else None.
Definition bounded_identity limit (xs : list (list L)) :=
  if length xs <=? limit then Some xs else None.

(* A visit may refuse work. The extracted caller uses it for cooperative
   cancellation/deadlines. Acceptance is sound for ANY Boolean callback. *)
Fixpoint bounded_cnf (visit : unit -> bool) limit (m : matrix L) : option (list (list L)) :=
  if visit tt then
    match m with
    | MLiteral l => bounded_identity limit [[l]]
    | MConj ms =>
      (fix join remaining ms := match ms with
       | [] => Some []
       | m::ms => match bounded_cnf visit limit m with
         | None => None
         | Some xs => if length xs <=? remaining then
           match join (remaining - length xs) ms with
           | None => None | Some ys => Some (xs ++ ys) end
           else None
         end
       end) limit ms
    | MDisj ms =>
      (fix join acc ms := match ms with
       | [] => bounded_identity limit acc
       | m::ms => match bounded_cnf visit limit m with
         | None => None
         | Some ys => match bounded_distribute limit acc ys with
           | None => None | Some xs => join xs ms end
         end
       end) [[]] ms
    end
  else None.

Lemma bounded_distribute_exact limit xs ys cs :
  bounded_distribute limit xs ys = Some cs -> cs = distribute xs ys.
Proof. unfold bounded_distribute. destruct (product_fits _ _ _); intros H; inversion H; reflexivity. Qed.
Lemma bounded_identity_exact limit xs cs :
  bounded_identity limit xs = Some cs -> cs = xs.
Proof. unfold bounded_identity. destruct (_ <=? _); intros H; inversion H; reflexivity. Qed.

Theorem bounded_cnf_exact : forall m visit limit cs,
  bounded_cnf visit limit m = Some cs -> cs = cnf m.
Proof.
  fix IH 1. intros [l|ms|ms] visit limit cs; cbn [bounded_cnf cnf];
    destruct (visit tt); try discriminate.
  - apply bounded_identity_exact.
  - generalize limit at 2 as remaining. revert cs.
    induction ms as [|m ms Hms]; intros cs remaining; cbn [flat_map].
    + intros H. inversion H. reflexivity.
    + destruct (bounded_cnf visit limit m) as [xs|] eqn:Hm; [|discriminate].
      destruct (length xs <=? remaining); [|discriminate].
      destruct ((fix join remaining ms := match ms with
        | [] => Some []
        | m::ms => match bounded_cnf visit limit m with
          | None => None | Some xs => if length xs <=? remaining then
            match join (remaining - length xs) ms with None => None | Some ys => Some (xs ++ ys) end else None end
        end) (remaining - length xs) ms) as [ys|] eqn:Hs; [|discriminate].
      intros H. inversion H; subst. rewrite (IH m visit limit xs Hm), (Hms ys _ Hs). reflexivity.
  - generalize ([[]] : list (list L)) as acc. revert cs.
    induction ms as [|m ms Hms]; intros cs acc; cbn [fold_left].
    + apply bounded_identity_exact.
    + destruct (bounded_cnf visit limit m) as [ys|] eqn:Hm; [|discriminate].
      destruct (bounded_distribute limit acc ys) as [xs|] eqn:Hx; [|discriminate].
      intros H. specialize (Hms cs xs H). apply bounded_distribute_exact in Hx.
      rewrite Hms, Hx, (IH m visit limit ys Hm). reflexivity.
Qed.

Lemma distribute_length xs ys : length (distribute xs ys) = length xs * length ys.
Proof. induction xs; simpl; [reflexivity|]. unfold distribute in *. simpl. rewrite length_app, length_map, IHxs. reflexivity. Qed.
Lemma product_fits_spec remaining rows width :
  product_fits remaining rows width = true <-> rows * width <= remaining.
Proof.
  revert remaining. induction rows; intros remaining; simpl; [lia|].
  rewrite andb_true_iff, Nat.leb_le, IHrows. lia.
Qed.
Lemma bounded_distribute_size limit xs ys cs :
  bounded_distribute limit xs ys = Some cs -> length cs <= limit.
Proof.
  unfold bounded_distribute. destruct (product_fits _ _ _) eqn:E; intros H; inversion H; subst.
  rewrite distribute_length. now apply product_fits_spec.
Qed.
Lemma bounded_identity_size limit xs cs :
  bounded_identity limit xs = Some cs -> length cs <= limit.
Proof. unfold bounded_identity. destruct (_ <=? _) eqn:E; intros H; inversion H; subst. now apply Nat.leb_le. Qed.

Theorem bounded_cnf_size : forall m visit limit cs,
  bounded_cnf visit limit m = Some cs -> length cs <= limit.
Proof.
  intros [l|ms|ms] visit limit cs; cbn [bounded_cnf]; destruct (visit tt); try discriminate.
  - apply bounded_identity_size.
  - generalize limit at 2 3 as remaining. revert cs.
    induction ms as [|m ms Hms]; intros cs remaining; simpl.
    + intros H. inversion H. simpl. lia.
    + destruct (bounded_cnf visit limit m) as [xs|]; [|discriminate].
      destruct (length xs <=? remaining) eqn:E; [|discriminate].
      destruct ((fix join remaining ms := match ms with
        | [] => Some []
        | m::ms => match bounded_cnf visit limit m with
          | None => None | Some xs => if length xs <=? remaining then
            match join (remaining - length xs) ms with None => None | Some ys => Some (xs ++ ys) end else None end
        end) (remaining - length xs) ms) as [ys|] eqn:Hs; [|discriminate].
      intros H. inversion H; subst. rewrite length_app.
      specialize (Hms ys _ Hs). apply Nat.leb_le in E. lia.
  - generalize ([[]] : list (list L)) as acc. revert cs.
    induction ms as [|m ms Hms]; intros cs acc; simpl.
    + apply bounded_identity_size.
    + destruct (bounded_cnf visit limit m); [|discriminate].
      destruct (bounded_distribute limit acc l); [apply Hms|discriminate].
Qed.
End Conversion.

Section Semantics.
Context {L : Type} (literal_holds : L -> Prop).
Fixpoint clause_holds (c : list L) : Prop :=
  match c with [] => False | l::c => literal_holds l \/ clause_holds c end.
Fixpoint clauses_hold (cs : list (list L)) : Prop :=
  match cs with [] => True | c::cs => clause_holds c /\ clauses_hold cs end.
Fixpoint matrix_holds (m : matrix L) : Prop :=
  match m with
  | MLiteral l => literal_holds l
  | MConj ms => (fix every ms := match ms with [] => True | m::ms => matrix_holds m /\ every ms end) ms
  | MDisj ms => (fix some ms := match ms with [] => False | m::ms => matrix_holds m \/ some ms end) ms
  end.
Lemma clause_append xs ys : clause_holds (xs ++ ys) <-> clause_holds xs \/ clause_holds ys.
Proof. induction xs; simpl; [tauto|]. rewrite IHxs. tauto. Qed.
Lemma clauses_append xs ys : clauses_hold (xs ++ ys) <-> clauses_hold xs /\ clauses_hold ys.
Proof. induction xs; simpl; [tauto|]. rewrite IHxs. tauto. Qed.
Lemma clauses_map_append xs ys : clauses_hold (map (app xs) ys) <-> clause_holds xs \/ clauses_hold ys.
Proof. induction ys; simpl; [tauto|]. rewrite clause_append, IHys. tauto. Qed.
Theorem distribute_correct xs ys : clauses_hold (distribute xs ys) <-> clauses_hold xs \/ clauses_hold ys.
Proof. induction xs; simpl; [tauto|]. unfold distribute in *. simpl. rewrite clauses_append, clauses_map_append, IHxs. tauto. Qed.
Theorem cnf_correct : forall m, clauses_hold (cnf m) <-> matrix_holds m.
Proof.
  fix IH 1. intros [l|ms|ms]; simpl.
  - tauto.
  - induction ms as [|m ms Hms]; simpl; [tauto|]. rewrite clauses_append, IH, Hms. reflexivity.
  - assert (H : forall acc,
      clauses_hold (fold_left (fun acc m => distribute acc (cnf m)) ms acc) <->
      clauses_hold acc \/ matrix_holds (MDisj ms)).
    { induction ms as [|m ms Hms]; intros acc; simpl; [tauto|].
      rewrite Hms, distribute_correct, IH. simpl. tauto. }
    specialize (H [[]]). simpl in H. tauto.
Qed.
Corollary bounded_cnf_correct m visit limit cs :
  bounded_cnf visit limit m = Some cs -> (clauses_hold cs <-> matrix_holds m).
Proof. intros H. apply bounded_cnf_exact in H. rewrite H. apply cnf_correct. Qed.
End Semantics.
Print Assumptions cnf_correct.
Print Assumptions bounded_cnf_correct.
Print Assumptions bounded_cnf_size.

(* Tseitin *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Require Import AxiomFuzzer.Source.Language.
Import ListNotations.

Inductive definition_literal (A : Type) :=
| DBase : bool -> A -> definition_literal A
| DAux : bool -> nat -> list nat -> definition_literal A.
Arguments DBase {A} _ _.
Arguments DAux {A} _ _ _.
Record definition (A : Type) := {
  conjunction : bool;
  arguments : list nat;
  children : list (definition_literal A)
}.
Arguments conjunction {A} _.
Arguments arguments {A} _.
Arguments children {A} _.

Section Construction.
Context {A : Type}.
Definition opposite (l : definition_literal A) :=
  match l with DBase b a => DBase (negb b) a | DAux b id vs => DAux (negb b) id vs end.
Definition definition_root id (d : definition A) : definition_literal A := DAux true id (arguments d).
Definition definition_clauses id (d : definition A) :=
  let root := definition_root id d in
  if conjunction d then
    map (fun child => [opposite root;child]) (children d) ++ [root::map opposite (children d)]
  else [opposite root::children d] ++ map (fun child => [root;opposite child]) (children d).
Lemma definition_clauses_length id (d : definition A) :
  length (definition_clauses id d) = S (length (children d)).
Proof. unfold definition_clauses. destruct (conjunction d); rewrite length_app, length_map; simpl; lia. Qed.
Definition literal_variables (support : A -> list nat) (l : definition_literal A) :=
  match l with DBase _ a => support a | DAux _ _ vs => vs end.
Definition definition_variables support (ls : list (definition_literal A)) :=
  sort_handles (flat_map (literal_variables support) ls).
Definition literal_before limit (l : definition_literal A) :=
  match l with DBase _ _ => true | DAux _ id _ => negb (limit <=? id) end.
Definition definition_valid support id (d : definition A) :=
  forallb (literal_before id) (children d) &&
  forallb (fun v => existsb (Nat.eqb v) (arguments d)) (flat_map (literal_variables support) (children d)).
End Construction.

Fixpoint forallb2 {X Y : Type} (test : X -> Y -> bool) xs ys :=
  match xs,ys with
  | [],[] => true | x::xs,y::ys => test x y && forallb2 test xs ys | _,_ => false
  end.
Lemma forallb2_nat xs ys : forallb2 Nat.eqb xs ys = true -> xs=ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl; try discriminate; [auto|].
  rewrite andb_true_iff, Nat.eqb_eq. intros [E H]. subst. f_equal. now apply IH.
Qed.

Section Circuit.
Context {A : Type}.
Variable lookup : nat -> option (definition A).
Fixpoint valid_prefix support size :=
  match size with
  | 0 => true
  | S size => valid_prefix support size &&
      match lookup size with Some d => definition_valid support size d | None => false end
  end.
Lemma valid_prefix_entry support size : valid_prefix support size = true ->
  forall id, id < size -> exists d, lookup id=Some d /\ definition_valid support id d=true.
Proof.
  induction size; simpl; [lia|]. rewrite andb_true_iff. intros [Old Here] id Bound.
  destruct (Nat.eq_dec id size); subst.
  - destruct (lookup size) as [d|] eqn:E; [exists d;auto|discriminate].
  - apply IHsize; [assumption|lia].
Qed.
Definition match_connective expected (check_children : list (definition_literal A) -> bool) size (root : definition_literal A) :=
  match root with
  | DAux true id vars =>
    negb (size <=? id) &&
    match lookup id with
    | Some d => Bool.eqb expected (conjunction d) && forallb2 Nat.eqb vars (arguments d) && check_children (children d)
    | None => false
    end
  | _ => false
  end.
Fixpoint matches_matrix (equal : A -> A -> bool) size (m : matrix (bool * A)) root :=
  match m with
  | MLiteral (sign,atom) => match root with DBase other b => Bool.eqb sign other && equal atom b | _ => false end
  | MConj ms => match_connective true (forallb2 (matches_matrix equal size) ms) size root
  | MDisj ms => match_connective false (forallb2 (matches_matrix equal size) ms) size root
  end.

Fixpoint emit_definitions (visit : unit -> bool) count first budget : option (list (list (definition_literal A))) :=
  if visit tt then
    match count with
    | 0 => Some []
    | S count => match lookup first with
      | None => None
      | Some d => if negb (budget <=? length (children d)) then
          let cs := definition_clauses first d in
          match emit_definitions visit count (S first) (budget-length cs) with
          | Some rest => Some (cs ++ rest) | None => None end
        else None
      end
    end
  else None.
Definition checked_definitions visit equal support size budget m root :=
  if visit tt && valid_prefix support size && matches_matrix equal size m root && (1 <=? budget) then
    match emit_definitions visit size 0 (budget-1) with
    | Some cs => Some (cs ++ [[root]]) | None => None end
  else None.
End Circuit.

Section Semantics.
Context {A D : Type} (base : A -> (nat -> D) -> Prop).
Definition definition_holds (aux : nat -> list D -> Prop) rho (l : definition_literal A) :=
  match l with
  | DBase b a => signed b (base a rho)
  | DAux b id vs => signed b (aux id (map rho vs))
  end.
Definition connective_holds aux rho (d : definition A) :=
  if conjunction d then Forall (definition_holds aux rho) (children d)
  else AxiomFuzzer.Preprocess.NormalForms.clause_holds (definition_holds aux rho) (children d).
Hypothesis excluded_middle : forall P : Prop, P \/ ~ P.

Lemma opposite_correct aux rho l :
  definition_holds aux rho (opposite l) <-> ~ definition_holds aux rho l.
Proof.
  destruct l as [b a|b id vs]; destruct b; simpl; unfold signed; simpl;
    try reflexivity; destruct (excluded_middle (base a rho)) || destruct (excluded_middle (aux id (map rho vs))); tauto.
Qed.
Lemma opposite_list aux rho ls :
  AxiomFuzzer.Preprocess.NormalForms.clause_holds (definition_holds aux rho) (map opposite ls) <-> ~ Forall (definition_holds aux rho) ls.
Proof.
  induction ls as [|l ls IH]; simpl.
  - rewrite Forall_nil_iff. tauto.
  - rewrite opposite_correct, IH, Forall_cons_iff.
    destruct (excluded_middle (definition_holds aux rho l)); tauto.
Qed.
Lemma forward_clauses aux rho root ls :
  AxiomFuzzer.Preprocess.NormalForms.clauses_hold (definition_holds aux rho) (map (fun child => [opposite root;child]) ls) <->
  (~ definition_holds aux rho root \/ Forall (definition_holds aux rho) ls).
Proof.
  induction ls as [|l ls IH]; simpl.
  - rewrite Forall_nil_iff. tauto.
  - rewrite opposite_correct, IH, Forall_cons_iff. tauto.
Qed.
Lemma backward_clauses aux rho root ls :
  AxiomFuzzer.Preprocess.NormalForms.clauses_hold (definition_holds aux rho) (map (fun child => [root;opposite child]) ls) <->
  (definition_holds aux rho root \/ ~ AxiomFuzzer.Preprocess.NormalForms.clause_holds (definition_holds aux rho) ls).
Proof.
  induction ls as [|l ls IH]; simpl.
  - tauto.
  - rewrite opposite_correct, IH. tauto.
Qed.
Theorem definition_clauses_correct aux rho id d :
  AxiomFuzzer.Preprocess.NormalForms.clauses_hold (definition_holds aux rho) (definition_clauses id d) <->
  (aux id (map rho (arguments d)) <-> connective_holds aux rho d).
Proof.
  unfold definition_clauses, connective_holds. destruct (conjunction d); rewrite AxiomFuzzer.Preprocess.NormalForms.clauses_append.
  - rewrite forward_clauses. simpl. rewrite opposite_list. unfold definition_root, definition_holds, signed. simpl.
    destruct (excluded_middle (aux id (map rho (arguments d))));
      destruct (excluded_middle (Forall (definition_holds aux rho) (children d))); tauto.
  - rewrite backward_clauses. simpl. unfold definition_root. simpl. unfold signed.
    destruct (excluded_middle (aux id (map rho (arguments d))));
      destruct (excluded_middle (AxiomFuzzer.Preprocess.NormalForms.clause_holds (definition_holds aux rho) (children d))); tauto.
Qed.
End Semantics.

Section MatrixCorrectness.
Context {A D : Type} (base : A -> (nat -> D) -> Prop).
Variable equal : A -> A -> bool.
Hypothesis equal_sound : forall a b, equal a b=true -> a=b.
Variable lookup : nat -> option (definition A).
Variable size : nat.
Variable aux : nat -> list D -> Prop.
Variable rho : nat -> D.
Hypothesis definitions_hold : forall id d, id<size -> lookup id=Some d ->
  (aux id (map rho (arguments d)) <-> connective_holds base aux rho d).

Theorem matches_matrix_correct : forall m root,
  matches_matrix lookup equal size m root=true ->
  (definition_holds base aux rho root <-> matrix_holds (fun l => signed (fst l) (base (snd l) rho)) m).
Proof.
  fix IH 1. intros [ [sign atom] |ms|ms] root; cbn [matches_matrix].
  - destruct root as [other b|other id vars]; [|discriminate].
    rewrite andb_true_iff, Bool.eqb_true_iff. intros [E H]. apply equal_sound in H. subst. reflexivity.
  - unfold match_connective. destruct root as [other b|[|] id vars]; try discriminate.
    rewrite andb_true_iff, negb_true_iff, Nat.leb_gt. intros [Bound H].
    destruct (lookup id) as [d|] eqn:Found; [|discriminate].
    apply andb_true_iff in H as [H Children]. apply andb_true_iff in H as [Sign Vars].
    rewrite Bool.eqb_true_iff in Sign. apply forallb2_nat in Vars. subst vars.
    change (aux id (map rho (arguments d)) <-> matrix_holds (fun l => signed (fst l) (base (snd l) rho)) (MConj ms)).
    rewrite (definitions_hold id d Bound Found). unfold connective_holds. rewrite <- Sign.
    assert (H : forall ls, forallb2 (matches_matrix lookup equal size) ms ls=true ->
      (Forall (definition_holds base aux rho) ls <-> matrix_holds (fun l => signed (fst l) (base (snd l) rho)) (MConj ms))).
    { clear Children. induction ms as [|m ms Hms]; intros [|l ls]; simpl; try discriminate.
      - intros _. rewrite Forall_nil_iff. tauto.
      - rewrite andb_true_iff. intros [Hm Hls]. rewrite Forall_cons_iff, (IH m l Hm), (Hms ls Hls). reflexivity. }
    apply H. exact Children.
  - unfold match_connective. destruct root as [other b|[|] id vars]; try discriminate.
    rewrite andb_true_iff, negb_true_iff, Nat.leb_gt. intros [Bound H].
    destruct (lookup id) as [d|] eqn:Found; [|discriminate].
    apply andb_true_iff in H as [H Children]. apply andb_true_iff in H as [Sign Vars].
    rewrite Bool.eqb_true_iff in Sign. apply forallb2_nat in Vars. subst vars.
    change (aux id (map rho (arguments d)) <-> matrix_holds (fun l => signed (fst l) (base (snd l) rho)) (MDisj ms)).
    rewrite (definitions_hold id d Bound Found). unfold connective_holds. rewrite <- Sign.
    assert (H : forall ls, forallb2 (matches_matrix lookup equal size) ms ls=true ->
      (AxiomFuzzer.Preprocess.NormalForms.clause_holds (definition_holds base aux rho) ls <-> matrix_holds (fun l => signed (fst l) (base (snd l) rho)) (MDisj ms))).
    { clear Children. induction ms as [|m ms Hms]; intros [|l ls]; simpl; try discriminate.
      - tauto.
      - rewrite andb_true_iff. intros [Hm Hls]. rewrite (IH m l Hm), (Hms ls Hls). reflexivity. }
    apply H. exact Children.
Qed.
End MatrixCorrectness.

(* Reconstruct a valuation from the argument vector of an auxiliary predicate.
   The default is needed only for variables outside its declared support. *)
Fixpoint restore_variables {D : Type} (default : D) variables values i :=
  match variables,values with
  | v::vs,x::xs => if i =? v then x else restore_variables default vs xs i
  | _,_ => default
  end.
Lemma restore_variables_correct {D : Type} (default : D) variables (rho : nat -> D) i :
  In i variables -> restore_variables default variables (map rho variables) i = rho i.
Proof.
  induction variables as [|v vs IH]; simpl; [tauto|].
  destruct (Nat.eqb_spec i v); subst; [reflexivity|]. intros [E|H]; [congruence|auto].
Qed.

Section Support.
Context {A D : Type} (base : A -> (nat -> D) -> Prop) (support : A -> list nat).
Hypothesis base_support : forall a rho other,
  (forall v, In v (support a) -> rho v = other v) -> (base a rho <-> base a other).
Lemma literal_support aux l rho other :
  (forall v, In v (literal_variables support l) -> rho v = other v) ->
  (definition_holds base aux rho l <-> definition_holds base aux other l).
Proof.
  intros Agree. destruct l as [b a|b id vs]; simpl in *.
  - destruct b; simpl; unfold signed; rewrite (base_support a rho other Agree); reflexivity.
  - assert (E : map rho vs = map other vs).
    { apply map_ext_in. intros v Hv. now apply Agree. }
    now rewrite E.
Qed.
Lemma literal_aux_agree bound aux other rho l :
  literal_before bound l = true ->
  (forall id args, id < bound -> (aux id args <-> other id args)) ->
  (definition_holds base aux rho l <-> definition_holds base other rho l).
Proof.
  intros Before Agree. destruct l as [b a|b id vs]; simpl in *; [reflexivity|].
  apply negb_true_iff, Nat.leb_gt in Before. specialize (Agree id (map rho vs) Before).
  destruct b; simpl; unfold signed; tauto.
Qed.
End Support.

Lemma Forall_equiv_in {X : Type} (P Q : X -> Prop) xs :
  (forall x, In x xs -> (P x <-> Q x)) -> (Forall P xs <-> Forall Q xs).
Proof.
  induction xs as [|x xs IH]; intros H; [rewrite !Forall_nil_iff; tauto|].
  rewrite !Forall_cons_iff, (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. now right.
Qed.
Lemma clause_equiv_in {X : Type} (P Q : X -> Prop) xs :
  (forall x, In x xs -> (P x <-> Q x)) -> (AxiomFuzzer.Preprocess.NormalForms.clause_holds P xs <-> AxiomFuzzer.Preprocess.NormalForms.clause_holds Q xs).
Proof.
  induction xs as [|x xs IH]; intros H; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. now right.
Qed.
Lemma connective_equiv {A D : Type} (base : A -> (nat -> D) -> Prop) aux other rho sigma d :
  (forall l, In l (children d) -> (definition_holds base aux rho l <-> definition_holds base other sigma l)) ->
  (connective_holds base aux rho d <-> connective_holds base other sigma d).
Proof.
  unfold connective_holds. destruct (conjunction d); [apply Forall_equiv_in|apply clause_equiv_in].
Qed.
Lemma valid_child {A : Type} support id (d : definition A) l :
  definition_valid support id d=true -> In l (children d) -> literal_before id l=true.
Proof.
  unfold definition_valid. rewrite andb_true_iff. intros [H _] Hl.
  rewrite forallb_forall in H. now apply H.
Qed.
Lemma valid_support {A : Type} support id (d : definition A) l v :
  definition_valid support id d=true -> In l (children d) ->
  In v (literal_variables support l) -> In v (arguments d).
Proof.
  unfold definition_valid. rewrite andb_true_iff. intros [_ H] Hl Hv.
  rewrite forallb_forall in H. specialize (H v).
  assert (In v (flat_map (literal_variables support) (children d))) by (apply in_flat_map; exists l; auto).
  specialize (H H0). apply existsb_exists in H as [w [Hw E]]. apply Nat.eqb_eq in E. now subst.
Qed.

Section ModelExtension.
Context {A D : Type} (base : A -> (nat -> D) -> Prop) (support : A -> list nat).
Hypothesis base_support : forall a rho other,
  (forall v, In v (support a) -> rho v=other v) -> (base a rho <-> base a other).
Variable default : D.
Variable lookup : nat -> option (definition A).

(* Each predicate is defined from strictly earlier predicates. Its arguments
   recover every variable on which its children depend. Thus this single model
   extension works simultaneously for ALL valuations of the first-order vars. *)
Fixpoint extension size : nat -> list D -> Prop :=
  match size with
  | 0 => fun _ _ => False
  | S n => fun id values => if id =? n then
      match lookup n with
      | Some d => connective_holds base (extension n) (restore_variables default (arguments d) values) d
      | None => False
      end
    else extension n id values
  end.
Lemma extension_step n id values : id<n -> (extension (S n) id values <-> extension n id values).
Proof.
  intros H. simpl. destruct (Nat.eqb_spec id n); [lia|reflexivity].
Qed.
Lemma extension_new n d rho : lookup n=Some d -> definition_valid support n d=true ->
  (extension (S n) n (map rho (arguments d)) <-> connective_holds base (extension (S n)) rho d).
Proof.
  intros Found Valid.
  transitivity (connective_holds base (extension n) (restore_variables default (arguments d) (map rho (arguments d))) d).
  { simpl. now rewrite Nat.eqb_refl, Found. }
  apply connective_equiv. intros l Hl.
  transitivity (definition_holds base (extension n) rho l).
  - apply (literal_support base support base_support). intros v Hv.
    apply restore_variables_correct. eapply valid_support; eauto.
  - apply (literal_aux_agree base n).
    + eapply valid_child; eauto.
    + intros id args Bound. symmetry. now apply extension_step.
Qed.
Theorem extension_correct size : valid_prefix lookup support size=true ->
  forall id d rho, id<size -> lookup id=Some d ->
  (extension size id (map rho (arguments d)) <-> connective_holds base (extension size) rho d).
Proof.
  induction size as [|n IH]; [lia|]. simpl. rewrite andb_true_iff.
  intros [Old Valid] id d rho Bound Found.
  destruct (Nat.eq_dec id n) as [E|E].
  - subst. apply extension_new; [assumption|]. now rewrite Found in Valid.
  - assert (Earlier : id<n) by lia.
    change (extension (S n) id (map rho (arguments d)) <-> connective_holds base (extension (S n)) rho d).
    rewrite (extension_step n id _ Earlier), (IH Old id d rho Earlier Found).
    apply connective_equiv. intros l Hl.
    destruct (valid_prefix_entry lookup support n Old id Earlier) as [d' [Hlookup Hvalid]].
    rewrite Found in Hlookup. inversion Hlookup; subst d'.
    apply (literal_aux_agree base id); [eapply valid_child; eauto|].
    intros k args Hk. symmetry. apply extension_step. lia.
Qed.
End ModelExtension.

Section OutputCorrectness.
Context {A D : Type} (base : A -> (nat -> D) -> Prop).
Hypothesis excluded_middle : forall P : Prop, P \/ ~ P.
Variable lookup : nat -> option (definition A).

Lemma emit_definitions_size count : forall visit first budget cs,
  emit_definitions lookup visit count first budget=Some cs -> length cs<=budget.
Proof.
  induction count as [|count IH]; intros visit first budget cs; simpl;
    destruct (visit tt); try discriminate.
  - intros H. inversion H; simpl; lia.
  - destruct (lookup first) as [d|]; [|discriminate].
    destruct (negb (budget <=? length (children d))) eqn:Bound; [|discriminate].
    destruct (emit_definitions lookup visit count (S first) (budget-length (definition_clauses first d))) as [rest|] eqn:Rest; [|discriminate].
    intros H. inversion H; subst. rewrite length_app.
    apply negb_true_iff, Nat.leb_gt in Bound. rewrite definition_clauses_length in *.
    specialize (IH visit (S first) _ rest Rest). lia.
Qed.
Lemma emit_definitions_correct count : forall visit first budget cs aux rho,
  emit_definitions lookup visit count first budget=Some cs ->
  (AxiomFuzzer.Preprocess.NormalForms.clauses_hold (definition_holds base aux rho) cs <->
    forall id d, first<=id -> id<first+count -> lookup id=Some d ->
      (aux id (map rho (arguments d)) <-> connective_holds base aux rho d)).
Proof.
  induction count as [|count IH]; intros visit first budget cs aux rho; simpl;
    destruct (visit tt); try discriminate.
  - intros H. inversion H; subst; simpl. split; [intros _ id d; lia|auto].
  - destruct (lookup first) as [d|] eqn:Found; [|discriminate].
    destruct (negb (budget <=? length (children d))); [|discriminate].
    destruct (emit_definitions lookup visit count (S first) (budget-length (definition_clauses first d))) as [rest|] eqn:Rest; [|discriminate].
    intros H. inversion H; subst.
    rewrite AxiomFuzzer.Preprocess.NormalForms.clauses_append, (definition_clauses_correct base excluded_middle), (IH _ _ _ rest aux rho Rest).
    split.
    + intros [Here Later] id d' Lower Upper Entry. destruct (Nat.eq_dec id first) as [E|E].
      * subst. rewrite Found in Entry. inversion Entry; subst. exact Here.
      * apply Later; try assumption; lia.
    + intros All. split.
      * apply All; try assumption; lia.
      * intros id d' Lower Upper Entry. apply All; try assumption; lia.
Qed.

Variable equal : A -> A -> bool.
Hypothesis equal_sound : forall a b, equal a b=true -> a=b.
Lemma checked_definitions_parts visit support size budget m root cs :
  checked_definitions lookup visit equal support size budget m root=Some cs ->
  valid_prefix lookup support size=true /\ matches_matrix lookup equal size m root=true /\
  1<=budget /\ exists before, emit_definitions lookup visit size 0 (budget-1)=Some before /\ cs=before++[[root]].
Proof.
  unfold checked_definitions.
  destruct (visit tt && valid_prefix lookup support size && matches_matrix lookup equal size m root && (1 <=? budget)) eqn:H; [|discriminate].
  repeat rewrite andb_true_iff in H. rewrite Nat.leb_le in H.
  destruct (emit_definitions lookup visit size 0 (budget-1)) as [before|] eqn:Before; [|discriminate].
  intros E. inversion E; subst. intuition. exists before. auto.
Qed.
Theorem checked_definitions_size visit support size budget m root cs :
  checked_definitions lookup visit equal support size budget m root=Some cs -> length cs<=budget.
Proof.
  intros Accepted. apply checked_definitions_parts in Accepted as [_ [_ [Bound [before [Emit Eq]]]]].
  rewrite Eq, length_app. simpl. pose proof (emit_definitions_size size _ _ _ before Emit). lia.
Qed.
Theorem checked_definitions_correct visit support size budget m root cs aux rho :
  checked_definitions lookup visit equal support size budget m root=Some cs ->
  (AxiomFuzzer.Preprocess.NormalForms.clauses_hold (definition_holds base aux rho) cs <->
    (forall id d, id<size -> lookup id=Some d ->
      (aux id (map rho (arguments d)) <-> connective_holds base aux rho d)) /\
    matrix_holds (fun l => signed (fst l) (base (snd l) rho)) m).
Proof.
  intros Accepted. apply checked_definitions_parts in Accepted as [_ [Match [_ [before [Emit Eq]]]]].
  rewrite Eq, AxiomFuzzer.Preprocess.NormalForms.clauses_append, (emit_definitions_correct size _ _ _ before aux rho Emit). simpl.
  split.
  - intros [Defs [[Root|F] _]]; [|contradiction].
    assert (All : forall id d, id<size -> lookup id=Some d ->
      (aux id (map rho (arguments d)) <-> connective_holds base aux rho d)) by (intros; apply Defs; auto; lia).
    split; [exact All|]. apply (matches_matrix_correct base equal equal_sound lookup size aux rho All m root Match). exact Root.
  - intros [Defs Matrix]. split; [intros; apply Defs; auto|]. split; [left|tauto].
    apply (matches_matrix_correct base equal equal_sound lookup size aux rho Defs m root Match). exact Matrix.
Qed.

Variable support : A -> list nat.
Hypothesis base_support : forall a rho other,
  (forall v, In v (support a) -> rho v=other v) -> (base a rho <-> base a other).
Variable default : D.

(* Equisatisfiability for universally closed first-order matrices: one auxiliary
   interpretation is chosen outside the quantification over valuations. *)
Theorem checked_definitions_equisat visit size budget m root cs :
  checked_definitions lookup visit equal support size budget m root=Some cs ->
  ((forall rho, matrix_holds (fun l => signed (fst l) (base (snd l) rho)) m) <->
   exists aux, forall rho, AxiomFuzzer.Preprocess.NormalForms.clauses_hold (definition_holds base aux rho) cs).
Proof.
  intros Accepted. pose proof (checked_definitions_parts _ _ _ _ _ _ _ Accepted) as [Valid _].
  split.
  - intros Matrix. exists (extension base default lookup size). intros rho.
    apply (checked_definitions_correct _ _ _ _ _ _ _ _ rho Accepted). split; [|apply Matrix].
    intros id d Bound Found. eapply (extension_correct base support base_support default lookup size Valid); eauto.
  - intros [aux Clauses] rho. specialize (Clauses rho).
    apply (checked_definitions_correct _ _ _ _ _ _ _ aux rho Accepted) in Clauses as [_ Matrix]. exact Matrix.
Qed.
End OutputCorrectness.
Print Assumptions definition_clauses_correct.
Print Assumptions extension_correct.
Print Assumptions checked_definitions_correct.
Print Assumptions checked_definitions_equisat.
Print Assumptions checked_definitions_size.
