(* WirePreprocess *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Require Import AxiomFuzzer.Preprocess.Quantifiers.
Require Import AxiomFuzzer.Preprocess.SkolemModel.
Require Import AxiomFuzzer.Wire.Syntax.
Import ListNotations.

Section Construction.
Context {F PT : Type}.
Definition wire_quantifiers visit limit ax (normal : normal F PT) :=
  eliminate_quantifiers visit (fun f ts => Fn (Original f) ts) (fun i => V (0,i))
    (fun id ts => Fn (Skolem ax id) ts)
    (fun sign p ts => (sign,P p ts)) (fun sign x y => (sign,E x y)) limit [] [] 0 0 normal.
Fixpoint wire_universal_scope (visit : unit -> bool) allowed limit next (f : universal (bool * wire_atom F PT)) :=
  match f with
  | ULiteral l => if visit tt then match checked_wire_support (snd l) with
    | Some vars => if forallb (fun v => existsb (Nat.eqb v) allowed) vars then Some next else None
    | None => None end else None
  | UConj fs | UDisj fs => scope_list (wire_universal_scope visit allowed limit) next fs
  | UAll v body => if (v =? next) && negb (limit <=? next)
    then wire_universal_scope visit (v::allowed) limit (S next) body else None
  end.
Definition wire_checked_universals visit limit f :=
  match wire_universal_scope visit [] limit 0 f with
  | Some _ => Some (erase_universals f) | None => None end.
Theorem wire_universal_scope_correct : forall f visit allowed limit next after,
  wire_universal_scope visit allowed limit next f=Some after ->
  universal_scope (fun l => wire_support (snd l)) allowed limit next f=Some after.
Proof.
  fix IH 1. intros [l|fs|fs|v f] visit allowed limit next after; cbn [wire_universal_scope universal_scope].
  - destruct (visit tt); [|discriminate].
    destruct (checked_wire_support (snd l)) as [vars|] eqn:Support; [|discriminate].
    apply checked_wire_support_correct in Support as [Eq _]. now rewrite Eq.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl; [auto|].
    destruct (wire_universal_scope visit allowed limit next f) as [middle|] eqn:First; [|discriminate].
    rewrite (IH f visit allowed limit next middle First). apply Hfs.
  - revert next after. induction fs as [|f fs Hfs]; intros next after; simpl; [auto|].
    destruct (wire_universal_scope visit allowed limit next f) as [middle|] eqn:First; [|discriminate].
    rewrite (IH f visit allowed limit next middle First). apply Hfs.
  - destruct ((v =? next) && negb (limit <=? next)); [apply IH|discriminate].
Qed.
Theorem wire_checked_universals_correct visit limit f m : wire_checked_universals visit limit f=Some m ->
  checked_universals (fun l => wire_support (snd l)) limit f=Some m.
Proof.
  unfold wire_checked_universals, checked_universals.
  destruct (wire_universal_scope visit [] limit 0 f) as [after|] eqn:Scope; [|discriminate].
  now rewrite (wire_universal_scope_correct f visit [] limit 0 after Scope).
Qed.
Definition pack_literal (l : bool * wire_atom F PT) := Build_wire_literal (fst l) (snd l).
Definition wire_distributive_cnf visit budget (m : matrix (bool * wire_atom F PT)) :=
  match bounded_cnf visit budget m with
  | Some cs => Some (map (map pack_literal) cs) | None => None end.
Definition definition_is_base (l : definition_literal (wire_atom F PT)) :=
  match l with DBase _ a => base_atom a | DAux _ _ _ => true end.
Definition wire_definition_valid (l : definition_literal (wire_atom F PT)) :=
  match l with
  | DBase _ a => wire_base_valid a
  | DAux _ id vars => (0 <=? id) && forallb (fun v => 0 <=? v) vars
  end.
Definition wire_lookup (lookup : nat -> option (definition (wire_atom F PT))) id :=
  match lookup id with
  | Some d => if forallb wire_definition_valid (children d) then Some d else None
  | None => None
  end.
(* The caller freezes its declaration array. Validate each entry once, then
   let the generic checker reuse the same pure lookup without rescanning it. *)
Fixpoint wire_definitions_valid lookup size :=
  match size with
  | 0 => true
  | S size => if wire_definitions_valid lookup size then
      match wire_lookup lookup size with Some _ => true | None => false end
    else false
  end.
Definition pack_definition ax (l : definition_literal (wire_atom F PT)) :=
  match l with
  | DBase sign a => Build_wire_literal sign a
  | DAux sign id vars => Build_wire_literal sign (D (ax,id) (map (fun i => V (0,i)) vars))
  end.
Definition wire_definitional_cnf lookup visit equal size budget ax m root :=
  if visit tt && wire_definition_valid root && wire_definitions_valid lookup size then
    match checked_definitions lookup visit equal wire_support size budget m root with
    | Some cs => Some (map (map (pack_definition ax)) cs) | None => None end
  else None.

Lemma valid_definition_base l : wire_definition_valid l=true -> definition_is_base l=true.
Proof. destruct l; simpl; [rewrite wire_base_valid_correct; tauto|auto]. Qed.
Lemma wire_lookup_base lookup id d : wire_lookup lookup id=Some d ->
  Forall (fun l => definition_is_base l=true) (children d).
Proof.
  unfold wire_lookup. destruct (lookup id) as [found|]; [|discriminate].
  destruct (forallb wire_definition_valid (children found)) eqn:Valid; [|discriminate].
  intros E. inversion E; subst. rewrite Forall_forall. intros l In. apply valid_definition_base.
  rewrite forallb_forall in Valid. now apply Valid.
Qed.
Lemma wire_definitions_entry lookup size : wire_definitions_valid lookup size=true ->
  forall id, id<size -> exists d, wire_lookup lookup id=Some d.
Proof.
  induction size as [|size IH]; simpl; [intros _ id Bound; lia|].
  destruct (wire_definitions_valid lookup size) eqn:Prefix; [|discriminate].
  destruct (wire_lookup lookup size) as [d|] eqn:Entry; [|discriminate].
  intros _ id Bound. destruct (Nat.eq_dec id size) as [Eq|Different].
  - subst id. eauto.
  - apply IH; [reflexivity|lia].
Qed.
Lemma wire_definitions_base lookup size id d : wire_definitions_valid lookup size=true -> id<size ->
  lookup id=Some d -> Forall (fun l => definition_is_base l=true) (children d).
Proof.
  intros Valid Bound Found. destruct (wire_definitions_entry lookup size Valid id Bound) as [checked Checked].
  assert (Same : checked=d).
  { unfold wire_lookup in Checked. rewrite Found in Checked. destruct (forallb _ _); inversion Checked; auto. }
  subst checked. now apply (wire_lookup_base lookup id d).
Qed.
Lemma opposite_base l : definition_is_base (opposite l)=definition_is_base l.
Proof. destruct l; reflexivity. Qed.
Lemma definition_clauses_base id d : Forall (fun l => definition_is_base l=true) (children d) ->
  Forall (Forall (fun l => definition_is_base l=true)) (definition_clauses id d).
Proof.
  intros Children. unfold definition_clauses. destruct (conjunction d); apply Forall_app; split.
  - apply Forall_map. eapply Forall_impl; [|exact Children]. intros l Base. simpl; repeat constructor; auto.
  - repeat constructor. apply Forall_map. eapply Forall_impl; [|exact Children]. intros l Base. now rewrite opposite_base.
  - repeat constructor. exact Children.
  - apply Forall_map. eapply Forall_impl; [|exact Children]. intros l Base. repeat constructor. now rewrite opposite_base.
Qed.
Lemma emit_wire_base lookup size (Valid : wire_definitions_valid lookup size=true) count : forall visit first budget cs,
  first+count<=size -> emit_definitions lookup visit count first budget=Some cs ->
  Forall (Forall (fun l => definition_is_base l=true)) cs.
Proof.
  induction count as [|count IH]; intros visit first budget cs Bound; simpl; destruct (visit tt); try discriminate.
  - intros E. inversion E; constructor.
  - destruct (lookup first) as [d|] eqn:Found; [|discriminate].
    destruct (negb (budget <=? length (children d))); [|discriminate].
    destruct (emit_definitions lookup visit count (S first) (budget-length (definition_clauses first d)))
      as [rest|] eqn:Rest; [|discriminate].
    intros E. inversion E; subst. apply Forall_app. split.
    + apply definition_clauses_base. eapply wire_definitions_base; eauto; lia.
    + eapply IH; eauto; lia.
Qed.
Lemma wire_definitional_parts lookup visit equal size budget ax m root cs :
  wire_definitional_cnf lookup visit equal size budget ax m root=Some cs ->
  exists raw, checked_definitions lookup visit equal wire_support size budget m root=Some raw /\
    cs=map (map (pack_definition ax)) raw /\ Forall (Forall (fun l => definition_is_base l=true)) raw.
Proof.
  unfold wire_definitional_cnf.
  destruct (visit tt && wire_definition_valid root && wire_definitions_valid lookup size) eqn:Guard; [|discriminate].
  repeat rewrite andb_true_iff in Guard. destruct Guard as [[_ Root] Valid].
  destruct (checked_definitions lookup visit equal wire_support size budget m root) as [raw|] eqn:Check; [|discriminate].
  intros E. inversion E; subst cs. exists raw. split; [reflexivity|]. split; [reflexivity|].
  apply checked_definitions_parts in Check as [_ [_ [_ [before [Emit Eq]]]]].
  rewrite Eq. apply Forall_app. split.
  - apply (emit_wire_base lookup size Valid size visit 0 (budget-1) before); [lia|exact Emit].
  - repeat constructor. apply valid_definition_base, Root.
Qed.
End Construction.

(* New symbols are namespaced by axiom ID. Interpretations for every other
   axiom are arbitrary and remain unchanged. *)
Definition axiom_symbols {X : Type} (old : (nat * nat) -> X) ax (fresh : nat -> X) :=
  fun id => if fst id =? ax then fresh (snd id) else old id.
Lemma axiom_symbols_here {X} (old : (nat * nat) -> X) ax fresh id : axiom_symbols old ax fresh (ax,id)=fresh id.
Proof. unfold axiom_symbols; simpl. now rewrite Nat.eqb_refl. Qed.
Lemma axiom_symbols_other {X} (old : (nat * nat) -> X) ax fresh id : fst id<>ax -> axiom_symbols old ax fresh id=old id.
Proof. intros Different. unfold axiom_symbols. apply Nat.eqb_neq in Different. now rewrite Different. Qed.

Section Semantics.
Context {F PT U : Type}.
Variable functions : F -> list U -> U.
Variable predicates : PT -> list U -> Prop.
Variable default : U.
Variable old_skolem : (nat * nat) -> list U -> U.
Variable old_definitions : (nat * nat) -> list U -> Prop.
Variable ax : nat.
Let eval sk rho := wire_eval functions (axiom_symbols old_skolem ax sk) (fun v => rho (snd v)).
Let base sk a rho := wire_atom_holds functions predicates (axiom_symbols old_skolem ax sk) old_definitions (fun v => rho (snd v)) a.
Let literal sk rho (l : bool * wire_atom F PT) := signed (fst l) (base sk (snd l) rho).
Let support (l : bool * wire_atom F PT) := wire_support (snd l).
Let holds sk definitions rho := wire_literal_holds functions predicates (axiom_symbols old_skolem ax sk) definitions (fun v => rho (snd v)).

Lemma wire_apply_law sk rho f ts : eval sk rho (Fn (Original f) ts)=functions f (map (eval sk rho) ts).
Proof. reflexivity. Qed.
Lemma wire_variable_law sk rho v : eval sk rho (V (0,v))=rho v.
Proof. reflexivity. Qed.
Lemma wire_witness_law sk rho id ts : eval sk rho (Fn (Skolem ax id) ts)=sk id (map (eval sk rho) ts).
Proof. unfold eval; simpl. now rewrite axiom_symbols_here. Qed.
Lemma wire_predicate_law sk rho sign p ts :
  literal sk rho (sign,P p ts) <-> signed sign (predicates p (map (eval sk rho) ts)).
Proof. reflexivity. Qed.
Lemma wire_equality_law sk rho sign x y : literal sk rho (sign,E x y) <-> signed sign (eval sk rho x=eval sk rho y).
Proof. reflexivity. Qed.
Lemma wire_base_support sk a rho other :
  (forall v, In v (wire_support a) -> rho v=other v) -> (base sk a rho <-> base sk a other).
Proof. apply wire_local_support. Qed.
Lemma wire_literal_support sk l rho other :
  (forall v, In v (support l) -> rho v=other v) -> (literal sk rho l <-> literal sk other l).
Proof.
  destruct l as [sign a]. intros Agree. unfold literal; simpl. destruct sign; unfold signed;
    now rewrite (wire_base_support sk a rho other Agree).
Qed.
Lemma clauses_pack sk rho cs : AxiomFuzzer.Preprocess.NormalForms.clauses_hold (literal sk rho) cs <->
  AxiomFuzzer.Preprocess.NormalForms.clauses_hold (holds sk old_definitions rho) (map (map pack_literal) cs).
Proof.
  induction cs as [|c cs IH]; simpl; [tauto|]. rewrite <- IH.
  assert (Clause : AxiomFuzzer.Preprocess.NormalForms.clause_holds (literal sk rho) c <->
    AxiomFuzzer.Preprocess.NormalForms.clause_holds (holds sk old_definitions rho) (map pack_literal c)).
  { induction c as [|[sign a] c Hc]; simpl; [tauto|].
    change (signed sign (base sk a rho) \/ AxiomFuzzer.Preprocess.NormalForms.clause_holds (literal sk rho) c <->
      holds sk old_definitions rho (Build_wire_literal sign a) \/ AxiomFuzzer.Preprocess.NormalForms.clause_holds (holds sk old_definitions rho) (map pack_literal c)).
    rewrite Hc. destruct sign; reflexivity. }
  tauto.
Qed.

Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.
Hypothesis functional_choice : forall R : list U -> U -> Prop,
  (forall args, exists x, R args x) -> exists g, forall args, R args (g args).

Theorem wire_source_matrix_equisat visit scope_visit limit source r m :
  wire_quantifiers visit limit ax (nnf true source)=Some r ->
  wire_checked_universals scope_visit limit (supplied_value r)=Some m ->
  (source_holds functions predicates (fun _ => default) (fun _ => default) source <->
   exists sk, forall rho, matrix_holds (literal sk rho) m).
Proof.
  intros Run Scope. apply wire_checked_universals_correct in Scope.
  apply (source_to_matrix_equisat functions predicates default (fun f ts => Fn (Original f) ts) (fun i => V (0,i))
    (fun id ts => Fn (Skolem ax id) ts) (fun sign p ts => (sign,P p ts)) (fun sign x y => (sign,E x y))
    eval literal wire_apply_law wire_variable_law wire_witness_law wire_predicate_law wire_equality_law
    visit limit excluded_middle functional_choice support wire_literal_support source r m Run Scope).
Qed.
Theorem wire_source_distributive_equisat visit scope_visit limit source r m cnf_visit budget cs :
  wire_quantifiers visit limit ax (nnf true source)=Some r ->
  wire_checked_universals scope_visit limit (supplied_value r)=Some m ->
  wire_distributive_cnf cnf_visit budget m=Some cs ->
  (source_holds functions predicates (fun _ => default) (fun _ => default) source <->
   exists sk, forall rho, AxiomFuzzer.Preprocess.NormalForms.clauses_hold (holds sk old_definitions rho) cs).
Proof.
  intros Run Scope. unfold wire_distributive_cnf.
  destruct (bounded_cnf cnf_visit budget m) as [raw|] eqn:CNF; [|discriminate].
  intros Accepted. inversion Accepted; subst cs.
  rewrite (wire_source_matrix_equisat visit scope_visit limit source r m Run Scope).
  split; intros [sk Model]; exists sk; intros rho.
  - apply clauses_pack. apply (bounded_cnf_correct (literal sk rho) m cnf_visit budget raw CNF), Model.
  - apply (bounded_cnf_correct (literal sk rho) m cnf_visit budget raw CNF).
    apply clauses_pack, Model.
Qed.

Lemma packed_definition_holds sk aux rho l : definition_is_base l=true ->
  (definition_holds (base sk) aux rho l <-> holds sk (axiom_symbols old_definitions ax aux) rho (pack_definition ax l)).
Proof.
  destruct l as [sign a|sign id vars]; simpl.
  - destruct a; try discriminate; intros _; destruct sign; reflexivity.
  - intros _. unfold holds, wire_literal_holds, pack_definition; simpl.
    rewrite axiom_symbols_here.
    assert (Args : map (eval sk rho) (map (fun i => V (0,i)) vars)=map rho vars).
    { rewrite map_map. reflexivity. }
    change (signed sign (aux id (map rho vars)) <->
      signed sign (aux id (map (eval sk rho) (map (fun i => V (0,i)) vars)))).
    now rewrite Args.
Qed.
Lemma packed_definition_clauses sk aux rho raw : Forall (Forall (fun l => definition_is_base l=true)) raw ->
  (AxiomFuzzer.Preprocess.NormalForms.clauses_hold (definition_holds (base sk) aux rho) raw <->
   AxiomFuzzer.Preprocess.NormalForms.clauses_hold (holds sk (axiom_symbols old_definitions ax aux) rho) (map (map (pack_definition ax)) raw)).
Proof.
  intros All. induction All as [|c cs Head Tail IH]; simpl; [tauto|]. rewrite <- IH.
  assert (Clause : AxiomFuzzer.Preprocess.NormalForms.clause_holds (definition_holds (base sk) aux rho) c <->
    AxiomFuzzer.Preprocess.NormalForms.clause_holds (holds sk (axiom_symbols old_definitions ax aux) rho) (map (pack_definition ax) c)).
  { induction Head as [|l c Base Rest HC]; simpl; [tauto|]. rewrite (packed_definition_holds sk aux rho l Base), HC. reflexivity. }
  tauto.
Qed.
Theorem wire_source_definitional_equisat visit scope_visit limit source r m lookup equal size budget root cs cnf_visit :
  (forall a b, equal a b=true -> a=b) ->
  wire_quantifiers visit limit ax (nnf true source)=Some r ->
  wire_checked_universals scope_visit limit (supplied_value r)=Some m ->
  wire_definitional_cnf lookup cnf_visit equal size budget ax m root=Some cs ->
  (source_holds functions predicates (fun _ => default) (fun _ => default) source <->
    exists sk aux, forall rho, AxiomFuzzer.Preprocess.NormalForms.clauses_hold (holds sk (axiom_symbols old_definitions ax aux) rho) cs).
Proof.
  intros Equal Run Scope Accepted. apply wire_definitional_parts in Accepted as [raw [CNF [Output Base]]]. subst cs.
  rewrite (wire_source_matrix_equisat visit scope_visit limit source r m Run Scope).
  split.
  - intros [sk Matrix].
    destruct (proj1 (checked_definitions_equisat (base sk) excluded_middle lookup equal Equal wire_support
      (wire_base_support sk) default cnf_visit size budget m root raw CNF) Matrix) as [aux Model].
    exists sk, aux. intros rho. now apply packed_definition_clauses.
  - intros [sk [aux Model]]. exists sk.
    apply (proj2 (checked_definitions_equisat (base sk) excluded_middle lookup equal Equal wire_support
      (wire_base_support sk) default cnf_visit size budget m root raw CNF)).
    exists aux. intros rho. apply (packed_definition_clauses sk aux rho raw Base), Model.
Qed.
End Semantics.
Print Assumptions wire_source_matrix_equisat.
Print Assumptions wire_source_distributive_equisat.
Print Assumptions wire_source_definitional_equisat.

(* WireLocal *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Require Import AxiomFuzzer.Preprocess.Quantifiers.
Require Import AxiomFuzzer.Wire.Syntax.
Import ListNotations.

(* The preprocessing semantics quantifies over local indices, whereas the
   clause checker uses (scope,index). A successful preprocessing pass emits
   only scope 0, including literals in unused definition declarations. *)
Section LocalSyntax.
Context {F PT : Type}.
Definition local_atom (a : wire_atom F PT) := forall v, In v (atom_variables a) -> fst v=0.
Definition local_literal (l : wire_literal F PT) := local_atom (atom l).
Definition local_clause (c : @wire_clause F PT) := Forall local_literal c.
Lemma base_valid_local a : wire_base_valid a=true -> local_atom a.
Proof.
  intros Valid. apply wire_base_valid_correct in Valid as [_ Local]. intros v In.
  specialize (Local v In). unfold local_variable in Local. apply andb_true_iff in Local.
  now apply Nat.eqb_eq, (proj1 Local).
Qed.
End LocalSyntax.

Section AllLiterals.
Context {L : Type}.
Fixpoint matrix_all (test : L -> Prop) (m : matrix L) {struct m} : Prop :=
  match m with MLiteral l => test l | MConj ms | MDisj ms => fold_right (fun m rest => matrix_all test m /\ rest) True ms end.
Fixpoint universal_all (test : L -> Prop) (q : universal L) {struct q} : Prop :=
  match q with
  | ULiteral l => test l | UConj qs | UDisj qs => fold_right (fun q rest => universal_all test q /\ rest) True qs
  | UAll _ q => universal_all test q end.
Lemma erase_universals_all : forall q test,
  universal_all test q -> matrix_all test (erase_universals q).
Proof.
  fix IH 1. intros [l|qs|qs|v q] test; simpl; try tauto.
  - induction qs as [|q qs Hqs]; simpl; [tauto|]. intros [Head Tail]. split; [now apply IH|now apply Hqs].
  - induction qs as [|q qs Hqs]; simpl; [tauto|]. intros [Head Tail]. split; [now apply IH|now apply Hqs].
  - apply IH.
Qed.
Lemma distribute_all (test : L -> Prop) xs ys : Forall (Forall test) xs -> Forall (Forall test) ys ->
  Forall (Forall test) (distribute xs ys).
Proof.
  intros X Y. unfold distribute. induction X; simpl; [constructor|].
  apply Forall_app; split; [|exact IHX]. apply Forall_map.
  eapply Forall_impl; [|exact Y]. intros c Hc. apply Forall_app; auto.
Qed.
Theorem cnf_all : forall m test, matrix_all test m -> Forall (Forall test) (cnf m).
Proof.
  fix IH 1. intros [l|ms|ms] test; simpl.
  - intros H. repeat constructor; exact H.
  - induction ms as [|m ms Hms]; simpl; [intros; constructor|].
    intros [Head Tail]. apply Forall_app; split; [now apply IH|now apply Hms].
  - assert (Fold : forall acc, fold_right (fun m rest => matrix_all test m /\ rest) True ms -> Forall (Forall test) acc ->
      Forall (Forall test) (fold_left (fun acc m => distribute acc (cnf m)) ms acc)).
    { induction ms as [|m ms Hms]; intros acc All Good; simpl in *; [exact Good|].
      destruct All as [Head Tail]. apply Hms; [exact Tail|]. apply distribute_all; [exact Good|now apply IH]. }
    intros All; apply Fold; [exact All|repeat constructor].
Qed.
End AllLiterals.

Section OutputLocal.
Context {F PT : Type}.
Lemma wire_scope_local : forall (q : universal (bool * wire_atom F PT)) visit allowed limit next after,
  wire_universal_scope visit allowed limit next q=Some after ->
  universal_all (fun l => local_atom (snd l)) q.
Proof.
  fix IH 1. intros [l|qs|qs|v q] visit allowed limit next after; cbn [wire_universal_scope universal_all].
  - destruct (visit tt); [|discriminate].
    destruct (checked_wire_support (snd l)) as [vars|] eqn:Support; [|discriminate].
    intros _. apply checked_wire_support_correct in Support as [_ [_ Local]]. exact Local.
  - revert next after. induction qs as [|q qs Hqs]; intros next after; simpl; [auto|].
    destruct (wire_universal_scope visit allowed limit next q) as [middle|] eqn:First; [|discriminate].
    intros Rest; split; [eapply IH; exact First|eapply Hqs; exact Rest].
  - revert next after. induction qs as [|q qs Hqs]; intros next after; simpl; [auto|].
    destruct (wire_universal_scope visit allowed limit next q) as [middle|] eqn:First; [|discriminate].
    intros Rest; split; [eapply IH; exact First|eapply Hqs; exact Rest].
  - destruct ((v =? next) && negb (limit <=? next)); [apply IH|discriminate].
Qed.
Theorem wire_matrix_local visit limit q m : wire_checked_universals visit limit q=Some m ->
  matrix_all (fun l : bool * wire_atom F PT => local_atom (snd l)) m.
Proof.
  unfold wire_checked_universals. destruct (wire_universal_scope visit [] limit 0 q) as [after|] eqn:Scope; [|discriminate].
  intros E; inversion E; subst m. apply erase_universals_all. eapply wire_scope_local; exact Scope.
Qed.
Theorem wire_distributive_local visit budget (m : matrix (bool * wire_atom F PT)) cs :
  matrix_all (fun l => local_atom (snd l)) m -> wire_distributive_cnf visit budget m=Some cs ->
  Forall local_clause cs.
Proof.
  intros Local. unfold wire_distributive_cnf. destruct (bounded_cnf visit budget m) as [raw|] eqn:CNF; [|discriminate].
  intros E; inversion E; subst cs. apply bounded_cnf_exact in CNF; subst raw.
  apply Forall_map. eapply Forall_impl; [|apply cnf_all; exact Local]. intros c Hc.
  unfold local_clause. apply Forall_map. eapply Forall_impl; [|exact Hc]. intros [sign a] H; exact H.
Qed.

Definition local_definition (l : definition_literal (wire_atom F PT)) :=
  match l with DBase _ a => local_atom a | DAux _ _ _ => True end.
Lemma valid_definition_local l : wire_definition_valid l=true -> local_definition l.
Proof. destruct l; simpl; [apply base_valid_local|auto]. Qed.
Lemma opposite_local l : local_definition (opposite l) <-> local_definition l.
Proof. destruct l; reflexivity. Qed.
Lemma definition_clauses_local id (d : definition (wire_atom F PT)) :
  Forall local_definition (children d) -> Forall (Forall local_definition) (definition_clauses id d).
Proof.
  intros Children. unfold definition_clauses. destruct (conjunction d); apply Forall_app; split.
  - apply Forall_map. eapply Forall_impl; [|exact Children]. intros l H; repeat constructor; auto.
  - repeat constructor. apply Forall_map. eapply Forall_impl; [|exact Children]. intros l H; now apply opposite_local.
  - repeat constructor. exact Children.
  - apply Forall_map. eapply Forall_impl; [|exact Children]. intros l H; repeat constructor. now apply opposite_local.
Qed.
Lemma definitions_local lookup size id d : wire_definitions_valid lookup size=true -> id<size ->
  lookup id=Some d -> Forall local_definition (children d).
Proof.
  intros Valid Bound Found. destruct (wire_definitions_entry lookup size Valid id Bound) as [checked Checked].
  unfold wire_lookup in Checked. rewrite Found in Checked.
  destruct (forallb wire_definition_valid (children d)) eqn:Children; [|discriminate].
  rewrite forallb_forall in Children. apply Forall_forall; intros l In. now apply valid_definition_local, Children.
Qed.
Lemma emit_definitions_local lookup size count : wire_definitions_valid lookup size=true ->
  forall visit first budget cs, first+count<=size -> emit_definitions lookup visit count first budget=Some cs ->
  Forall (Forall local_definition) cs.
Proof.
  intros Valid. induction count as [|count IH]; intros visit first budget cs Bound; simpl; destruct (visit tt); try discriminate.
  - intros E; inversion E; constructor.
  - destruct (lookup first) as [d|] eqn:Found; [|discriminate].
    destruct (negb (budget <=? length (children d))); [|discriminate].
    destruct (emit_definitions lookup visit count (S first) (budget-length (definition_clauses first d))) as [rest|] eqn:Rest; [|discriminate].
    intros E; inversion E; subst cs. apply Forall_app; split.
    + apply definition_clauses_local. eapply definitions_local; eauto; lia.
    + eapply IH; eauto; lia.
Qed.
Lemma pack_definition_local ax l : local_definition l -> local_literal (pack_definition ax l).
Proof.
  destruct l as [sign a|sign id vars]; simpl; [auto|]. intros _.
  intros v In. simpl in In. apply in_flat_map in In as [t [Ht Hv]].
  apply in_map_iff in Ht as [i [Eq _]]; subst t. simpl in Hv. destruct Hv as [Eq|Absent]; [now subst v|contradiction].
Qed.
Theorem wire_definitional_local lookup visit equal size budget ax (m : matrix (bool * wire_atom F PT)) root cs :
  wire_definitional_cnf lookup visit equal size budget ax m root=Some cs -> Forall local_clause cs.
Proof.
  unfold wire_definitional_cnf.
  destruct (visit tt && wire_definition_valid root && wire_definitions_valid lookup size) eqn:Guard; [|discriminate].
  repeat rewrite andb_true_iff in Guard. destruct Guard as [[_ Root] Valid].
  destruct (checked_definitions lookup visit equal wire_support size budget m root) as [raw|] eqn:CNF; [|discriminate].
  intros E; inversion E; subst cs. apply checked_definitions_parts in CNF as [_ [_ [_ [before [Emit Eq]]]]].
  assert (Local : Forall (Forall local_definition) raw).
  { rewrite Eq. apply Forall_app; split.
    - eapply emit_definitions_local; eauto; lia.
    - repeat constructor. now apply valid_definition_local. }
  apply Forall_map. eapply Forall_impl; [|exact Local]. intros c Hc. unfold local_clause. apply Forall_map.
  eapply Forall_impl; [|exact Hc]. intros l H; now apply pack_definition_local.
Qed.
End OutputLocal.

Section LocalSemantics.
Context {F PT U : Type}.
Variable functions : F -> list U -> U.
Variable predicates : PT -> list U -> Prop.
Variable skolem : (nat * nat) -> list U -> U.
Variable definitions : (nat * nat) -> list U -> Prop.
Let holds := wire_literal_holds functions predicates skolem definitions.
Lemma local_literal_holds l rho : local_literal l ->
  (holds rho l <-> holds (fun v => rho (0,snd v)) l).
Proof.
  intros Local. apply wire_literal_support. intros [scope i] In. simpl.
  assert (scope=0) by (apply (Local (scope,i)); exact In). now subst scope.
Qed.
Lemma local_clause_holds c rho : local_clause c ->
  (wire_clause_holds functions predicates skolem definitions rho c <->
   wire_clause_holds functions predicates skolem definitions (fun v => rho (0,snd v)) c).
Proof.
  intros Local. induction Local as [|l c Head Tail IH]; simpl; [reflexivity|].
  change (holds rho l \/ wire_clause_holds functions predicates skolem definitions rho c <->
    holds (fun v => rho (0,snd v)) l \/
    wire_clause_holds functions predicates skolem definitions (fun v => rho (0,snd v)) c).
  now rewrite (local_literal_holds l rho Head), IH.
Qed.
Lemma clauses_hold_forall rho cs : AxiomFuzzer.Preprocess.NormalForms.clauses_hold (holds rho) cs <->
  Forall (wire_clause_holds functions predicates skolem definitions rho) cs.
Proof. induction cs; simpl; [split; constructor|]. rewrite IHcs, Forall_cons_iff. reflexivity. Qed.
Theorem local_clauses_model cs : Forall local_clause cs ->
  ((forall rho : nat -> U, AxiomFuzzer.Preprocess.NormalForms.clauses_hold (holds (fun v => rho (snd v))) cs) <->
   Forall (wire_valid functions predicates skolem definitions) cs).
Proof.
  intros Local. split.
  - intros Model. rewrite Forall_forall in Local |- *. intros c In rho.
    apply (local_clause_holds c rho (Local c In)).
    specialize (Model (fun i => rho (0,i))). apply clauses_hold_forall in Model.
    rewrite Forall_forall in Model. exact (Model c In).
  - intros Model rho. apply clauses_hold_forall. rewrite Forall_forall in Model |- *.
    intros c In. apply (Model c In).
Qed.
End LocalSemantics.
Print Assumptions wire_matrix_local.
Print Assumptions wire_distributive_local.
Print Assumptions wire_definitional_local.
Print Assumptions local_clauses_model.

(* WireNamespaces *)
From Stdlib Require Import List Bool Arith.PeanoNat.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Require Import AxiomFuzzer.Preprocess.Quantifiers.
Require Import AxiomFuzzer.Wire.Syntax.
Import ListNotations.

Section Ownership.
Context {F PT : Type}.
Fixpoint owned_term ax (t : wire_term F) : Prop :=
  match t with
  | V _ => True
  | Fn symbol ts => (match symbol with Original _ => True | Skolem owner _ => owner=ax end) /\
      fold_right (fun t rest => owned_term ax t /\ rest) True ts
  end.
Definition owned_base ax (a : wire_atom F PT) : Prop :=
  match a with P _ ts => Forall (owned_term ax) ts | E x y => owned_term ax x /\ owned_term ax y | D _ _ => False end.
Lemma owned_apply ax f ts : Forall (owned_term ax) ts -> owned_term ax (Fn (Original f) ts).
Proof. simpl; rewrite <- Forall_fold_right; tauto. Qed.
Lemma owned_witness ax id ts : Forall (owned_term ax) ts -> owned_term ax (Fn (Skolem ax id) ts).
Proof. simpl; rewrite <- Forall_fold_right; tauto. Qed.

Lemma instantiate_owned ax visit : forall t env result,
  Forall (owned_term ax) env -> instantiate_bound visit (fun f ts => Fn (Original f) ts) env t=Some result ->
  owned_term ax result.
Proof.
  fix IH 1. intros [i|i|f ts] env result Env; cbn [instantiate_bound]; destruct (visit tt); try discriminate.
  - intros Found. rewrite Forall_forall in Env. apply Env. now apply nth_error_In in Found.
  - destruct (map_option (instantiate_bound visit (fun f ts => Fn (Original f) ts) env) ts) as [args|] eqn:Args; [|discriminate].
    intros E; inversion E; subst result. apply owned_apply. clear E.
    revert args Args. induction ts as [|t ts Hts]; intros args; simpl.
    + intros E; inversion E; constructor.
    + destruct (instantiate_bound visit (fun f ts => Fn (Original f) ts) env t) as [first|] eqn:First; [|discriminate].
      destruct (map_option (instantiate_bound visit (fun f ts => Fn (Original f) ts) env) ts) as [rest|] eqn:Rest; [|discriminate].
      intros E; inversion E; subst args. constructor; [eapply IH; eauto|now apply Hts].
Qed.
Lemma instantiate_arguments_owned ax visit env ts args : Forall (owned_term ax) env ->
  map_option (instantiate_bound visit (fun f ts => Fn (Original f) ts) env) ts=Some args -> Forall (owned_term ax) args.
Proof.
  intros Env. revert args. induction ts as [|t ts IH]; intros args; simpl.
  - intros E; inversion E; constructor.
  - destruct (instantiate_bound visit (fun f ts => Fn (Original f) ts) env t) as [first|] eqn:First; [|discriminate].
    destruct (map_option (instantiate_bound visit (fun f ts => Fn (Original f) ts) env) ts) as [rest|] eqn:Rest; [|discriminate].
    intros E; inversion E; subst args. constructor; [eapply instantiate_owned; eauto|now apply IH].
Qed.

Lemma quantifier_trace_owned ax visit limit :
  (forall env us v s f q v' s', quantifier_trace visit (fun f ts => Fn (Original f) ts) (fun i => V (0,i))
    (fun id ts => Fn (Skolem ax id) ts) (fun sign p ts => (sign,P p ts)) (fun sign x y => (sign,E x y))
    limit env us v s f q v' s' ->
    Forall (owned_term ax) env -> Forall (owned_term ax) us -> universal_all (fun l => owned_base ax (snd l)) q) /\
  (forall env us v s fs qs v' s', quantifier_traces visit (fun f ts => Fn (Original f) ts) (fun i => V (0,i))
    (fun id ts => Fn (Skolem ax id) ts) (fun sign p ts => (sign,P p ts)) (fun sign x y => (sign,E x y))
    limit env us v s fs qs v' s' ->
    Forall (owned_term ax) env -> Forall (owned_term ax) us -> Forall (universal_all (fun l => owned_base ax (snd l))) qs).
Proof.
  apply traces_mutind; simpl.
  - intros env us v s sign p ts args Inst Env Us.
    exact (instantiate_arguments_owned ax visit env ts args Env Inst).
  - intros env us v s sign x y a b X Y Env Us. split.
    + exact (instantiate_owned ax visit x env a Env X).
    + exact (instantiate_owned ax visit y env b Env Y).
  - intros env us v s fs qs v' s' Run IH Env Us. rewrite <- Forall_fold_right; now apply IH.
  - intros env us v s fs qs v' s' Run IH Env Us. rewrite <- Forall_fold_right; now apply IH.
  - intros env us v s f q v' s' Bound Run IH Env Us. apply IH.
    + constructor; [exact I|exact Env].
    + apply Forall_app; split; [exact Us|repeat constructor].
  - intros env us v s f q v' s' Bound Run IH Env Us. apply IH; [|exact Us].
    constructor; [now apply owned_witness|exact Env].
  - intros; constructor.
  - intros env us v s f fs q qs mid_v mid_s v' s' First IHfirst Rest IHrest Env Us.
    constructor; [now apply IHfirst|now apply IHrest].
Qed.
Theorem wire_matrix_owned ax visit scope_visit limit normal r m :
  wire_quantifiers visit limit ax normal=Some r -> wire_checked_universals scope_visit limit (supplied_value r)=Some m ->
  matrix_all (fun l => owned_base ax (snd l)) m.
Proof.
  unfold wire_quantifiers. intros Run Scope. apply eliminate_quantifiers_trace in Run.
  pose proof (proj1 (quantifier_trace_owned ax visit limit) _ _ _ _ _ _ _ _ Run (Forall_nil _) (Forall_nil _)) as Owned.
  unfold wire_checked_universals in Scope.
  destruct (wire_universal_scope scope_visit [] limit 0 (supplied_value r)); [|discriminate].
  inversion Scope; subst m. now apply erase_universals_all.
Qed.

Definition auxiliary_at ax (l : wire_literal F PT) :=
  match atom l with D id _ => fst id=ax | _ => True end.
Lemma owned_base_is_base ax a : owned_base ax a -> base_atom a=true.
Proof. destruct a; simpl; tauto. Qed.
Lemma packed_base_auxiliary ax l : definition_is_base l=true -> auxiliary_at ax (pack_definition ax l).
Proof. destruct l as [sign a|sign id vars]; unfold auxiliary_at; [destruct a|]; simpl; try tauto; discriminate. Qed.
Theorem definitional_auxiliary_at lookup visit equal size budget ax (m : matrix (bool * wire_atom F PT)) root cs :
  wire_definitional_cnf lookup visit equal size budget ax m root=Some cs -> Forall (Forall (auxiliary_at ax)) cs.
Proof.
  intros CNF. apply wire_definitional_parts in CNF as [raw [_ [Output All]]]; subst cs.
  apply Forall_map. eapply Forall_impl; [|exact All]. intros c Hc. apply Forall_map.
  eapply Forall_impl; [|exact Hc]. intros l H; now apply packed_base_auxiliary.
Qed.
Theorem distributive_auxiliary_at ax visit budget (m : matrix (bool * wire_atom F PT)) cs :
  matrix_all (fun l => owned_base ax (snd l)) m -> wire_distributive_cnf visit budget m=Some cs ->
  Forall (Forall (auxiliary_at ax)) cs.
Proof.
  intros Owned. unfold wire_distributive_cnf. destruct (bounded_cnf visit budget m) as [raw|] eqn:CNF; [|discriminate].
  intros E; inversion E; subst cs. apply bounded_cnf_exact in CNF; subst raw.
  apply Forall_map. eapply Forall_impl; [|apply cnf_all; exact Owned]. intros c Hc. apply Forall_map.
  eapply Forall_impl; [|exact Hc]. intros [sign a] H. unfold auxiliary_at. destruct a; simpl in *; tauto.
Qed.
End Ownership.

Section MatrixAgreement.
Context {L : Type}.
Lemma matrix_all_impl : forall (m : matrix L) P Q, (forall l, P l -> Q l) -> matrix_all P m -> matrix_all Q m.
Proof.
  fix IH 1. intros [l|ms|ms] P Q Imp; simpl; [apply Imp| |];
    induction ms as [|m ms Hms]; simpl; [tauto| |tauto|]; intros [Head Tail];
    split; [eapply IH; eauto|now apply Hms|eapply IH; eauto|now apply Hms].
Qed.
Lemma matrix_holds_agree : forall (m : matrix L) P Q,
  matrix_all (fun l => P l <-> Q l) m -> (matrix_holds P m <-> matrix_holds Q m).
Proof.
  fix IH 1. intros [l|ms|ms] P Q; simpl; [tauto| |];
    induction ms as [|m ms Hms]; simpl; [tauto| |tauto|]; intros [Head Tail];
    rewrite (IH m P Q Head), (Hms Tail); reflexivity.
Qed.
End MatrixAgreement.

Section ModelAgreement.
Context {F PT U : Type}.
Variable functions : F -> list U -> U.
Variable predicates : PT -> list U -> Prop.
Lemma owned_term_eval ax : forall t sk other rho,
  owned_term ax t -> (forall id args, sk (ax,id) args=other (ax,id) args) ->
  wire_eval functions sk rho t=wire_eval functions other rho t.
Proof.
  fix IH 1. intros [v|symbol ts] sk other rho Owned Agree; simpl; [reflexivity|].
  destruct Owned as [Symbol Args].
  assert (Values : map (wire_eval functions sk rho) ts=map (wire_eval functions other rho) ts).
  { induction ts as [|t ts Hts]; simpl in *; [reflexivity|]. destruct Args as [Head Tail].
    now rewrite (IH t sk other rho Head Agree), (Hts Tail). }
  destruct symbol as [f|owner id]; simpl in *; [now rewrite Values|]. subst owner.
  rewrite Values. apply Agree.
Qed.
Lemma owned_base_holds ax a sk other defs other_defs rho : owned_base ax a ->
  (forall id args, sk (ax,id) args=other (ax,id) args) ->
  (wire_atom_holds functions predicates sk defs rho a <-> wire_atom_holds functions predicates other other_defs rho a).
Proof.
  destruct a as [p ts|x y|id ts]; simpl; intros Owned Agree; [| |contradiction].
  - assert (Args : map (wire_eval functions sk rho) ts=map (wire_eval functions other rho) ts).
    { induction Owned; simpl; [reflexivity|]. now rewrite (owned_term_eval ax x sk other rho H Agree), IHOwned. }
    now rewrite Args.
  - destruct Owned as [X Y]. now rewrite (owned_term_eval ax x sk other rho X Agree), (owned_term_eval ax y sk other rho Y Agree).
Qed.
Definition wire_matrix_holds sk defs rho (m : matrix (bool * wire_atom F PT)) :=
  matrix_holds (fun l => signed (fst l) (wire_atom_holds functions predicates sk defs rho (snd l))) m.
Theorem owned_matrix_holds ax m sk other defs other_defs rho : matrix_all (fun l => owned_base ax (snd l)) m ->
  (forall id args, sk (ax,id) args=other (ax,id) args) ->
  (wire_matrix_holds sk defs rho m <-> wire_matrix_holds other other_defs rho m).
Proof.
  intros Owned Agree. apply matrix_holds_agree. eapply matrix_all_impl; [|exact Owned].
  intros [sign a] H; simpl. destruct sign; unfold signed; now rewrite (owned_base_holds ax a sk other defs other_defs rho H Agree).
Qed.
Theorem auxiliary_valid_agree ax c sk defs other : Forall (auxiliary_at ax) c ->
  (forall id args, defs (ax,id) args <-> other (ax,id) args) ->
  (wire_valid functions predicates sk defs c <-> wire_valid functions predicates sk other c).
Proof.
  intros Owned Agree. assert (Clause : forall rho,
    wire_clause_holds functions predicates sk defs rho c <-> wire_clause_holds functions predicates sk other rho c).
  { intros rho. apply clause_equiv_in. intros [sign a] In.
    rewrite Forall_forall in Owned. specialize (Owned (Build_wire_literal sign a) In).
    unfold auxiliary_at in Owned; simpl in Owned.
    unfold wire_literal_holds; simpl. destruct a as [p ts|x y|[owner id] ts]; simpl in *; try reflexivity.
    subst owner. destruct sign; now rewrite Agree. }
  split; intros Model rho; apply Clause, Model.
Qed.
End ModelAgreement.
Print Assumptions wire_matrix_owned.
Print Assumptions definitional_auxiliary_at.
Print Assumptions owned_matrix_holds.
Print Assumptions auxiliary_valid_agree.
