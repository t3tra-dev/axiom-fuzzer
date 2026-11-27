From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Require Import AxiomFuzzer.Clause.Kernel.
Import ListNotations.

Fixpoint term_variables (t : term) : list nat := match t with
  | Var v => [v]
  | Fun _ ts => flat_map term_variables ts
  end.
Definition atom_variables (a : atom) : list nat := match a with
  | Pred _ ts => flat_map term_variables ts
  | Eq x y => term_variables x ++ term_variables y
  end.
Definition literal_variables (l : literal) : list nat := atom_variables (snd l).
Definition clause_variables (c : clause) : list nat := flat_map literal_variables c.
Definition vars_disjoint (a b : clause) : bool :=
  forallb (fun v => negb (existsb (Nat.eqb v) (clause_variables b))) (clause_variables a).
Fixpoint components_disjoint (cs : list clause) : bool := match cs with
  | [] => true
  | c :: cs => forallb (vars_disjoint c) cs && components_disjoint cs
  end.

Lemma vars_disjoint_sound a b : vars_disjoint a b=true ->
  forall v, In v (clause_variables a) -> ~ In v (clause_variables b).
Proof.
  unfold vars_disjoint. rewrite forallb_forall. intros Disjoint v InA InB.
  specialize (Disjoint v InA). apply negb_true_iff in Disjoint.
  assert (Present : existsb (Nat.eqb v) (clause_variables b)=true).
  { apply existsb_exists; exists v; split; [exact InB|apply Nat.eqb_refl]. }
  congruence.
Qed.
Lemma clause_variables_app a b :
  clause_variables (a ++ b)=clause_variables a ++ clause_variables b.
Proof. unfold clause_variables; apply flat_map_app. Qed.
Lemma clause_variables_concat cs v : In v (clause_variables (concat cs)) ->
  exists c, In c cs /\ In v (clause_variables c).
Proof.
  induction cs as [|c cs IH]; simpl; [tauto|]. rewrite clause_variables_app, in_app_iff.
  intros [InC|InRest].
  - exists c; auto.
  - destruct (IH InRest) as [d [InD InV]]. exists d; auto.
Qed.

Section SplitSemantics.
Context {D : Type} (functions : nat -> list D -> D) (predicates : nat -> list D -> Prop).

Lemma eval_variables_agree : forall t rho sigma,
  (forall v, In v (term_variables t) -> rho v=sigma v) ->
  eval functions rho t=eval functions sigma t.
Proof.
  fix IH 1. intros [v|f ts] rho sigma Agree; simpl in *.
  - apply Agree; auto.
  - f_equal. induction ts as [|t ts Hts]; simpl in *; [reflexivity|].
    f_equal.
    + apply IH. intros v InT. apply Agree; apply in_or_app; auto.
    + apply Hts. intros v InTs. apply Agree; apply in_or_app; auto.
Qed.
Lemma eval_arguments_variables_agree ts rho sigma :
  (forall v, In v (flat_map term_variables ts) -> rho v=sigma v) ->
  map (eval functions rho) ts=map (eval functions sigma) ts.
Proof.
  induction ts as [|t ts IH]; simpl; intros Agree; [reflexivity|].
  f_equal.
  - apply eval_variables_agree. intros v InT. apply Agree; apply in_or_app; auto.
  - apply IH. intros v InTs. apply Agree; apply in_or_app; auto.
Qed.
Lemma atom_variables_agree a rho sigma :
  (forall v, In v (atom_variables a) -> rho v=sigma v) ->
  (atom_holds functions predicates rho a <-> atom_holds functions predicates sigma a).
Proof.
  destruct a as [p ts|x y]; simpl; intros Agree.
  - now rewrite (eval_arguments_variables_agree ts rho sigma Agree).
  - assert (X : eval functions rho x=eval functions sigma x).
    { apply eval_variables_agree; intros v InX. apply Agree; apply in_or_app; auto. }
    assert (Y : eval functions rho y=eval functions sigma y).
    { apply eval_variables_agree; intros v InY. apply Agree; apply in_or_app; auto. }
    now rewrite X,Y.
Qed.
Lemma literal_variables_agree l rho sigma :
  (forall v, In v (literal_variables l) -> rho v=sigma v) ->
  (literal_holds functions predicates rho l <-> literal_holds functions predicates sigma l).
Proof.
  destruct l as [sign a]. unfold literal_variables, literal_holds; simpl.
  intros Agree; pose proof (atom_variables_agree a rho sigma Agree) as Same.
  destruct sign; tauto.
Qed.
Lemma clause_variables_agree c rho sigma :
  (forall v, In v (clause_variables c) -> rho v=sigma v) ->
  (clause_holds functions predicates rho c <-> clause_holds functions predicates sigma c).
Proof.
  intros Agree. assert (Same : forall l, In l c ->
    (literal_holds functions predicates rho l <-> literal_holds functions predicates sigma l)).
  { intros l InL. apply literal_variables_agree. intros v InV. apply Agree.
    unfold clause_variables; apply in_flat_map; exists l; auto. }
  unfold clause_holds; split; intros [l [InL Holds]]; exists l; split; [exact InL| |exact InL|].
  - apply (Same l InL); exact Holds.
  - apply (Same l InL); exact Holds.
Qed.
Lemma clause_holds_app rho a b : clause_holds functions predicates rho (a ++ b) <->
  clause_holds functions predicates rho a \/ clause_holds functions predicates rho b.
Proof.
  unfold clause_holds. split.
  - intros [l [InL Holds]]. apply in_app_iff in InL. destruct InL; [left|right]; exists l; auto.
  - intros [[l [InL Holds]]|[l [InL Holds]]]; exists l; split; auto; apply in_or_app; auto.
Qed.

Variable inhabitant : D.
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.

Lemma invalid_clause_witness c : ~ valid functions predicates c ->
  exists rho, ~ clause_holds functions predicates rho c.
Proof.
  intros Invalid. destruct (excluded_middle (exists rho, ~ clause_holds functions predicates rho c)) as [Witness|NoWitness].
  - exact Witness.
  - exfalso; apply Invalid; intros rho.
    destruct (excluded_middle (clause_holds functions predicates rho c)) as [Holds|NotHolds].
    + exact Holds.
    + exfalso; apply NoWitness; now exists rho.
Qed.
Lemma disjoint_disjunction_valid a b :
  (forall v, In v (clause_variables a) -> ~ In v (clause_variables b)) ->
  valid functions predicates (a ++ b) ->
  valid functions predicates a \/ valid functions predicates b.
Proof.
  intros Disjoint Both. destruct (excluded_middle (valid functions predicates a)) as [A|NotA]; [now left|].
  right. destruct (invalid_clause_witness a NotA) as [rhoA FalseA]. intros rhoB.
  set (merged := fun v => if existsb (Nat.eqb v) (clause_variables a) then rhoA v else rhoB v).
  assert (AgreeA : forall v, In v (clause_variables a) -> merged v=rhoA v).
  { intros v InA. unfold merged.
    assert (Present : existsb (Nat.eqb v) (clause_variables a)=true).
    { apply existsb_exists; exists v; split; [exact InA|apply Nat.eqb_refl]. }
    now rewrite Present. }
  assert (AgreeB : forall v, In v (clause_variables b) -> merged v=rhoB v).
  { intros v InB. unfold merged. destruct (existsb (Nat.eqb v) (clause_variables a)) eqn:Present; [|reflexivity].
    exfalso. apply existsb_exists in Present as [w [InA Equal]]. apply Nat.eqb_eq in Equal; subst w.
    exact (Disjoint v InA InB). }
  specialize (Both merged). apply clause_holds_app in Both as [A|B].
  - exfalso; apply FalseA. apply (clause_variables_agree a merged rhoA AgreeA); exact A.
  - apply (clause_variables_agree b merged rhoB AgreeB); exact B.
Qed.

Theorem split_components_valid cs : components_disjoint cs=true ->
  valid functions predicates (concat cs) -> Exists (valid functions predicates) cs.
Proof.
  induction cs as [|c cs IH]; simpl.
  - intros _ Valid. destruct (Valid (fun _ => inhabitant)) as [l [InL _]]. contradiction.
  - rewrite andb_true_iff. intros [Disjoint Tail] Valid.
    assert (NoShared : forall v, In v (clause_variables c) -> ~ In v (clause_variables (concat cs))).
    { intros v InC InRest. destruct (clause_variables_concat cs v InRest) as [d [InD InV]].
      apply forallb_forall with (x:=d) in Disjoint; [|exact InD].
      exact (vars_disjoint_sound c d Disjoint v InC InV). }
    destruct (disjoint_disjunction_valid c (concat cs) NoShared Valid) as [Head|Rest].
    + now apply Exists_cons_hd.
    + apply Exists_cons_tl; now apply IH.
Qed.
End SplitSemantics.
Print Assumptions split_components_valid.

(* Conditions are inferred from the primitive parents, never trusted metadata.
   Components keep their original variable identifiers; a split is a literal
   partition, not an independently alpha-normalized collection of clauses. *)
Inductive fo_rule := Ordinary (r : rule) | Component (id : nat).
Definition fo_step := (fo_rule * clause)%type.
Definition annotated := (clause * list nat)%type.
Definition rule_parents (r : rule) : list nat := match r with
  | Input _ => []
  | Instance p _ | Copy p | Equality_resolve p _ | Equality_factor p _ _ _ _ => [p]
  | Resolve p _ q _ | Paramodulate p _ _ q _ _ => [p;q]
  end.
Fixpoint gather_dependencies (db : list annotated) (parents : list nat) : option (list nat) :=
  match parents with
  | [] => Some []
  | p::ps => match nth_error db p,gather_dependencies db ps with
      | Some (_,deps),Some rest => Some (deps++rest)
      | _,_ => None end
  end.
Definition infer_fo inputs components (db : list annotated) r : option annotated :=
  match r with
  | Component id => match nth_error components id with Some c => Some (c,[id]) | None => None end
  | Ordinary primitive =>
      match infer inputs (map fst db) primitive,gather_dependencies db (rule_parents primitive) with
      | Some c,Some deps => Some (c,nodup Nat.eq_dec deps)
      | _,_ => None end
  end.
Fixpoint replay_fo inputs components (db : list annotated) (steps : list fo_step) : option (list annotated) :=
  match steps with
  | [] => Some db
  | (r,c)::rest => match infer_fo inputs components db r with
      | Some (expected,deps) => if included expected c then replay_fo inputs components (db++[(c,deps)]) rest else None
      | None => None end
  end.

Section ConditionalSoundness.
Context {D : Type} (functions : nat -> list D -> D) (predicates : nat -> list D -> Prop).
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.
Local Abbreviation valid := (AxiomFuzzer.Clause.Kernel.valid functions predicates).
Definition component_holds (components : list clause) (id : nat) := exists c, nth_error components id=Some c /\ valid c.
Definition dependencies_hold components deps := Forall (component_holds components) deps.
Definition annotated_valid components (a : annotated) := dependencies_hold components (snd a) -> valid (fst a).

Lemma valid_tautology : valid [(true,Eq (Var 0) (Var 0))].
Proof. intros rho; exists (true,Eq (Var 0) (Var 0)); split; [now left|reflexivity]. Qed.
Lemma valid_replacements db : exists safe,
  Forall valid safe /\ forall i, match nth_error db i with
    | Some c => valid c -> nth_error safe i=Some c
    | None => nth_error safe i=None end.
Proof.
  induction db as [|c db [safe [Safe Same]]].
  - exists []; split; [constructor|intros [|i]; reflexivity].
  - destruct (excluded_middle (valid c)) as [C|NotC].
    + exists (c::safe); split; [now constructor|].
      intros [|i]; simpl; [intros _; reflexivity|exact (Same i)].
    + exists ([(true,Eq (Var 0) (Var 0))]::safe); split.
      * constructor; [exact valid_tautology|exact Safe].
      * intros [|i]; simpl; [intros C; contradiction|apply Same].
Qed.
Lemma infer_parent_agreement inputs db safe r :
  (forall p, In p (rule_parents r) -> nth_error db p=nth_error safe p) ->
  infer inputs db r=infer inputs safe r.
Proof.
  destruct r as [i|p s|p|p i q j|p i|p i rev q j ctx|p i ri j rj];
    intros Same; unfold infer, infer_with; try reflexivity.
  - rewrite (Same p) by (simpl; auto); reflexivity.
  - apply Same; simpl; auto.
  - rewrite (Same p), (Same q) by (simpl; auto); reflexivity.
  - rewrite (Same p) by (simpl; auto); reflexivity.
  - rewrite (Same p), (Same q) by (simpl; auto); reflexivity.
  - rewrite (Same p) by (simpl; auto); reflexivity.
Qed.
Lemma infer_locally_sound inputs db r expected : Forall valid inputs ->
  (forall p c, In p (rule_parents r) -> nth_error db p=Some c -> valid c) ->
  infer inputs db r=Some expected -> valid expected.
Proof.
  intros Inputs Parents Inferred. destruct (valid_replacements db) as [safe [Safe Same]].
  assert (Agree : forall p, In p (rule_parents r) -> nth_error db p=nth_error safe p).
  { intros p Parent. specialize (Same p). destruct (nth_error db p) as [c|] eqn:Lookup.
    - symmetry; apply Same; eapply Parents; eauto.
    - now symmetry. }
  rewrite (infer_parent_agreement inputs db safe r Agree) in Inferred.
  assert (LiftInputs : Forall (fun c => forall rho, ~ ~ clause_holds functions predicates rho c) inputs).
  { eapply Forall_impl; [|exact Inputs]; intros c C rho Not; apply Not,C. }
  assert (LiftSafe : Forall (fun c => forall rho, ~ ~ clause_holds functions predicates rho c) safe).
  { eapply Forall_impl; [|exact Safe]; intros c C rho Not; apply Not,C. }
  intros rho. destruct (excluded_middle (clause_holds functions predicates rho expected)) as [H|Not]; [exact H|].
  exfalso; exact (infer_sound functions predicates inputs safe r expected LiftInputs LiftSafe Inferred rho Not).
Qed.
Lemma gathered_parents_valid components db parents deps :
  Forall (annotated_valid components) db -> gather_dependencies db parents=Some deps ->
  dependencies_hold components deps ->
  forall p a, In p parents -> nth_error db p=Some a -> valid (fst a).
Proof.
  intros Database. revert deps. induction parents as [|p ps IH]; intros deps Run Holds q a InQ Lookup; [contradiction|].
  simpl in Run. destruct (nth_error db p) as [[c ds]|] eqn:Head; [|discriminate].
  destruct (gather_dependencies db ps) as [rest|] eqn:Tail; [|discriminate].
  inversion Run; subst deps. unfold dependencies_hold in Holds; apply Forall_app in Holds as [Ds Rest].
  destruct InQ as [<-|InQ].
  - rewrite Head in Lookup; inversion Lookup; subst a.
    apply Forall_forall with (x:=(c,ds)) in Database; [now apply Database|eapply nth_error_In; exact Head].
  - eapply IH; eauto.
Qed.
Lemma infer_fo_sound inputs components db r result : Forall valid inputs ->
  Forall (annotated_valid components) db -> infer_fo inputs components db r=Some result ->
  annotated_valid components result.
Proof.
  intros Inputs Database. destruct r as [r|id]; simpl.
  - destruct (infer inputs (map fst db) r) as [c|] eqn:Inferred; [|discriminate].
    destruct (gather_dependencies db (rule_parents r)) as [deps|] eqn:Deps; [|discriminate].
    intros H; inversion H; subst result. intros Enabled; simpl in Enabled |- *.
    assert (EnabledAll : dependencies_hold components deps).
    { unfold dependencies_hold in *. rewrite Forall_forall in *. intros d InD.
      apply Enabled; apply nodup_In; exact InD. }
    eapply (infer_locally_sound inputs (map fst db) r c); [exact Inputs| |exact Inferred].
    intros p parent Used Lookup. rewrite nth_error_map in Lookup.
    destruct (@nth_error (clause * list nat) db p) as [a|] eqn:Found; simpl in Lookup; [|discriminate].
    inversion Lookup; subst parent. eapply gathered_parents_valid; eauto.
  - destruct (@nth_error clause components id) as [c|] eqn:Lookup; [|discriminate].
    intros H; inversion H; subst result. intros Enabled.
    inversion Enabled as [|d ds Head Tail]; subst. destruct Head as [other [Other Valid]].
    rewrite Lookup in Other; inversion Other; exact Valid.
Qed.
Lemma replay_fo_sound inputs components steps db result : Forall valid inputs ->
  Forall (annotated_valid components) db -> replay_fo inputs components db steps=Some result ->
  Forall (annotated_valid components) result.
Proof.
  revert db result. induction steps as [|[r c] steps IH]; intros db result Inputs Database Run; simpl in Run.
  - inversion Run; subst; exact Database.
  - destruct (infer_fo inputs components db r) as [[expected deps]|] eqn:Inferred; [|discriminate].
    destruct (included expected c) eqn:Included; [|discriminate].
    eapply IH; [exact Inputs| |exact Run]. apply Forall_app; split; [exact Database|].
    constructor; [|constructor]. intros Enabled rho.
    eapply included_sound; [exact Included|].
    apply (infer_fo_sound inputs components db r (expected,deps) Inputs Database Inferred Enabled rho).
Qed.
End ConditionalSoundness.

(* Stdlib's nodup keeps the last occurrence of each element and tests membership by a
   scan of the rest of the list. The indexed version walks from the right with an AVL
   set of the elements seen so far; it computes the same list. Lists of up to 64
   elements keep the scan, which is faster at that size. *)
Fixpoint nodup_indexed (xs : list nat) : list nat * ClauseMap.t unit := match xs with
  | [] => ([],ClauseMap.empty unit)
  | x::rest => let (kept,seen) := nodup_indexed rest in
      if ClauseMap.mem x seen then (kept,seen) else (x::kept,ClauseMap.add x tt seen)
  end.
Lemma nodup_indexed_correct xs : fst (nodup_indexed xs)=nodup Nat.eq_dec xs /\
  forall v, ClauseMap.In v (snd (nodup_indexed xs)) <-> In v xs.
Proof.
  induction xs as [|x rest [Kept Seen]]; simpl.
  - split; [reflexivity|]. intros v. rewrite ClauseFacts.empty_in_iff. tauto.
  - destruct (nodup_indexed rest) as [kept seen]; simpl in Kept,Seen.
    destruct (ClauseMap.mem x seen) eqn:Member.
    + assert (Present : In x rest) by (apply Seen,ClauseFacts.mem_in_iff,Member).
      destruct (in_dec Nat.eq_dec x rest) as [_|Missing]; [|contradiction].
      split; [exact Kept|]. intros v. simpl. rewrite Seen. split; [now right|].
      intros [<-|In]; [exact Present|exact In].
    + assert (Missing : ~ In x rest).
      { intros In. apply Seen,ClauseFacts.mem_in_iff in In. congruence. }
      destruct (in_dec Nat.eq_dec x rest) as [In|_]; [contradiction|].
      simpl. split; [now rewrite Kept|]. intros v. rewrite ClauseFacts.add_in_iff,Seen.
      reflexivity.
Qed.
Definition fast_nodup xs := if length xs <=? 64 then nodup Nat.eq_dec xs else fst (nodup_indexed xs).
Lemma fast_nodup_correct xs : fast_nodup xs=nodup Nat.eq_dec xs.
Proof. unfold fast_nodup. destruct (length xs <=? 64); [reflexivity|apply nodup_indexed_correct]. Qed.

Fixpoint gather_dependencies_with (parent : nat -> option annotated) (parents : list nat)
    : option (list nat) := match parents with
  | [] => Some []
  | p::ps => match parent p,gather_dependencies_with parent ps with
      | Some (_,deps),Some rest => Some (deps++rest)
      | _,_ => None end
  end.
Definition infer_fo_with (input components : nat -> option clause)
    (parent : nat -> option annotated) (r : fo_rule) : option annotated := match r with
  | Component id => match components id with Some c => Some (c,[id]) | None => None end
  | Ordinary primitive =>
      match infer_with input (fun i => option_map fst (parent i)) primitive,
            gather_dependencies_with parent (rule_parents primitive) with
      | Some c,Some deps => Some (c,fast_nodup deps)
      | _,_ => None end
  end.
Fixpoint fast_replay_fo_from (input components : nat -> option clause)
    (db : ClauseMap.t annotated) next (revdb : list annotated) (steps : list fo_step)
    : option (list annotated) := match steps with
  | [] => Some (rev_append revdb [])
  | (r,c)::rest => match infer_fo_with input components (fun i => ClauseMap.find i db) r with
      | Some (expected,deps) => if included expected c then
          fast_replay_fo_from input components (ClauseMap.add next (c,deps) db)
            (S next) ((c,deps)::revdb) rest
        else None
      | None => None end
  end.
Definition fast_replay_fo inputs components steps :=
  fast_replay_fo_from (cached inputs) (cached components) (ClauseMap.empty annotated) 0 [] steps.

Lemma gather_dependencies_with_correct db parent parents :
  (forall p, parent p=nth_error db p) ->
  gather_dependencies_with parent parents=gather_dependencies db parents.
Proof.
  intros Same; induction parents as [|p parents IH]; simpl; [reflexivity|].
  now rewrite Same,IH.
Qed.
Lemma infer_fo_with_correct inputs components db parent r :
  (forall p, parent p=nth_error db p) ->
  infer_fo_with (cached inputs) (cached components) parent r=infer_fo inputs components db r.
Proof.
  intros Same; destruct r as [primitive|id]; simpl.
  - rewrite (gather_dependencies_with_correct db parent (rule_parents primitive) Same).
    assert (Parents : forall p, option_map fst (parent p)=nth_error (map fst db) p).
    { intros p; rewrite Same,nth_error_map; reflexivity. }
    assert (Primitive : infer_with (cached inputs) (fun i => option_map fst (parent i)) primitive=
        infer inputs (map fst db) primitive).
    { unfold infer,infer_with. destruct primitive; repeat rewrite cached_correct;
        repeat rewrite Parents; reflexivity. }
    rewrite Primitive. destruct (infer inputs (map fst db) primitive); [|reflexivity].
    destruct (gather_dependencies db (rule_parents primitive)); [|reflexivity].
    now rewrite fast_nodup_correct.
  - now rewrite cached_correct.
Qed.
Lemma fast_replay_fo_from_correct inputs components steps : forall prefix db,
  (forall i, ClauseMap.find i db=nth_error prefix i) ->
  fast_replay_fo_from (cached inputs) (cached components) db (length prefix) (rev prefix) steps=
    replay_fo inputs components prefix steps.
Proof.
  induction steps as [|[r c] steps IH]; intros prefix db Same; simpl.
  - now rewrite <- rev_alt,rev_involutive.
  - rewrite (infer_fo_with_correct inputs components prefix (fun i => ClauseMap.find i db) r Same).
    destruct (infer_fo inputs components prefix r) as [[expected deps]|] eqn:Inferred; [|reflexivity].
    destruct (included expected c); [|reflexivity].
    specialize (IH (prefix++[(c,deps)]) (ClauseMap.add (length prefix) (c,deps) db)
      (indexed_snoc prefix db (c,deps) Same)).
    rewrite length_app in IH; simpl in IH.
    replace (length prefix + 1) with (S (length prefix)) in IH by lia.
    rewrite rev_app_distr in IH; simpl in IH; exact IH.
Qed.
Theorem fast_replay_fo_correct inputs components steps :
  fast_replay_fo inputs components steps=replay_fo inputs components [] steps.
Proof.
  unfold fast_replay_fo.
  apply (fast_replay_fo_from_correct inputs components steps [] (ClauseMap.empty annotated)).
  intros i; rewrite ClauseFacts.empty_o; now destruct i.
Qed.
Print Assumptions fast_replay_fo_correct.

(* The acceptance path keeps each replayed database in its AVL index. No list of all
   steps is rebuilt, reversed, or indexed again after the replay. *)
Definition indexes {A} (index : ClauseMap.t A) (xs : list A) := forall i, ClauseMap.find i index=nth_error xs i.
Lemma empty_indexes {A} : indexes (ClauseMap.empty A) [].
Proof. intros i; rewrite ClauseFacts.empty_o; now destruct i. Qed.
Fixpoint index_replay_fo_from (input components : nat -> option clause)
    (db : ClauseMap.t annotated) next (steps : list fo_step) : option (ClauseMap.t annotated) :=
  match steps with
  | [] => Some db
  | (r,c)::rest => match infer_fo_with input components (fun i => ClauseMap.find i db) r with
      | Some (expected,deps) => if included expected c then
          index_replay_fo_from input components (ClauseMap.add next (c,deps) db) (S next) rest
        else None
      | None => None end
  end.
Lemma index_replay_fo_from_correct inputs components steps : forall prefix db, indexes db prefix ->
  match index_replay_fo_from (cached inputs) (cached components) db (length prefix) steps,
        replay_fo inputs components prefix steps with
  | Some index,Some result => indexes index result
  | None,None => True
  | _,_ => False end.
Proof.
  induction steps as [|[r c] steps IH]; intros prefix db Same; simpl; [exact Same|].
  rewrite (infer_fo_with_correct inputs components prefix (fun i => ClauseMap.find i db) r Same).
  destruct (infer_fo inputs components prefix r) as [[expected deps]|]; [|exact I].
  destruct (included expected c); [|exact I].
  specialize (IH (prefix++[(c,deps)]) (ClauseMap.add (length prefix) (c,deps) db)
    (indexed_snoc prefix db (c,deps) Same)).
  rewrite length_app in IH; simpl in IH.
  replace (length prefix + 1) with (S (length prefix)) in IH by lia. exact IH.
Qed.

Definition sat_literal := (bool * nat)%type.
Definition sat_clause := list sat_literal.
Definition sat_equal (x y : sat_literal) :=
  Bool.eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).
Definition sat_included (xs ys : sat_clause) :=
  forallb (fun x => existsb (sat_equal x) ys) xs.
Definition sat_remove (l : sat_literal) (c : sat_clause) :=
  filter (fun x => negb (sat_equal l x)) c.
Definition sat_resolve (left : sat_clause) (pivot : nat) (right : sat_clause) : option sat_clause :=
  if existsb (sat_equal (true,pivot)) left && existsb (sat_equal (false,pivot)) right
  then Some (sat_remove (true,pivot) left ++ sat_remove (false,pivot) right)
  else if existsb (sat_equal (false,pivot)) left && existsb (sat_equal (true,pivot)) right
  then Some (sat_remove (false,pivot) left ++ sat_remove (true,pivot) right)
  else None.

Lemma sat_equal_spec x y : sat_equal x y=true <-> x=y.
Proof.
  destruct x as [a i], y as [b j]. unfold sat_equal; simpl.
  rewrite andb_true_iff, Bool.eqb_true_iff, Nat.eqb_eq.
  split; [intros [-> ->]; reflexivity|intros H; inversion H; auto].
Qed.

(* Membership in two AVL sets of the claimed literal identifiers (one per sign) replaces
   the scan of the claimed clause for each expected literal. Claims of up to 64 literals
   keep the scan, which is faster at that size. *)
Fixpoint sat_index (ys : sat_clause) (positive negative : ClauseMap.t unit) :=
  match ys with
  | [] => (positive,negative)
  | (sign,id)::ys => if sign then sat_index ys (ClauseMap.add id tt positive) negative
      else sat_index ys positive (ClauseMap.add id tt negative)
  end.
Lemma sat_index_spec ys : forall (positive negative : ClauseMap.t unit) (sign : bool) (id : nat),
  ClauseMap.In id (if sign then fst (sat_index ys positive negative) else snd (sat_index ys positive negative)) <->
  ClauseMap.In id (if sign then positive else negative) \/ In (sign,id) ys.
Proof.
  induction ys as [|[b x] ys IH]; intros positive negative sign id; simpl; [tauto|].
  destruct b; rewrite IH; destruct sign; rewrite ?ClauseFacts.add_in_iff;
    split; intros H; repeat destruct H as [H|H]; subst; try tauto;
    try (inversion H; subst; tauto); try (right; left; reflexivity).
Qed.
Definition indexed_sat_included (xs ys : sat_clause) :=
  let (positive,negative) := sat_index ys (ClauseMap.empty unit) (ClauseMap.empty unit) in
  forallb (fun x : sat_literal => ClauseMap.mem (snd x) (if fst x then positive else negative)) xs.
Lemma indexed_sat_included_correct xs ys : indexed_sat_included xs ys=sat_included xs ys.
Proof.
  unfold indexed_sat_included,sat_included.
  pose proof (sat_index_spec ys (ClauseMap.empty unit) (ClauseMap.empty unit)) as Spec.
  destruct (sat_index ys (ClauseMap.empty unit) (ClauseMap.empty unit)) as [positive negative].
  assert (Member : forall x : sat_literal,
    ClauseMap.mem (snd x) (if fst x then positive else negative)=existsb (sat_equal x) ys).
  { intros [sign id]. apply Bool.eq_iff_eq_true. rewrite <- ClauseFacts.mem_in_iff, existsb_exists.
    specialize (Spec sign id). transitivity (In (sign,id) ys).
    - destruct sign; simpl in Spec |- *; rewrite Spec, ClauseFacts.empty_in_iff; tauto.
    - split; [intros In; exists (sign,id); split; [exact In|apply sat_equal_spec; reflexivity]|].
      intros [y [In Equal]]. apply sat_equal_spec in Equal; now subst y. }
  induction xs as [|x xs IH]; simpl; [reflexivity|]. now rewrite IH, Member.
Qed.
Definition fast_sat_included xs ys :=
  if length ys <=? 64 then sat_included xs ys else indexed_sat_included xs ys.
Lemma fast_sat_included_correct xs ys : fast_sat_included xs ys=sat_included xs ys.
Proof. unfold fast_sat_included. destruct (length ys <=? 64); [reflexivity|apply indexed_sat_included_correct]. Qed.

Section Soundness.
Variable val : nat -> Prop.
Definition sat_literal_holds (l : sat_literal) :=
  if fst l then val (snd l) else ~val (snd l).
Definition sat_holds (c : sat_clause) :=
  exists l, In l c /\ sat_literal_holds l.

Lemma sat_included_sound expected claimed :
  sat_included expected claimed=true -> sat_holds expected -> sat_holds claimed.
Proof.
  unfold sat_included. rewrite forallb_forall.
  intros Included [l [InL Holds]].
  specialize (Included l InL). apply existsb_exists in Included as [r [InR Equal]].
  apply sat_equal_spec in Equal; subst r. exists l; auto.
Qed.

Lemma sat_remove_cases l c : sat_holds c ->
  sat_holds (sat_remove l c) \/ sat_literal_holds l.
Proof.
  intros [x [InX Holds]]. destruct (sat_equal l x) eqn:Equal.
  - right. apply sat_equal_spec in Equal; now subst x.
  - left. exists x; split; [|exact Holds].
    unfold sat_remove; apply filter_In; split; [exact InX|now rewrite Equal].
Qed.

Lemma sat_holds_app l r : sat_holds l \/ sat_holds r -> sat_holds (l ++ r).
Proof.
  intros [[x [InX Holds]]|[x [InX Holds]]]; exists x; split;
    try exact Holds; apply in_or_app; auto.
Qed.

Lemma sat_resolve_oriented_sound left pivot right :
  sat_holds left -> sat_holds right ->
  sat_holds (sat_remove (true,pivot) left ++ sat_remove (false,pivot) right).
Proof.
  intros Left Right.
  destruct (sat_remove_cases (true,pivot) left Left) as [Rest|Positive].
  - apply sat_holds_app; now left.
  - destruct (sat_remove_cases (false,pivot) right Right) as [Rest|Negative].
    + apply sat_holds_app; now right.
    + exfalso; exact (Negative Positive).
Qed.

Lemma sat_resolve_sound left pivot right result :
  sat_resolve left pivot right=Some result ->
  sat_holds left -> sat_holds right -> sat_holds result.
Proof.
  unfold sat_resolve.
  destruct (existsb (sat_equal (true,pivot)) left && existsb (sat_equal (false,pivot)) right).
  - intros Run Left Right. inversion Run; subst result.
    now apply sat_resolve_oriented_sound.
  - destruct (existsb (sat_equal (false,pivot)) left && existsb (sat_equal (true,pivot)) right);
      [|discriminate].
    intros Run Left Right. inversion Run; subst result.
    destruct (sat_remove_cases (false,pivot) left Left) as [Rest|Negative].
    + apply sat_holds_app; now left.
    + destruct (sat_remove_cases (true,pivot) right Right) as [Rest|Positive].
      * apply sat_holds_app; now right.
      * exfalso; exact (Negative Positive).
Qed.
End Soundness.
Print Assumptions sat_included_sound.
Print Assumptions sat_resolve_sound.

Fixpoint collect_components (components : list clause) (ids : list nat) : option (list clause) :=
  match ids with
  | [] => Some []
  | id::ids => match nth_error components id,collect_components components ids with
      | Some c,Some cs => Some (c::cs) | _,_ => None end
  end.
Definition infer_split components (db : list annotated) (split : nat * list nat) : option sat_clause :=
  let (parent,ids) := split in
  match nth_error db parent,collect_components components ids with
  | Some (c,deps),Some cs =>
      if included c (concat cs) && included (concat cs) c && components_disjoint cs
      then Some (map (fun id => (false,id)) deps ++ map (fun id => (true,id)) ids)
      else None
  | _,_ => None end.
Fixpoint build_splits components db (splits : list (nat * list nat)) : option (list sat_clause) :=
  match splits with
  | [] => Some []
  | s::ss => match infer_split components db s,build_splits components db ss with
      | Some c,Some cs => Some (c::cs) | _,_ => None end
  end.
Fixpoint collect_components_with (component : nat -> option clause) (ids : list nat)
    : option (list clause) := match ids with
  | [] => Some []
  | id::ids => match component id,collect_components_with component ids with
      | Some c,Some cs => Some (c::cs) | _,_ => None end
  end.
Definition infer_split_with (component : nat -> option clause) (fo : nat -> option annotated)
    (split : nat * list nat) : option sat_clause :=
  let (parent,ids) := split in
  match fo parent,collect_components_with component ids with
  | Some (c,deps),Some cs =>
      if included c (concat cs) && included (concat cs) c && components_disjoint cs
      then Some (map (fun id => (false,id)) deps ++ map (fun id => (true,id)) ids)
      else None
  | _,_ => None end.
Fixpoint build_splits_with (component : nat -> option clause) (fo : nat -> option annotated)
    (splits : list (nat * list nat)) : option (list sat_clause) := match splits with
  | [] => Some []
  | s::ss => match infer_split_with component fo s,build_splits_with component fo ss with
      | Some c,Some cs => Some (c::cs) | _,_ => None end
  end.
Definition fast_build_splits components fo splits :=
  build_splits_with (cached components) (cached fo) splits.

Lemma collect_components_with_correct components ids :
  collect_components_with (cached components) ids=collect_components components ids.
Proof.
  induction ids as [|id ids IH]; simpl; [reflexivity|].
  now rewrite cached_correct,IH.
Qed.
Lemma infer_split_with_correct components fo split :
  infer_split_with (cached components) (cached fo) split=infer_split components fo split.
Proof.
  destruct split as [parent ids]; unfold infer_split_with,infer_split.
  now rewrite cached_correct,collect_components_with_correct.
Qed.
Lemma build_splits_with_correct components fo splits :
  build_splits_with (cached components) (cached fo) splits=build_splits components fo splits.
Proof.
  induction splits as [|s ss IH]; simpl; [reflexivity|].
  now rewrite infer_split_with_correct,IH.
Qed.
Theorem fast_build_splits_correct components fo splits :
  fast_build_splits components fo splits=build_splits components fo splits.
Proof. apply build_splits_with_correct. Qed.
Print Assumptions fast_build_splits_correct.
Lemma build_splits_with_lookup components fo lookup splits : indexes lookup fo ->
  build_splits_with (cached components) (fun i => ClauseMap.find i lookup) splits=build_splits components fo splits.
Proof.
  intros Same. induction splits as [|[parent ids] ss IH]; simpl; [reflexivity|].
  rewrite IH. unfold infer_split_with,infer_split.
  now rewrite Same,collect_components_with_correct.
Qed.

Definition infer_conflict (db : list annotated) id : option sat_clause :=
  match nth_error db id with
  | Some ([],deps) => Some (map (fun id => (false,id)) deps)
  | _ => None end.
Inductive sat_rule := Split (id : nat) | Conflict (id : nat)
  | Boolean_resolve (left pivot right : nat).
Definition sat_step := (sat_rule * sat_clause)%type.
Definition infer_sat (fo : list annotated) (splits : list sat_clause) (db : list sat_clause)
    (r : sat_rule) : option sat_clause := match r with
  | Split id => nth_error splits id
  | Conflict id => infer_conflict fo id
  | Boolean_resolve p pivot q => match nth_error db p,nth_error db q with
      | Some l,Some r => sat_resolve l pivot r | _,_ => None end
  end.
Fixpoint replay_sat fo splits (db : list sat_clause) (steps : list sat_step) : option (list sat_clause) :=
  match steps with
  | [] => Some db
  | (r,c)::steps => match infer_sat fo splits db r with
      | Some expected => if sat_included expected c then replay_sat fo splits (db++[c]) steps else None
      | None => None end
  end.
Definition infer_conflict_with (fo : nat -> option annotated) id : option sat_clause :=
  match fo id with
  | Some ([],deps) => Some (map (fun id => (false,id)) deps)
  | _ => None end.
Definition infer_sat_with (fo : nat -> option annotated)
    (splits db : nat -> option sat_clause) (r : sat_rule) : option sat_clause := match r with
  | Split id => splits id
  | Conflict id => infer_conflict_with fo id
  | Boolean_resolve p pivot q => match db p,db q with
      | Some l,Some r => sat_resolve l pivot r | _,_ => None end
  end.
Fixpoint fast_replay_sat_from (fo : nat -> option annotated) (splits : nat -> option sat_clause)
    (db : ClauseMap.t sat_clause) next (revdb : list sat_clause) (steps : list sat_step)
    : option (list sat_clause) := match steps with
  | [] => Some (rev_append revdb [])
  | (r,c)::rest => match infer_sat_with fo splits (fun i => ClauseMap.find i db) r with
      | Some expected => if sat_included expected c then
          fast_replay_sat_from fo splits (ClauseMap.add next c db) (S next) (c::revdb) rest
        else None
      | None => None end
  end.
Definition fast_replay_sat fo splits steps :=
  fast_replay_sat_from (cached fo) (cached splits) (ClauseMap.empty sat_clause) 0 [] steps.

Lemma infer_conflict_with_correct fo id :
  infer_conflict_with (cached fo) id=infer_conflict fo id.
Proof. unfold infer_conflict_with,infer_conflict; now rewrite cached_correct. Qed.
Lemma infer_sat_with_correct fo splits db parent r :
  (forall p, parent p=nth_error db p) ->
  infer_sat_with (cached fo) (cached splits) parent r=infer_sat fo splits db r.
Proof.
  intros Same; destruct r as [id|id|left pivot right]; simpl.
  - apply cached_correct.
  - apply infer_conflict_with_correct.
  - now rewrite !Same.
Qed.
Lemma fast_replay_sat_from_correct fo splits steps : forall prefix db,
  (forall i, ClauseMap.find i db=nth_error prefix i) ->
  fast_replay_sat_from (cached fo) (cached splits) db (length prefix) (rev prefix) steps=
    replay_sat fo splits prefix steps.
Proof.
  induction steps as [|[r c] steps IH]; intros prefix db Same; simpl.
  - now rewrite <- rev_alt,rev_involutive.
  - rewrite (infer_sat_with_correct fo splits prefix (fun i => ClauseMap.find i db) r Same).
    destruct (infer_sat fo splits prefix r) as [expected|] eqn:Inferred; [|reflexivity].
    destruct (sat_included expected c); [|reflexivity].
    specialize (IH (prefix++[c]) (ClauseMap.add (length prefix) c db)
      (indexed_snoc prefix db c Same)).
    rewrite length_app in IH; simpl in IH.
    replace (length prefix + 1) with (S (length prefix)) in IH by lia.
    rewrite rev_app_distr in IH; simpl in IH; exact IH.
Qed.
Theorem fast_replay_sat_correct fo splits steps :
  fast_replay_sat fo splits steps=replay_sat fo splits [] steps.
Proof.
  unfold fast_replay_sat.
  apply (fast_replay_sat_from_correct fo splits steps [] (ClauseMap.empty sat_clause)).
  intros i; rewrite ClauseFacts.empty_o; now destruct i.
Qed.
Print Assumptions fast_replay_sat_correct.
Lemma infer_sat_with_lookup fo lookup splits db parent r : indexes lookup fo ->
  (forall p, parent p=nth_error db p) ->
  infer_sat_with (fun i => ClauseMap.find i lookup) (cached splits) parent r=infer_sat fo splits db r.
Proof.
  intros FO Same; destruct r as [id|id|left pivot right]; simpl.
  - apply cached_correct.
  - unfold infer_conflict_with,infer_conflict. now rewrite FO.
  - now rewrite !Same.
Qed.
Fixpoint index_replay_sat_from (fo : nat -> option annotated) (splits : nat -> option sat_clause)
    (db : ClauseMap.t sat_clause) next (steps : list sat_step) : option (ClauseMap.t sat_clause) :=
  match steps with
  | [] => Some db
  | (r,c)::rest => match infer_sat_with fo splits (fun i => ClauseMap.find i db) r with
      | Some expected => if fast_sat_included expected c then
          index_replay_sat_from fo splits (ClauseMap.add next c db) (S next) rest
        else None
      | None => None end
  end.
Lemma index_replay_sat_from_correct fo lookup splits steps : indexes lookup fo -> forall prefix db, indexes db prefix ->
  match index_replay_sat_from (fun i => ClauseMap.find i lookup) (cached splits) db (length prefix) steps,
        replay_sat fo splits prefix steps with
  | Some index,Some result => indexes index result
  | None,None => True
  | _,_ => False end.
Proof.
  intros FO. induction steps as [|[r c] steps IH]; intros prefix db Same; simpl; [exact Same|].
  rewrite (infer_sat_with_lookup fo lookup splits prefix (fun i => ClauseMap.find i db) r FO Same).
  destruct (infer_sat fo splits prefix r) as [expected|]; [|exact I].
  rewrite fast_sat_included_correct. destruct (sat_included expected c); [|exact I].
  specialize (IH (prefix++[c]) (ClauseMap.add (length prefix) c db) (indexed_snoc prefix db c Same)).
  rewrite length_app in IH; simpl in IH.
  replace (length prefix + 1) with (S (length prefix)) in IH by lia. exact IH.
Qed.

Record certificate := {
  components : list clause;
  fo_steps : list fo_step;
  splits : list (nat * list nat);
  boolean_steps : list sat_step;
  boolean_root : nat
}.
(* The list replay below is the specification; check keeps every database indexed. *)
Definition check_list inputs proof : bool :=
  match replay_fo inputs (components proof) [] (fo_steps proof) with
  | Some fo => match build_splits (components proof) fo (splits proof) with
      | Some split_clauses => match replay_sat fo split_clauses [] (boolean_steps proof) with
          | Some db => match nth_error db (boolean_root proof) with Some [] => true | _ => false end
          | None => false end
      | None => false end
  | None => false end.
Definition check inputs proof : bool :=
  let component := cached (components proof) in
  match index_replay_fo_from (cached inputs) component (ClauseMap.empty annotated) 0 (fo_steps proof) with
  | Some fo =>
      match build_splits_with component (fun i => ClauseMap.find i fo) (splits proof) with
      | Some split_clauses =>
          match index_replay_sat_from (fun i => ClauseMap.find i fo) (cached split_clauses)
              (ClauseMap.empty sat_clause) 0 (boolean_steps proof) with
          | Some db => match ClauseMap.find (boolean_root proof) db with Some [] => true | _ => false end
          | None => false end
      | None => false end
  | None => false end.
Theorem check_correct inputs proof : check inputs proof=check_list inputs proof.
Proof.
  unfold check,check_list. cbv zeta.
  pose proof (index_replay_fo_from_correct inputs (components proof) (fo_steps proof) []
    (ClauseMap.empty annotated) empty_indexes) as FO. cbn [length] in FO.
  destruct (index_replay_fo_from _ _ _ 0 _) as [index|];
    destruct (replay_fo inputs (components proof) [] (fo_steps proof)) as [fo|]; try contradiction; [|reflexivity].
  rewrite (build_splits_with_lookup (components proof) fo index (splits proof) FO).
  destruct (build_splits (components proof) fo (splits proof)) as [split_clauses|]; [|reflexivity].
  pose proof (index_replay_sat_from_correct fo index split_clauses (boolean_steps proof) FO []
    (ClauseMap.empty sat_clause) empty_indexes) as SAT. cbn [length] in SAT.
  destruct (index_replay_sat_from _ _ _ 0 _) as [db_index|];
    destruct (replay_sat fo split_clauses [] (boolean_steps proof)) as [db|]; try contradiction; [|reflexivity].
  now rewrite SAT.
Qed.
Print Assumptions check_correct.

Lemma collect_components_member components ids cs : collect_components components ids=Some cs ->
  forall c, In c cs -> exists id, In id ids /\ nth_error components id=Some c.
Proof.
  revert cs. induction ids as [|id ids IH]; intros cs Run c InC; simpl in Run.
  - inversion Run; subst cs; contradiction.
  - destruct (@nth_error clause components id) as [head|] eqn:Head; [|discriminate].
    destruct (collect_components components ids) as [tail|] eqn:Tail; [|discriminate].
    inversion Run; subst cs. destruct InC as [<-|InC].
    + exists id; split; [now left|exact Head].
    + destruct (IH tail eq_refl c InC) as [j [InJ Lookup]]. exists j; split; [now right|exact Lookup].
Qed.
Section CertificateSoundness.
Context {D : Type} (functions : nat -> list D -> D) (predicates : nat -> list D -> Prop).
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~Q.
Variable inhabitant : D.
Local Abbreviation valid := (AxiomFuzzer.Clause.Kernel.valid functions predicates).
Local Abbreviation enabled := (dependencies_hold functions predicates).
Local Abbreviation conditional := (annotated_valid functions predicates).
Local Abbreviation valuation := (component_holds functions predicates).

Lemma dependencies_cases components deps :
  sat_holds (valuation components) (map (fun id => (false,id)) deps) \/ enabled components deps.
Proof.
  induction deps as [|id deps [Negative|Enabled]].
  - right; constructor.
  - left. destruct Negative as [l [InL Holds]]. exists l; split; [now right|exact Holds].
  - destruct (excluded_middle (valuation components id)) as [Holds|Not].
    + right; now constructor.
    + left; exists (false,id); split; [now left|exact Not].
Qed.
Lemma infer_split_sound components db split c :
  Forall (conditional components) db -> infer_split components db split=Some c ->
  sat_holds (valuation components) c.
Proof.
  intros Database. destruct split as [parent ids]. unfold infer_split.
  destruct (nth_error db parent) as [[body deps]|] eqn:Parent; [|discriminate].
  destruct (collect_components components ids) as [cs|] eqn:Parts; [|discriminate].
  destruct (included body (concat cs) && included (concat cs) body && components_disjoint cs) eqn:Checks;
    [|discriminate]. intros Run; inversion Run; subst c.
  apply andb_true_iff in Checks as [Included Disjoint]. apply andb_true_iff in Included as [Forward Backward].
  apply sat_holds_app. destruct (dependencies_cases components deps) as [Negative|Enabled]; [now left|].
  right. assert (ParentValid : valid body).
  { apply Forall_forall with (x:=(body,deps)) in Database; [now apply Database|eapply nth_error_In; exact Parent]. }
  assert (Together : valid (concat cs)).
  { intros rho; eapply included_sound; [exact Forward|apply ParentValid]. }
  pose proof (split_components_valid functions predicates inhabitant excluded_middle cs Disjoint Together) as One.
  apply Exists_exists in One as [part [InPart Valid]].
  destruct (collect_components_member components ids cs Parts part InPart) as [id [InId Lookup]].
  exists (true,id); split; [apply in_map; exact InId|]. exists part; auto.
Qed.
Lemma build_splits_sound components db splits cs :
  Forall (conditional components) db -> build_splits components db splits=Some cs ->
  Forall (sat_holds (valuation components)) cs.
Proof.
  intros Database. revert cs. induction splits as [|s ss IH]; intros cs Run; simpl in Run.
  - inversion Run; constructor.
  - destruct (infer_split components db s) as [c|] eqn:Head; [|discriminate].
    destruct (build_splits components db ss) as [tail|] eqn:Tail; [|discriminate].
    inversion Run; subst cs; constructor; [eapply infer_split_sound; eauto|now apply IH].
Qed.
Lemma infer_conflict_sound components db id c :
  Forall (conditional components) db -> infer_conflict db id=Some c ->
  sat_holds (valuation components) c.
Proof.
  intros Database. unfold infer_conflict. destruct (nth_error db id) as [[body deps]|] eqn:Lookup; [|discriminate].
  destruct body; [|discriminate]. intros Run; inversion Run; subst c.
  destruct (dependencies_cases components deps) as [Negative|Enabled]; [exact Negative|].
  exfalso. apply Forall_forall with (x:=([],deps)) in Database; [|eapply nth_error_In; exact Lookup].
  destruct (Database Enabled (fun _ => inhabitant)) as [l [Impossible _]]. exact Impossible.
Qed.
Lemma infer_sat_sound components fo splits db r c :
  Forall (conditional components) fo -> Forall (sat_holds (valuation components)) splits ->
  Forall (sat_holds (valuation components)) db -> infer_sat fo splits db r=Some c ->
  sat_holds (valuation components) c.
Proof.
  intros FO Splits Database. destruct r as [id|id|left pivot right]; simpl.
  - intros Lookup; apply Forall_forall with (x:=c) in Splits; [exact Splits|eapply nth_error_In; exact Lookup].
  - now apply infer_conflict_sound.
  - destruct (nth_error db left) as [l|] eqn:Left; [|discriminate].
    destruct (nth_error db right) as [r|] eqn:Right; [|discriminate]. intros Run.
    eapply sat_resolve_sound; [exact Run| |].
    all: eapply Forall_forall; [exact Database|eapply nth_error_In; eassumption].
Qed.
Lemma replay_sat_sound components fo splits steps db result :
  Forall (conditional components) fo -> Forall (sat_holds (valuation components)) splits ->
  Forall (sat_holds (valuation components)) db -> replay_sat fo splits db steps=Some result ->
  Forall (sat_holds (valuation components)) result.
Proof.
  revert db result. induction steps as [|[r c] steps IH]; intros db result FO Splits Database Run; simpl in Run.
  - inversion Run; subst; exact Database.
  - destruct (infer_sat fo splits db r) as [expected|] eqn:Inferred; [|discriminate].
    destruct (sat_included expected c) eqn:Included; [|discriminate].
    eapply IH; [exact FO|exact Splits| |exact Run]. apply Forall_app; split; [exact Database|].
    constructor; [|constructor]. eapply sat_included_sound; [exact Included|].
    exact (infer_sat_sound components fo splits db r expected FO Splits Database Inferred).
Qed.
Theorem check_sound_with_inhabitant inputs proof : check inputs proof=true ->
  ~ Forall valid inputs.
Proof.
  rewrite check_correct. unfold check_list.
  destruct (replay_fo inputs (components proof) [] (fo_steps proof)) as [fo|] eqn:FO; [|discriminate].
  destruct (build_splits (components proof) fo (splits proof)) as [split_clauses|] eqn:Splits; [|discriminate].
  destruct (replay_sat fo split_clauses [] (boolean_steps proof)) as [db|] eqn:SAT; [|discriminate].
  destruct (nth_error db (boolean_root proof)) as [root|] eqn:Root; [|discriminate].
  destruct root; [|discriminate]. intros _ Inputs.
  assert (ValidFO : Forall (conditional (components proof)) fo).
  { eapply replay_fo_sound; [exact excluded_middle|exact Inputs|constructor|exact FO]. }
  assert (ValidSplits : Forall (sat_holds (valuation (components proof))) split_clauses).
  { eapply build_splits_sound; eauto. }
  assert (ValidSAT : Forall (sat_holds (valuation (components proof))) db).
  { eapply replay_sat_sound; [exact ValidFO|exact ValidSplits|constructor|exact SAT]. }
  apply Forall_forall with (x:=[]) in ValidSAT; [|eapply nth_error_In; exact Root].
  destruct ValidSAT as [l [Impossible _]]. exact Impossible.
Qed.
End CertificateSoundness.
Theorem check_sound {D : Type} (functions : nat -> list D -> D)
    (predicates : nat -> list D -> Prop) (excluded_middle : forall Q : Prop, Q \/ ~Q)
    inputs proof : check inputs proof=true -> forall inhabitant : D,
    ~ Forall (AxiomFuzzer.Clause.Kernel.valid functions predicates) inputs.
Proof. intros Checked inhabitant; exact (check_sound_with_inhabitant functions predicates excluded_middle inhabitant inputs proof Checked). Qed.
Print Assumptions check_sound.
