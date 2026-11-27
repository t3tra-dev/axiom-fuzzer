(* SkolemModel *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Require Import AxiomFuzzer.Source.Language.
Require Import AxiomFuzzer.Preprocess.NormalForms.
Require Import AxiomFuzzer.Preprocess.Quantifiers.
Import ListNotations.

Section SourceAgreement.
Context {F P D : Type} (functions : F -> list D -> D) (predicates : P -> list D -> Prop).
Lemma source_term_bound_agree : forall t bound other free,
  (forall i, bound i=other i) -> source_eval functions bound free t=source_eval functions other free t.
Proof.
  fix IH 1. intros [i|i|f ts] bound other free Agree; simpl; auto.
  f_equal. induction ts as [|t ts Hts]; simpl; [reflexivity|]. rewrite (IH t _ _ _ Agree), Hts. reflexivity.
Qed.
Theorem normal_bound_agree : forall f bound other free,
  (forall i, bound i=other i) ->
  (normal_holds functions predicates bound free f <-> normal_holds functions predicates other free f).
Proof.
  fix IH 1. intros [sign p ts|sign x y|fs|fs|f|f] bound other free Agree; simpl.
  - assert (E : map (source_eval functions bound free) ts=map (source_eval functions other free) ts).
    { apply map_ext. intros t. apply source_term_bound_agree, Agree. }
    now rewrite E.
  - rewrite (source_term_bound_agree x _ _ _ Agree), (source_term_bound_agree y _ _ _ Agree). reflexivity.
  - induction fs; simpl; [tauto|]. rewrite (IH a _ _ _ Agree), IHfs. reflexivity.
  - induction fs; simpl; [tauto|]. rewrite (IH a _ _ _ Agree), IHfs. reflexivity.
  - assert (Each : forall x, normal_holds functions predicates (push x bound) free f <->
        normal_holds functions predicates (push x other) free f).
    { intros x. apply IH. intros [|i]; simpl; auto. }
    split; intros H x; apply Each, H.
  - assert (Each : forall x, normal_holds functions predicates (push x bound) free f <->
        normal_holds functions predicates (push x other) free f).
    { intros x. apply IH. intros [|i]; simpl; auto. }
    split; intros [x H]; exists x; apply Each; exact H.
Qed.
End SourceAgreement.

Section Model.
Context {F P T L D : Type}.
Variable functions : F -> list D -> D.
Variable predicates : P -> list D -> Prop.
Variable default : D.
Variable apply : F -> list T -> T.
Variable variable : nat -> T.
Variable witness : nat -> list T -> T.
Variable predicate : bool -> P -> list T -> L.
Variable equality : bool -> T -> T -> L.
Let interpretation := nat -> list D -> D.
Variable eval : interpretation -> (nat -> D) -> T -> D.
Variable literal : interpretation -> (nat -> D) -> L -> Prop.

(* The target term/literal algebra is abstract, as in the extracted traversal.
   These premises describe only constructor meanings; the model extension is
   proved below rather than assumed as a law of the whole transformation. *)
Hypothesis eval_apply : forall sk rho f args, eval sk rho (apply f args)=functions f (map (eval sk rho) args).
Hypothesis eval_variable : forall sk rho v, eval sk rho (variable v)=rho v.
Hypothesis eval_witness : forall sk rho id args, eval sk rho (witness id args)=sk id (map (eval sk rho) args).
Hypothesis literal_predicate : forall sk rho sign p args,
  literal sk rho (predicate sign p args) <-> signed sign (predicates p (map (eval sk rho) args)).
Hypothesis literal_equality : forall sk rho sign x y,
  literal sk rho (equality sign x y) <-> signed sign (eval sk rho x=eval sk rho y).

Definition agree_symbols n (sk other : interpretation) := forall id args, id<n -> sk id args=other id args.
Definition term_depends n (vars : nat -> Prop) t := forall sk other rho sigma,
  agree_symbols n sk other -> (forall v, vars v -> rho v=sigma v) -> eval sk rho t=eval other sigma t.
Definition all_variables (_ : nat) := True.
Definition universal_symbols n q := forall sk other rho,
  agree_symbols n sk other -> (universal_holds (literal sk) rho q <-> universal_holds (literal other) rho q).
Definition environment sk rho env i := match nth_error env i with Some t => eval sk rho t | None => default end.
Let free := fun _ : nat => default.

Lemma agree_symbols_refl n sk : agree_symbols n sk sk.
Proof. intros id args H; reflexivity. Qed.
Lemma agree_symbols_sym n sk other : agree_symbols n sk other -> agree_symbols n other sk.
Proof. intros H id args Bound. symmetry. apply H, Bound. Qed.
Lemma agree_symbols_weaken n m sk other : n<=m -> agree_symbols m sk other -> agree_symbols n sk other.
Proof. intros Bound H id args Hi. apply H. lia. Qed.
Lemma depends_weaken n m vars more t : n<=m -> (forall v, vars v -> more v) ->
  term_depends n vars t -> term_depends m more t.
Proof. intros Bound Subset Dep sk other rho sigma Agree Values. apply Dep; [eapply agree_symbols_weaken; eauto|auto]. Qed.
Lemma depends_variable n vars v : vars v -> term_depends n vars (variable v).
Proof. intros Hv sk other rho sigma _ Values. rewrite !eval_variable. now apply Values. Qed.
Lemma dependent_arguments n vars args sk other rho sigma : Forall (term_depends n vars) args ->
  agree_symbols n sk other -> (forall v, vars v -> rho v=sigma v) ->
  map (eval sk rho) args=map (eval other sigma) args.
Proof.
  intros Args Agree Values. apply map_ext_in. intros t Ht.
  rewrite Forall_forall in Args. apply (Args t Ht); assumption.
Qed.
Lemma depends_apply n vars f args : Forall (term_depends n vars) args -> term_depends n vars (apply f args).
Proof. intros Args sk other rho sigma Agree Values. rewrite !eval_apply. f_equal. eapply dependent_arguments; eauto. Qed.
Lemma depends_witness n vars id args : id<n -> Forall (term_depends n vars) args -> term_depends n vars (witness id args).
Proof.
  intros Bound Args sk other rho sigma Agree Values. rewrite !eval_witness.
  rewrite (dependent_arguments n vars args sk other rho sigma Args Agree Values). apply Agree, Bound.
Qed.
Lemma arguments_weaken n m vars more args : n<=m -> (forall v, vars v -> more v) ->
  Forall (term_depends n vars) args -> Forall (term_depends m more) args.
Proof.
  intros Bound Subset Args. rewrite Forall_forall in *. intros t Ht. eapply depends_weaken; eauto.
Qed.
Lemma environment_agree n vars env sk other rho sigma : Forall (term_depends n vars) env ->
  agree_symbols n sk other -> (forall v, vars v -> rho v=sigma v) ->
  forall i, environment sk rho env i=environment other sigma env i.
Proof.
  intros Env Agree Values i. unfold environment. destruct (nth_error env i) as [t|] eqn:Found; [|reflexivity].
  rewrite Forall_forall in Env. apply (Env t); [eapply nth_error_In; eauto|assumption|assumption].
Qed.
Lemma environment_cons sk rho t env i : environment sk rho (t::env) i=push (eval sk rho t) (environment sk rho env) i.
Proof. destruct i; reflexivity. Qed.
Lemma variable_arguments sk rho vars : map (eval sk rho) (map variable vars)=map rho vars.
Proof. rewrite map_map. apply map_ext. intros v. apply eval_variable. Qed.

Variable visit : unit -> bool.
Variable limit : nat.
Let trace := quantifier_trace visit apply variable witness predicate equality limit.
Let traces := quantifier_traces visit apply variable witness predicate equality limit.

Lemma instantiate_semantics env t result sk rho : instantiate_bound visit apply env t=Some result ->
  eval sk rho result=source_eval functions (environment sk rho env) free t.
Proof.
  intros Inst. apply (instantiate_bound_correct visit apply functions (eval sk rho) (eval_apply sk rho)
    env (environment sk rho env) free); [|exact Inst].
  intros i x Found. unfold environment. now rewrite Found.
Qed.
Lemma instantiate_arguments_semantics env ts args sk rho : map_option (instantiate_bound visit apply env) ts=Some args ->
  map (eval sk rho) args=map (source_eval functions (environment sk rho env) free) ts.
Proof.
  revert args. induction ts as [|t ts IH]; intros args; simpl.
  - intros E. inversion E. reflexivity.
  - destruct (instantiate_bound visit apply env t) as [x|] eqn:Term; [|discriminate].
    destruct (map_option (instantiate_bound visit apply env) ts) as [xs|] eqn:Rest; [|discriminate].
    intros E. inversion E; subst. simpl. rewrite (instantiate_semantics env t x sk rho Term), (IH xs eq_refl). reflexivity.
Qed.
Lemma instantiate_depends : forall t env result n vars,
  instantiate_bound visit apply env t=Some result -> Forall (term_depends n vars) env -> term_depends n vars result.
Proof.
  fix IH 1. intros [i|i|f ts] env result n vars; cbn [instantiate_bound]; destruct (visit tt); try discriminate.
  - intros Found Env. rewrite Forall_forall in Env. apply Env. eapply nth_error_In; eauto.
  - destruct (map_option (instantiate_bound visit apply env) ts) as [args|] eqn:Args; [|discriminate].
    intros E Env. inversion E; subst. apply depends_apply. clear E.
    revert args Args. induction ts as [|t ts Hts]; intros args; simpl.
    + intros E; inversion E; constructor.
    + destruct (instantiate_bound visit apply env t) as [x|] eqn:Term; [|discriminate].
      destruct (map_option (instantiate_bound visit apply env) ts) as [xs|] eqn:Rest; [|discriminate].
      intros E. inversion E; subst. constructor; [eapply IH; eauto|apply Hts, eq_refl].
Qed.
Lemma instantiate_arguments_depends env ts args n vars :
  map_option (instantiate_bound visit apply env) ts=Some args ->
  Forall (term_depends n vars) env -> Forall (term_depends n vars) args.
Proof.
  revert args. induction ts as [|t ts IH]; intros args; simpl.
  - intros E _. inversion E; constructor.
  - destruct (instantiate_bound visit apply env t) as [x|] eqn:Term; [|discriminate].
    destruct (map_option (instantiate_bound visit apply env) ts) as [xs|] eqn:Rest; [|discriminate].
    intros E Env. inversion E; subst. constructor; [eapply instantiate_depends; eauto|apply IH; auto].
Qed.
Lemma trace_monotone env us v s f q v' s' : trace env us v s f q v' s' -> v<=v' /\ s<=s'.
Proof. intros H. pose proof (proj1 (quantifier_trace_counts visit apply variable witness predicate equality limit) _ _ _ _ _ _ _ _ H). lia. Qed.
Lemma traces_monotone env us v s fs qs v' s' : traces env us v s fs qs v' s' -> v<=v' /\ s<=s'.
Proof. intros H. pose proof (proj2 (quantifier_trace_counts visit apply variable witness predicate equality limit) _ _ _ _ _ _ _ _ H). lia. Qed.

Lemma universal_symbols_weaken n m q : n<=m -> universal_symbols n q -> universal_symbols m q.
Proof. intros Bound Dep sk other rho Agree. apply Dep. eapply agree_symbols_weaken; eauto. Qed.
Theorem trace_symbol_support :
  (forall env us v s f q v' s', trace env us v s f q v' s' ->
    Forall (term_depends s all_variables) env -> Forall (term_depends s all_variables) us -> universal_symbols s' q) /\
  (forall env us v s fs qs v' s', traces env us v s fs qs v' s' ->
    Forall (term_depends s all_variables) env -> Forall (term_depends s all_variables) us -> Forall (universal_symbols s') qs).
Proof.
  apply (traces_mutind visit apply variable witness predicate equality limit).
  - intros env us v s sign p ts args Inst Env Us sk other rho Agree. simpl. rewrite !literal_predicate.
    rewrite (dependent_arguments s all_variables args sk other rho rho); [reflexivity| |exact Agree|reflexivity].
    eapply instantiate_arguments_depends; eauto.
  - intros env us v s sign x y a b X Y Env Us sk other rho Agree. simpl. rewrite !literal_equality.
    pose proof (instantiate_depends x env a s all_variables X Env) as Adep.
    pose proof (instantiate_depends y env b s all_variables Y Env) as Bdep.
    rewrite (Adep sk other rho rho Agree), (Bdep sk other rho rho Agree); reflexivity.
  - intros env us v s fs qs v' s' Run IH Env Us sk other rho Agree.
    rewrite !universal_conj. apply Forall_equiv_in. intros q Hq.
    specialize (IH Env Us). rewrite Forall_forall in IH. apply (IH q Hq), Agree.
  - intros env us v s fs qs v' s' Run IH Env Us sk other rho Agree.
    rewrite !universal_disj. apply clause_equiv_in. intros q Hq.
    specialize (IH Env Us). rewrite Forall_forall in IH. apply (IH q Hq), Agree.
  - intros env us v s f q v' s' Bound Run IH Env Us.
    assert (NewEnv : Forall (term_depends s all_variables) (variable v::env)).
    { constructor; [apply depends_variable; exact I|exact Env]. }
    assert (NewUs : Forall (term_depends s all_variables) (us++[variable v])).
    { apply Forall_app. split; [exact Us|constructor; [apply depends_variable; exact I|constructor]]. }
    specialize (IH NewEnv NewUs). intros sk other rho Agree. simpl.
    split; intros H x; apply (IH sk other (update rho v x) Agree), H.
  - intros env us v s f q v' s' Bound Run IH Env Us.
    apply IH.
    + constructor.
      * apply depends_witness; [lia|]. apply (arguments_weaken s (S s) all_variables all_variables us); auto; lia.
      * apply (arguments_weaken s (S s) all_variables all_variables env); auto; lia.
    + apply (arguments_weaken s (S s) all_variables all_variables us); auto; lia.
  - intros; constructor.
  - intros env us v s f fs q qs mid_v mid_s v' s' First IHfirst Rest IHrest Env Us.
    pose proof (trace_monotone _ _ _ _ _ _ _ _ First) as [_ Middle].
    pose proof (traces_monotone _ _ _ _ _ _ _ _ Rest) as [_ Final].
    constructor.
    + eapply universal_symbols_weaken; [exact Final|]. apply IHfirst; assumption.
    + apply IHrest.
      * apply (arguments_weaken s mid_s all_variables all_variables env); auto.
      * apply (arguments_weaken s mid_s all_variables all_variables us); auto.
Qed.

Lemma variables_depend n vars : Forall (term_depends n (fun v => In v vars)) (map variable vars).
Proof. apply Forall_map, Forall_forall. intros v Hv. apply depends_variable, Hv. Qed.
Lemma universal_environment vars s env v : Forall (term_depends s (fun x => In x vars)) env ->
  Forall (term_depends s (fun x => In x (vars++[v]))) (variable v::env).
Proof.
  intros Env. constructor.
  - apply depends_variable, in_or_app. right. now left.
  - apply (arguments_weaken s s (fun x => In x vars) (fun x => In x (vars++[v])) env); auto.
    intros x Hx. apply in_or_app. now left.
Qed.
Lemma witness_environment vars s env us : us=map variable vars ->
  Forall (term_depends s (fun x => In x vars)) env ->
  Forall (term_depends (S s) (fun x => In x vars)) (witness s us::env).
Proof.
  intros E Env. subst us. constructor.
  - apply depends_witness; [lia|apply variables_depend].
  - apply (arguments_weaken s (S s) (fun x => In x vars) (fun x => In x vars) env); auto; lia.
Qed.
Lemma variables_before_append vars v : (forall x, In x vars -> x<v) ->
  forall x, In x (vars++[v]) -> x<S v.
Proof. intros Before x Hx. apply in_app_or in Hx as [Hx|[E|Empty]]; [specialize (Before x Hx)|subst|contradiction]; lia. Qed.
Lemma fresh_environment vars s env v sk rho x : (forall y, In y vars -> y<v) ->
  Forall (term_depends s (fun y => In y vars)) env ->
  forall i, environment sk (update rho v x) (variable v::env) i=push x (environment sk rho env) i.
Proof.
  intros Before Env [|i]; cbn [environment push nth_error].
  - rewrite eval_variable. unfold update. now rewrite Nat.eqb_refl.
  - change (environment sk (update rho v x) env i=environment sk rho env i).
    apply (environment_agree s (fun y => In y vars) env sk sk (update rho v x) rho Env).
    + apply agree_symbols_refl.
    + intros y Hy. unfold update. destruct (Nat.eqb_spec y v); [subst; specialize (Before v Hy); lia|reflexivity].
Qed.
Lemma normal_environment_agree f vars s env sk other rho :
  Forall (term_depends s (fun x => In x vars)) env -> agree_symbols s sk other ->
  (normal_holds functions predicates (environment sk rho env) free f <->
   normal_holds functions predicates (environment other rho env) free f).
Proof.
  intros Env Agree. apply normal_bound_agree. apply (environment_agree s (fun x => In x vars) env sk other rho rho Env Agree).
  reflexivity.
Qed.

(* Projection works for EVERY interpretation of the new functions. This
   direction is constructive and does not assume they select good witnesses. *)
Theorem trace_model_projection :
  (forall env us v s f q v' s', trace env us v s f q v' s' ->
    forall vars, us=map variable vars -> (forall x, In x vars -> x<v) ->
    Forall (term_depends s (fun x => In x vars)) env -> forall sk rho,
    universal_holds (literal sk) rho q -> normal_holds functions predicates (environment sk rho env) free f) /\
  (forall env us v s fs qs v' s', traces env us v s fs qs v' s' ->
    forall vars, us=map variable vars -> (forall x, In x vars -> x<v) ->
    Forall (term_depends s (fun x => In x vars)) env -> forall sk rho,
    (universal_holds (literal sk) rho (UConj qs) -> normal_holds functions predicates (environment sk rho env) free (NConj fs)) /\
    (universal_holds (literal sk) rho (UDisj qs) -> normal_holds functions predicates (environment sk rho env) free (NDisj fs))).
Proof.
  apply (traces_mutind visit apply variable witness predicate equality limit).
  - intros env us v s sign p ts args Inst vars Us Before Env sk rho Holds. simpl in *.
    apply literal_predicate in Holds. rewrite (instantiate_arguments_semantics _ _ _ sk rho Inst) in Holds. exact Holds.
  - intros env us v s sign x y a b X Y vars Us Before Env sk rho Holds. simpl in *.
    apply literal_equality in Holds. rewrite (instantiate_semantics _ _ _ sk rho X), (instantiate_semantics _ _ _ sk rho Y) in Holds. exact Holds.
  - intros env us v s fs qs v' s' Run IH vars Us Before Env sk rho. apply (proj1 (IH vars Us Before Env sk rho)).
  - intros env us v s fs qs v' s' Run IH vars Us Before Env sk rho. apply (proj2 (IH vars Us Before Env sk rho)).
  - intros env us v s f q v' s' Bound Run IH vars Us Before Env sk rho Holds. simpl in *. intros x.
    assert (Us' : us++[variable v]=map variable (vars++[v])) by (rewrite map_app; simpl; now rewrite Us).
    pose proof (IH (vars++[v]) Us' (variables_before_append vars v Before)
      (universal_environment vars s env v Env) sk (update rho v x) (Holds x)) as Body.
    apply (normal_bound_agree functions predicates f _ _ free (fresh_environment vars s env v sk rho x Before Env)) in Body.
    exact Body.
  - intros env us v s f q v' s' Bound Run IH vars Us Before Env sk rho Holds. simpl.
    exists (eval sk rho (witness s us)).
    pose proof (IH vars Us Before (witness_environment vars s env us Us Env) sk rho Holds) as Body.
    apply (normal_bound_agree functions predicates f _ _ free (environment_cons sk rho (witness s us) env)) in Body. exact Body.
  - intros; simpl; tauto.
  - intros env us v s f fs q qs mid_v mid_s v' s' First IHfirst Rest IHrest vars Us Before Env sk rho.
    destruct (trace_monotone _ _ _ _ _ _ _ _ First) as [Vars Symbols].
    assert (Before' : forall x, In x vars -> x<mid_v) by (intros x Hx; specialize (Before x Hx); lia).
    assert (Env' : Forall (term_depends mid_s (fun x => In x vars)) env).
    { apply (arguments_weaken s mid_s (fun x => In x vars) (fun x => In x vars) env); auto. }
    specialize (IHfirst vars Us Before Env sk rho). specialize (IHrest vars Us Before' Env' sk rho). simpl in *. tauto.
Qed.

Hypothesis excluded_middle : forall Q : Prop, Q \/ ~ Q.
Hypothesis functional_choice : forall R : list D -> D -> Prop,
  (forall args, exists x, R args x) -> exists g, forall args, R args (g args).

Definition replace_symbol (old : interpretation) fresh (g : list D -> D) : interpretation :=
  fun id args => if id =? fresh then g args else old id args.
Lemma replace_symbol_preserves old fresh g : agree_symbols fresh (replace_symbol old fresh g) old.
Proof. intros id args Bound. unfold replace_symbol. destruct (Nat.eqb_spec id fresh); [lia|reflexivity]. Qed.
Lemma agree_symbols_trans n first second third : agree_symbols n first second -> agree_symbols n second third -> agree_symbols n first third.
Proof. intros One Two id args Bound. rewrite (One id args Bound). apply Two, Bound. Qed.
Lemma choose_environment_witness f vars s env old : Forall (term_depends s (fun v => In v vars)) env ->
  exists g, forall rho,
    ((exists x, normal_holds functions predicates (push x (environment old rho env)) free f) <->
     normal_holds functions predicates (push (g (map rho vars)) (environment old rho env)) free f).
Proof.
  intros Env. apply (skolem_witness_on_support default excluded_middle functional_choice vars
    (fun rho x => normal_holds functions predicates (push x (environment old rho env)) free f)).
  intros rho other x Agree. apply normal_bound_agree. intros [|i]; simpl; [reflexivity|].
  apply (environment_agree s (fun v => In v vars) env old old rho other Env); [apply agree_symbols_refl|exact Agree].
Qed.
Lemma chosen_environment vars s env us old g rho : us=map variable vars ->
  Forall (term_depends s (fun v => In v vars)) env -> forall i,
  environment (replace_symbol old s g) rho (witness s us::env) i=
  push (g (map rho vars)) (environment old rho env) i.
Proof.
  intros Us Env [|i]; cbn [environment push nth_error].
  - rewrite eval_witness, Us, variable_arguments. unfold replace_symbol. now rewrite Nat.eqb_refl.
  - change (environment (replace_symbol old s g) rho env i=environment old rho env i).
    apply (environment_agree s (fun v => In v vars) env (replace_symbol old s g) old rho rho Env).
    + apply replace_symbol_preserves.
    + reflexivity.
Qed.

(* One interpretation is constructed for the ENTIRE trace, outside forall rho.
   Earlier symbol meanings are preserved. This also handles false branches:
   a fresh function selects a witness whenever one exists, and is otherwise
   total using the nonempty-domain element. No branch is assumed satisfiable. *)
Theorem trace_model_extension :
  (forall env us v s f q v' s', trace env us v s f q v' s' ->
    forall vars, us=map variable vars -> (forall x, In x vars -> x<v) ->
    Forall (term_depends s (fun x => In x vars)) env -> forall old,
    exists sk, agree_symbols s sk old /\ forall rho,
      (normal_holds functions predicates (environment old rho env) free f <-> universal_holds (literal sk) rho q)) /\
  (forall env us v s fs qs v' s', traces env us v s fs qs v' s' ->
    forall vars, us=map variable vars -> (forall x, In x vars -> x<v) ->
    Forall (term_depends s (fun x => In x vars)) env -> forall old,
    exists sk, agree_symbols s sk old /\
      (forall rho, normal_holds functions predicates (environment old rho env) free (NConj fs) <-> universal_holds (literal sk) rho (UConj qs)) /\
      (forall rho, normal_holds functions predicates (environment old rho env) free (NDisj fs) <-> universal_holds (literal sk) rho (UDisj qs))).
Proof.
  apply (traces_mutind visit apply variable witness predicate equality limit).
  - intros env us v s sign p ts args Inst vars Us Before Env old.
    exists old. split; [apply agree_symbols_refl|]. intros rho. simpl. rewrite literal_predicate.
    now rewrite (instantiate_arguments_semantics env ts args old rho Inst).
  - intros env us v s sign x y a b X Y vars Us Before Env old.
    exists old. split; [apply agree_symbols_refl|]. intros rho. simpl. rewrite literal_equality.
    now rewrite (instantiate_semantics env x a old rho X), (instantiate_semantics env y b old rho Y).
  - intros env us v s fs qs v' s' Run IH vars Us Before Env old.
    destruct (IH vars Us Before Env old) as [sk [Agree [Conj Disj]]]. exists sk. auto.
  - intros env us v s fs qs v' s' Run IH vars Us Before Env old.
    destruct (IH vars Us Before Env old) as [sk [Agree [Conj Disj]]]. exists sk. auto.
  - intros env us v s f q v' s' Bound Run IH vars Us Before Env old.
    assert (Us' : us++[variable v]=map variable (vars++[v])) by (rewrite map_app; simpl; now rewrite Us).
    destruct (IH (vars++[v]) Us' (variables_before_append vars v Before)
      (universal_environment vars s env v Env) old) as [sk [Agree Correct]].
    exists sk. split; [exact Agree|]. intros rho. simpl.
    assert (Each : forall x, normal_holds functions predicates (push x (environment old rho env)) free f <->
      universal_holds (literal sk) (update rho v x) q).
    { intros x. specialize (Correct (update rho v x)).
      rewrite (normal_bound_agree functions predicates f _ _ free (fresh_environment vars s env v old rho x Before Env)) in Correct.
      exact Correct. }
    split; intros H x; apply Each, H.
  - intros env us v s f q v' s' Bound Run IH vars Us Before Env old.
    destruct (choose_environment_witness f vars s env old Env) as [g Witness].
    destruct (IH vars Us Before (witness_environment vars s env us Us Env) (replace_symbol old s g)) as [sk [Agree Correct]].
    exists sk. split.
    + apply (agree_symbols_trans s sk (replace_symbol old s g) old).
      * apply (agree_symbols_weaken s (S s)); [lia|exact Agree].
      * apply replace_symbol_preserves.
    + intros rho. simpl. rewrite (Witness rho).
      transitivity (normal_holds functions predicates (environment (replace_symbol old s g) rho (witness s us::env)) free f).
      * symmetry. apply normal_bound_agree, (chosen_environment vars s env us old g rho Us Env).
      * apply Correct.
  - intros env us v s vars Us Before Env old. exists old. split; [apply agree_symbols_refl|]. simpl. split; intros; tauto.
  - intros env us v s f fs q qs mid_v mid_s v' s' First IHfirst Rest IHrest vars Us Before Env old.
    destruct (trace_monotone _ _ _ _ _ _ _ _ First) as [Vars Symbols].
    assert (Before' : forall x, In x vars -> x<mid_v) by (intros x Hx; specialize (Before x Hx); lia).
    assert (Env' : Forall (term_depends mid_s (fun x => In x vars)) env).
    { apply (arguments_weaken s mid_s (fun x => In x vars) (fun x => In x vars) env); auto. }
    destruct (IHfirst vars Us Before Env old) as [middle [FirstAgree FirstCorrect]].
    destruct (IHrest vars Us Before' Env' middle) as [sk [RestAgree [ConjCorrect DisjCorrect]]].
    assert (HeadSymbols : universal_symbols mid_s q).
    { apply (proj1 trace_symbol_support env us v s f q mid_v mid_s First).
      - apply (arguments_weaken s s (fun x => In x vars) all_variables env); auto; intros; exact I.
      - rewrite Us. apply (arguments_weaken s s (fun x => In x vars) all_variables (map variable vars));
          auto using variables_depend; intros; exact I. }
    assert (HeadCorrect : forall rho, normal_holds functions predicates (environment old rho env) free f <-> universal_holds (literal sk) rho q).
    { intros rho. rewrite (FirstCorrect rho). apply HeadSymbols, agree_symbols_sym, RestAgree. }
    assert (ConjTail : forall rho, normal_holds functions predicates (environment old rho env) free (NConj fs) <-> universal_holds (literal sk) rho (UConj qs)).
    { intros rho. rewrite (normal_environment_agree (NConj fs) vars s env old middle rho Env (agree_symbols_sym s middle old FirstAgree)). apply ConjCorrect. }
    assert (DisjTail : forall rho, normal_holds functions predicates (environment old rho env) free (NDisj fs) <-> universal_holds (literal sk) rho (UDisj qs)).
    { intros rho. rewrite (normal_environment_agree (NDisj fs) vars s env old middle rho Env (agree_symbols_sym s middle old FirstAgree)). apply DisjCorrect. }
    exists sk. split.
    + apply (agree_symbols_trans s sk middle old); [apply (agree_symbols_weaken s mid_s); assumption|exact FirstAgree].
    + split; intros rho; simpl; [rewrite (HeadCorrect rho), (ConjTail rho)|rewrite (HeadCorrect rho), (DisjTail rho)]; reflexivity.
Qed.

Lemma empty_environment sk rho : forall i, environment sk rho [] i=default.
Proof. intros [|i]; reflexivity. Qed.
Theorem eliminate_quantifiers_model f r :
  eliminate_quantifiers visit apply variable witness predicate equality limit [] [] 0 0 f=Some r ->
  exists sk, forall rho,
    (normal_holds functions predicates free free f <-> universal_holds (literal sk) rho (supplied_value r)).
Proof.
  intros Accepted. apply eliminate_quantifiers_trace in Accepted.
  assert (Before : forall x, In x [] -> x<0) by (simpl; tauto).
  assert (Env : Forall (term_depends 0 (fun x => In x [])) []) by constructor.
  destruct (proj1 trace_model_extension [] [] 0 0 f _ _ _ Accepted [] eq_refl Before Env (fun _ _ => default)) as [sk [_ Correct]].
  exists sk. intros rho. specialize (Correct rho).
  rewrite (normal_bound_agree functions predicates f _ free free (empty_environment (fun _ _ => default) rho)) in Correct.
  exact Correct.
Qed.
Theorem eliminate_quantifiers_equisat f r :
  eliminate_quantifiers visit apply variable witness predicate equality limit [] [] 0 0 f=Some r ->
  (normal_holds functions predicates free free f <->
   exists sk, forall rho, universal_holds (literal sk) rho (supplied_value r)).
Proof.
  intros Accepted. split.
  - intros Original. destruct (eliminate_quantifiers_model f r Accepted) as [sk Correct].
    exists sk. intros rho. apply Correct, Original.
  - intros [sk Holds]. apply eliminate_quantifiers_trace in Accepted.
    assert (Before : forall x, In x [] -> x<0) by (simpl; tauto).
    assert (Env : Forall (term_depends 0 (fun x => In x [])) []) by constructor.
    pose proof (proj1 trace_model_projection [] [] 0 0 f _ _ _ Accepted [] eq_refl Before Env sk free (Holds free)) as Original.
    apply (normal_bound_agree functions predicates f _ free free (empty_environment sk free)) in Original. exact Original.
Qed.

Variable support : L -> list nat.
Hypothesis literal_support : forall sk l rho other,
  (forall v, In v (support l) -> rho v=other v) -> (literal sk rho l <-> literal sk other l).

Theorem normal_to_matrix_equisat f r m :
  eliminate_quantifiers visit apply variable witness predicate equality limit [] [] 0 0 f=Some r ->
  checked_universals support limit (supplied_value r)=Some m ->
  (normal_holds functions predicates free free f <->
   exists sk, forall rho, matrix_holds (literal sk rho) m).
Proof.
  intros Eliminate Scope. rewrite (eliminate_quantifiers_equisat f r Eliminate).
  split; intros [sk Holds]; exists sk.
  - apply (checked_universals_correct (literal sk) support (literal_support sk) excluded_middle limit _ m free Scope), Holds.
  - intros rho. apply (checked_universals_correct (literal sk) support (literal_support sk) excluded_middle limit _ m rho Scope), Holds.
Qed.
Theorem source_to_matrix_equisat source r m :
  eliminate_quantifiers visit apply variable witness predicate equality limit [] [] 0 0 (nnf true source)=Some r ->
  checked_universals support limit (supplied_value r)=Some m ->
  (source_holds functions predicates free free source <->
   exists sk, forall rho, matrix_holds (literal sk rho) m).
Proof.
  intros Eliminate Scope. pose proof (normal_to_matrix_equisat (nnf true source) r m Eliminate Scope) as Result.
  rewrite (nnf_correct functions predicates excluded_middle source true free free) in Result. exact Result.
Qed.
Theorem source_distributive_cnf_equisat source r m cnf_visit budget cs :
  eliminate_quantifiers visit apply variable witness predicate equality limit [] [] 0 0 (nnf true source)=Some r ->
  checked_universals support limit (supplied_value r)=Some m ->
  bounded_cnf cnf_visit budget m=Some cs ->
  (source_holds functions predicates free free source <->
   exists sk, forall rho, AxiomFuzzer.Preprocess.NormalForms.clauses_hold (literal sk rho) cs).
Proof.
  intros Eliminate Scope CNF. rewrite (source_to_matrix_equisat source r m Eliminate Scope).
  split; intros [sk Holds]; exists sk; intros rho;
    apply (bounded_cnf_correct (literal sk rho) m cnf_visit budget cs CNF), Holds.
Qed.
End Model.

Section DefinitionalPipeline.
Context {F P T A D : Type}.
Variable functions : F -> list D -> D.
Variable predicates : P -> list D -> Prop.
Variable default : D.
Variable apply : F -> list T -> T.
Variable variable : nat -> T.
Variable witness : nat -> list T -> T.
Variable predicate_atom : P -> list T -> A.
Variable equality_atom : T -> T -> A.
Variable eval : (nat -> list D -> D) -> (nat -> D) -> T -> D.
Variable base : (nat -> list D -> D) -> A -> (nat -> D) -> Prop.
Hypothesis eval_apply : forall sk rho f args, eval sk rho (apply f args)=functions f (map (eval sk rho) args).
Hypothesis eval_variable : forall sk rho v, eval sk rho (variable v)=rho v.
Hypothesis eval_witness : forall sk rho id args, eval sk rho (witness id args)=sk id (map (eval sk rho) args).
Hypothesis base_predicate : forall sk rho p args,
  base sk (predicate_atom p args) rho <-> predicates p (map (eval sk rho) args).
Hypothesis base_equality : forall sk rho x y, base sk (equality_atom x y) rho <-> eval sk rho x=eval sk rho y.
Variable support : A -> list nat.
Hypothesis base_support : forall sk a rho other,
  (forall v, In v (support a) -> rho v=other v) -> (base sk a rho <-> base sk a other).
Hypothesis excluded_middle : forall Q : Prop, Q \/ ~ Q.
Hypothesis functional_choice : forall R : list D -> D -> Prop,
  (forall args, exists x, R args x) -> exists g, forall args, R args (g args).

Let signed_predicate (sign : bool) p args := (sign, predicate_atom p args).
Let signed_equality (sign : bool) x y := (sign, equality_atom x y).
Let signed_literal sk rho (l : bool * A) := signed (fst l) (base sk (snd l) rho).
Let literal_variables (l : bool * A) := support (snd l).
Lemma signed_predicate_correct sk rho sign p args :
  signed_literal sk rho (signed_predicate sign p args) <-> signed sign (predicates p (map (eval sk rho) args)).
Proof. unfold signed_literal, signed_predicate; simpl. destruct sign; unfold signed; now rewrite base_predicate. Qed.
Lemma signed_equality_correct sk rho sign x y :
  signed_literal sk rho (signed_equality sign x y) <-> signed sign (eval sk rho x=eval sk rho y).
Proof. unfold signed_literal, signed_equality; simpl. destruct sign; unfold signed; now rewrite base_equality. Qed.
Lemma signed_support sk l rho other : (forall v, In v (literal_variables l) -> rho v=other v) ->
  (signed_literal sk rho l <-> signed_literal sk other l).
Proof.
  destruct l as [sign a]. unfold literal_variables, signed_literal; simpl. intros Agree.
  destruct sign; unfold signed; now rewrite (base_support sk a rho other Agree).
Qed.

Theorem source_definitional_cnf_equisat visit limit source r m lookup equal size budget root cs cnf_visit :
  (forall a b, equal a b=true -> a=b) ->
  eliminate_quantifiers visit apply variable witness signed_predicate signed_equality limit [] [] 0 0 (nnf true source)=Some r ->
  checked_universals literal_variables limit (supplied_value r)=Some m ->
  checked_definitions lookup cnf_visit equal support size budget m root=Some cs ->
  (source_holds functions predicates (fun _ => default) (fun _ => default) source <->
    exists sk aux, forall rho, AxiomFuzzer.Preprocess.NormalForms.clauses_hold (definition_holds (base sk) aux rho) cs).
Proof.
  intros Equal Eliminate Scope CNF.
  rewrite (source_to_matrix_equisat functions predicates default apply variable witness signed_predicate signed_equality
    eval signed_literal eval_apply eval_variable eval_witness signed_predicate_correct signed_equality_correct
    visit limit excluded_middle functional_choice literal_variables signed_support source r m Eliminate Scope).
  split.
  - intros [sk Matrix].
    destruct (proj1 (checked_definitions_equisat (base sk) excluded_middle lookup equal Equal support (base_support sk)
      default cnf_visit size budget m root cs CNF) Matrix) as [aux Clauses].
    exists sk, aux. exact Clauses.
  - intros [sk [aux Clauses]]. exists sk.
    apply (proj2 (checked_definitions_equisat (base sk) excluded_middle lookup equal Equal support (base_support sk)
      default cnf_visit size budget m root cs CNF)). exists aux. exact Clauses.
Qed.
End DefinitionalPipeline.
Print Assumptions trace_model_projection.
Print Assumptions trace_model_extension.
Print Assumptions eliminate_quantifiers_equisat.
Print Assumptions source_to_matrix_equisat.
Print Assumptions source_distributive_cnf_equisat.
Print Assumptions source_definitional_cnf_equisat.
