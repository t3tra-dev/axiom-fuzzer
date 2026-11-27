(* Syntax *)
From Stdlib Require Import List Bool Arith.PeanoNat.
From Stdlib Require Import FSets.FMapAVL FSets.FMapFacts Structures.OrderedTypeEx Lia.
Import ListNotations.
Scheme All for list.

Inductive term : Type := Var : nat -> term | Fun : nat -> list term -> term.
Definition term_eq_dec : forall x y : term, {x = y} + {x <> y}.
Proof.
  fix IH 1. decide equality; try apply Nat.eq_dec.
  apply list_eq_dec. exact IH.
Defined.
Inductive atom : Type := Pred : nat -> list term -> atom | Eq : term -> term -> atom.
Definition atom_eq_dec : forall x y : atom, {x = y} + {x <> y}.
Proof. decide equality; try apply term_eq_dec; try apply Nat.eq_dec.
  apply list_eq_dec. apply term_eq_dec.
Defined.
Definition literal := (bool * atom)%type.
Definition clause := list literal.
Definition term_eqb x y := if term_eq_dec x y then true else false.
Definition atom_eqb x y := if atom_eq_dec x y then true else false.
Definition atom_equiv x y :=
  atom_eqb x y || match x,y with
  | Eq s t, Eq u v => term_eqb s v && term_eqb t u
  | _,_ => false
  end.
Definition literal_equiv (x y : literal) := Bool.eqb (fst x) (fst y) && atom_equiv (snd x) (snd y).
Definition included (xs ys : clause) := forallb (fun x => existsb (literal_equiv x) ys) xs.
Fixpoint remove_at {A} (n : nat) (xs : list A) : list A :=
  match n,xs with 0,_::rest => rest | S n,x::rest => x::remove_at n rest | _,[] => [] end.
Definition replace_at {A} (n : nat) (x : A) (xs : list A) :=
  firstn n xs ++ x :: skipn (S n) xs.

(* Substitution *)
From Stdlib Require Import List.
Import ListNotations.
Definition substitution := list (nat * term).
(* Keep the original constant explicit: PeanoNat's alias has a different
   extraction directive when these definitions live in the same module. *)
Fixpoint lookup (s : substitution) (v : nat) : term :=
  match s with [] => Var v | (w,t)::rest => if Corelib.Init.Nat.eqb v w then t else lookup rest v end.
Fixpoint subst_term (s : substitution) (t : term) : term :=
  match t with Var v => lookup s v | Fun f ts => Fun f (map (subst_term s) ts) end.
Definition subst_atom s a := match a with
  | Pred p ts => Pred p (map (subst_term s) ts)
  | Eq x y => Eq (subst_term s x) (subst_term s y) end.
Definition subst_literal s (l : literal) : literal := (fst l,subst_atom s (snd l)).
Definition subst_clause s c := map (subst_literal s) c.

(* FOL *)
From Stdlib Require Import List Bool Logic.Classical_Prop.
Import ListNotations.
Section Semantics.
Context {D : Type} (functions : nat -> list D -> D) (predicates : nat -> list D -> Prop).
Fixpoint eval (rho : nat -> D) (t : term) : D :=
  match t with Var v => rho v | Fun f ts => functions f (map (eval rho) ts) end.
Definition atom_holds rho a := match a with
  | Pred p ts => predicates p (map (eval rho) ts) | Eq x y => eval rho x = eval rho y end.
Definition literal_holds rho (l : literal) :=
  if fst l then atom_holds rho (snd l) else ~ atom_holds rho (snd l).
Definition clause_holds rho c := exists l, In l c /\ literal_holds rho l.
Definition valid c := forall rho, clause_holds rho c.

Lemma term_substitution : forall t rho s,
  eval rho (subst_term s t) = eval (fun v => eval rho (lookup s v)) t.
Proof.
  fix IH 1. intros [v|f ts] rho s; simpl; [reflexivity|].
  f_equal. induction ts as [|t ts Hts]; simpl; [reflexivity|].
  rewrite IH, Hts. reflexivity.
Qed.
Lemma atom_substitution rho s a :
  atom_holds rho (subst_atom s a) <-> atom_holds (fun v => eval rho (lookup s v)) a.
Proof.
  destruct a as [p ts|x y]; unfold atom_holds, subst_atom; simpl.
  - assert (H : map (eval rho) (map (subst_term s) ts) = map (eval (fun v => eval rho (lookup s v))) ts).
    { induction ts; simpl; [reflexivity|]. rewrite term_substitution, IHts. reflexivity. }
    rewrite H. tauto.
  - rewrite !term_substitution. tauto.
Qed.
Lemma instance_valid c s : valid c -> valid (subst_clause s c).
Proof.
  intros H rho. destruct (H (fun v => eval rho (lookup s v))) as [l [Hin Hholds]].
  exists (subst_literal s l). split; [apply in_map; exact Hin|].
  destruct l as [b a]. unfold literal_holds, subst_literal; simpl.
  pose proof (atom_substitution rho s a). unfold literal_holds in Hholds.
  destruct b; simpl in *; tauto.
Qed.
Lemma atom_equiv_sound rho a b : atom_equiv a b = true -> (atom_holds rho a <-> atom_holds rho b).
Proof.
  unfold atom_equiv, atom_eqb. destruct (atom_eq_dec a b) as [H|H]; [subst; tauto|].
  simpl. destruct a as [p ts|s t], b as [q us|u v]; try discriminate.
  unfold term_eqb. destruct (term_eq_dec s v); [subst|discriminate].
  destruct (term_eq_dec t u); [subst|discriminate]. simpl; intros; split; symmetry; assumption.
Qed.
Lemma literal_equiv_sound rho a b : literal_equiv a b = true -> (literal_holds rho a <-> literal_holds rho b).
Proof.
  destruct a as [ba a], b as [bb b]. unfold literal_equiv; simpl.
  rewrite andb_true_iff. intros [Hb Ha]. apply Bool.eqb_prop in Hb. subst bb.
  pose proof (atom_equiv_sound rho a b Ha). destruct ba; unfold literal_holds; simpl; tauto.
Qed.
Lemma included_sound rho c d : included c d = true -> clause_holds rho c -> clause_holds rho d.
Proof.
  unfold included. rewrite forallb_forall. intros H [l [Hin Hl]].
  specialize (H l Hin). apply existsb_exists in H. destruct H as [k [Hk He]].
  exists k. split; [exact Hk|]. apply (literal_equiv_sound rho l k He). exact Hl.
Qed.
Lemma remove_member {A} (xs : list A) n pivot l :
  nth_error xs n = Some pivot -> In l xs -> l = pivot \/ In l (remove_at n xs).
Proof.
  revert n. induction xs as [|x xs IH]; intros [|n] H Hin; simpl in *; try discriminate.
  - inversion H; subst. destruct Hin; auto.
  - destruct Hin as [->|Hin]; [right;left;reflexivity|].
    destruct (IH n H Hin); auto.
Qed.
Lemma resolution_sound rho xs ys i j l r :
  nth_error xs i = Some l -> nth_error ys j = Some r ->
  fst l <> fst r -> atom_equiv (snd l) (snd r) = true ->
  clause_holds rho xs -> clause_holds rho ys -> clause_holds rho (remove_at i xs ++ remove_at j ys).
Proof.
  intros Hi Hj Hsign Heq [a [Ha HholdsA]] [b [Hb HholdsB]].
  destruct (remove_member xs i l a Hi Ha) as [->|Ha2];
  destruct (remove_member ys j r b Hj Hb) as [->|Hb2].
  - exfalso. pose proof (atom_equiv_sound rho (snd l) (snd r) Heq).
    destruct l as [bl al], r as [br ar]; destruct bl,br; simpl in *;
      unfold literal_holds in *; simpl in *; tauto.
  - exists b. split; [apply in_or_app;right;exact Hb2|exact HholdsB].
  - exists a. split; [apply in_or_app;left;exact Ha2|exact HholdsA].
  - exists a. split; [apply in_or_app;left;exact Ha2|exact HholdsA].
Qed.
End Semantics.

(* Certificate *)
From Stdlib Require Import List.
Import ListNotations.
Inductive term_context :=
  | Hole
  | Under : nat -> list term -> term_context -> list term -> term_context.
Fixpoint fill_term c t := match c with
  | Hole => t | Under f before c after => Fun f (before ++ fill_term c t :: after) end.
Inductive atom_context :=
  | In_pred : nat -> list term -> term_context -> list term -> atom_context
  | In_eq_left : term_context -> term -> atom_context
  | In_eq_right : term -> term_context -> atom_context.
Definition fill_atom c t := match c with
  | In_pred p before ctx after => Pred p (before ++ fill_term ctx t :: after)
  | In_eq_left ctx rhs => Eq (fill_term ctx t) rhs
  | In_eq_right lhs ctx => Eq lhs (fill_term ctx t) end.
Definition literal_context := (bool * atom_context)%type.
Definition fill_literal (c : literal_context) t : literal := (fst c,fill_atom (snd c) t).
Inductive rule :=
  | Input : nat -> rule
  | Instance : nat -> substitution -> rule
  | Copy : nat -> rule
  | Resolve : nat -> nat -> nat -> nat -> rule
  | Equality_resolve : nat -> nat -> rule
  | Paramodulate : nat -> nat -> bool -> nat -> nat -> literal_context -> rule
  | Equality_factor : nat -> nat -> bool -> nat -> bool -> rule.
Definition step := (rule * clause)%type.
Definition certificate := list step.

(* Checker *)
From Stdlib Require Import List Bool.
Import ListNotations.
Module ClauseMap := FMapAVL.Make Nat_as_OT.
Module ClauseFacts := FMapFacts.WFacts_fun Nat_as_OT ClauseMap.
(* Instance steps can bind every variable of a long clause. Above 32 bindings, an AVL
   index of the bindings replaces lookup's scan at each variable occurrence. The first
   binding of a variable wins, as in lookup. *)
Fixpoint substitution_index (s : substitution) : ClauseMap.t term := match s with
  | [] => ClauseMap.empty term
  | (w,t)::rest => ClauseMap.add w t (substitution_index rest) end.
Definition indexed_lookup (index : ClauseMap.t term) v :=
  match ClauseMap.find v index with Some t => t | None => Var v end.
Lemma indexed_lookup_correct s v : indexed_lookup (substitution_index s) v=lookup s v.
Proof.
  unfold indexed_lookup. induction s as [|[w t] rest IH]; cbn [substitution_index lookup].
  - now rewrite ClauseFacts.empty_o.
  - rewrite ClauseFacts.add_o. destruct (ClauseFacts.eq_dec w v) as [Same|Different];
      destruct (Corelib.Init.Nat.eqb v w) eqn:E; try reflexivity.
    + apply Nat.eqb_neq in E. hnf in Same. congruence.
    + apply Nat.eqb_eq in E. hnf in Different. congruence.
    + exact IH.
Qed.
Fixpoint subst_term_with (look : nat -> term) (t : term) : term :=
  match t with Var v => look v | Fun f ts => Fun f (map (subst_term_with look) ts) end.
Lemma subst_term_with_lookup look s : (forall v, look v=lookup s v) ->
  forall t, subst_term_with look t=subst_term s t.
Proof.
  intros Same. fix IH 1. intros [v|f ts]; simpl; [apply Same|]. f_equal.
  induction ts as [|t ts Hts]; simpl; [reflexivity|]. now rewrite IH, Hts.
Qed.
Definition subst_atom_with look a := match a with
  | Pred p ts => Pred p (map (subst_term_with look) ts)
  | Eq x y => Eq (subst_term_with look x) (subst_term_with look y) end.
Definition fast_subst_clause (s : substitution) (c : clause) : clause :=
  if length s <=? 32 then subst_clause s c else
  let index := substitution_index s in
  map (fun l : literal => (fst l,subst_atom_with (indexed_lookup index) (snd l))) c.
Lemma fast_subst_clause_correct s c : fast_subst_clause s c=subst_clause s c.
Proof.
  unfold fast_subst_clause. destruct (length s <=? 32); [reflexivity|]. cbv zeta.
  unfold subst_clause. apply map_ext. intros [b a]. unfold subst_literal; simpl. f_equal.
  pose proof (subst_term_with_lookup (indexed_lookup (substitution_index s)) s
    (indexed_lookup_correct s)) as Same.
  destruct a as [p ts|x y]; simpl; [f_equal; apply map_ext; exact Same|now rewrite !Same].
Qed.
(* Storage-independent rule evaluation. The trusted replay below uses pure
   list lookups; native proof elaboration can propose steps using array lookups
   without duplicating the rules. Its output still passes the complete replay. *)
Definition infer_with (input parent : nat -> option clause) (r : rule) : option clause :=
  match r with
  | Input i => input i
  | Instance p s => match parent p with Some c => Some (fast_subst_clause s c) | _ => None end
  | Copy p => parent p
  | Resolve p i q j =>
    match parent p, parent q with
    | Some xs,Some ys =>
      match nth_error xs i,nth_error ys j with
      | Some l,Some r => if negb (Bool.eqb (fst l) (fst r)) && atom_equiv (snd l) (snd r)
        then Some (remove_at i xs ++ remove_at j ys) else None
      | _,_ => None end
    | _,_ => None end
  | Equality_resolve p i =>
    match parent p with
    | Some xs => match nth_error xs i with
      | Some (false, Eq x y) => if term_eqb x y then Some (remove_at i xs) else None
      | _ => None end
    | None => None end
  | Paramodulate p i reverse q j context =>
    match parent p,parent q with
    | Some xs,Some ys =>
      match nth_error xs i,nth_error ys j with
      | Some (true,Eq x y),Some target =>
        let lhs := if reverse then y else x in
        let rhs := if reverse then x else y in
        if literal_equiv target (fill_literal context lhs)
        then Some (remove_at i xs ++ replace_at j (fill_literal context rhs) ys) else None
      | _,_ => None end
    | _,_ => None end
  | Equality_factor p i reverse_i j reverse_j =>
    match parent p with
    | Some xs => match nth_error xs i,nth_error xs j with
      | Some (true,Eq s t),Some (true,Eq u v) =>
        let lhs := if reverse_i then t else s in
        let rhs := if reverse_i then s else t in
        let lhs' := if reverse_j then v else u in
        let rhs' := if reverse_j then u else v in
        if term_eqb lhs lhs'
        then Some ((false,Eq rhs rhs') :: (true,Eq u v) :: remove_at i xs)
        else None
      | _,_ => None end
    | None => None end
  end.
Definition infer (inputs db : list clause) : rule -> option clause :=
  infer_with (nth_error inputs) (nth_error db).
Fixpoint replay (inputs db : list clause) (steps : certificate) : option (list clause) :=
  match steps with
  | [] => Some db
  | (r,c)::rest => match infer inputs db r with
    | Some expected => if included expected c then replay inputs (db ++ [c]) rest else None
    | None => None end
  end.
Definition check_list inputs steps := match replay inputs [] steps with
  | Some db => existsb (fun c => match c with [] => true | _ => false end) db
  | None => false end.

(* Persistent indexed storage. The list replay remains the specification; the
   extracted acceptance path does no append or linear parent/input lookup. *)
Fixpoint index_from {A} (xs : list A) offset : ClauseMap.t A := match xs with
  | [] => ClauseMap.empty A
  | x::xs => ClauseMap.add offset x (index_from xs (S offset)) end.
Lemma index_from_spec {A} (xs : list A) : forall offset i,
  ClauseMap.find i (index_from xs offset)=
    if offset <=? i then nth_error xs (i-offset) else None.
Proof.
  induction xs as [|x xs IH]; intros offset i; simpl.
  - rewrite ClauseFacts.empty_o. destruct (offset <=? i); [now destruct (i-offset)|reflexivity].
  - destruct (Nat.eq_dec offset i) as [<-|Different].
    + rewrite ClauseFacts.add_eq_o by reflexivity. rewrite Nat.leb_refl,Nat.sub_diag; reflexivity.
    + rewrite ClauseFacts.add_neq_o by exact Different. rewrite IH.
      destruct (Nat.leb_spec0 offset i) as [Le|Lt].
      * replace (S offset <=? i) with true by (symmetry; apply Nat.leb_le; lia).
        replace (i-offset) with (S (i-S offset)) by lia. reflexivity.
      * replace (S offset <=? i) with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
Qed.
Definition cached {A} (xs : list A) : nat -> option A :=
  let table := index_from xs 0 in fun i => ClauseMap.find i table.
Lemma cached_correct {A} (xs : list A) i : cached xs i=nth_error xs i.
Proof. unfold cached. rewrite index_from_spec; simpl. now rewrite Nat.sub_0_r. Qed.
Definition empty_clause (c : clause) := match c with [] => true | _ => false end.
Fixpoint replay_indexed input (db : ClauseMap.t clause) next found steps := match steps with
  | [] => found
  | (r,c)::rest => match infer_with input (fun i => ClauseMap.find i db) r with
      | Some expected => if included expected c then
          replay_indexed input (ClauseMap.add next c db) (S next) (found || empty_clause c) rest
        else false
      | None => false end end.
Definition check inputs steps := replay_indexed (cached inputs) (ClauseMap.empty clause) 0 false steps.
Lemma indexed_snoc {A} (xs : list A) db c :
  (forall i, ClauseMap.find i db=nth_error xs i) ->
  forall i, ClauseMap.find i (ClauseMap.add (length xs) c db)=nth_error (xs++[c]) i.
Proof.
  intros Same i. destruct (Nat.eq_dec (length xs) i) as [<-|Different].
  - rewrite ClauseFacts.add_eq_o by reflexivity. rewrite nth_error_app2 by lia.
    now rewrite Nat.sub_diag.
  - rewrite ClauseFacts.add_neq_o by exact Different. rewrite Same.
    destruct (Nat.ltb_spec0 i (length xs)) as [Lt|Ge].
    + rewrite nth_error_app1 by exact Lt; reflexivity.
    + rewrite nth_error_app2 by lia.
      assert (Empty : nth_error xs i=None) by (apply nth_error_None; lia).
      rewrite Empty. destruct (i-length xs) eqn:N; [lia|now destruct n].
Qed.
Lemma replay_indexed_correct inputs steps : forall prefix db,
  (forall i, ClauseMap.find i db=nth_error prefix i) ->
  replay_indexed (cached inputs) db (length prefix) (existsb empty_clause prefix) steps=
  match replay inputs prefix steps with Some result => existsb empty_clause result | None => false end.
Proof.
  induction steps as [|[r c] steps IH]; intros prefix db Same; simpl; [reflexivity|].
  assert (Infer : infer_with (cached inputs) (fun i => ClauseMap.find i db) r=infer inputs prefix r).
  { unfold infer,infer_with. destruct r; repeat rewrite cached_correct; repeat rewrite Same; reflexivity. }
  rewrite Infer. destruct (infer inputs prefix r) as [expected|]; [|reflexivity].
  destruct (included expected c); [|reflexivity].
  replace (S (length prefix)) with (length (prefix++[c])) by (rewrite length_app; simpl; lia).
  replace (existsb empty_clause prefix || empty_clause c) with (existsb empty_clause (prefix++[c]))
    by (rewrite existsb_app; simpl; now rewrite Bool.orb_false_r).
  apply IH,indexed_snoc,Same.
Qed.
Theorem check_correct inputs steps : check inputs steps=check_list inputs steps.
Proof.
  unfold check,check_list. change (replay_indexed (cached inputs) (ClauseMap.empty clause)
    (length (@nil clause)) (existsb empty_clause []) steps =
    match replay inputs [] steps with Some db => existsb empty_clause db | None => false end).
  rewrite (replay_indexed_correct inputs steps [] (ClauseMap.empty clause));
    [reflexivity|intros i; rewrite ClauseFacts.empty_o; now destruct i].
Qed.

(* Soundness *)
From Stdlib Require Import List Bool Logic.Classical_Prop.
Import ListNotations.
Section Soundness.
Context {D : Type} (functions : nat -> list D -> D) (predicates : nat -> list D -> Prop).
Local Abbreviation holds := (clause_holds functions predicates).
(* Double-negation validity suffices for refutation soundness and lets equality
   factoring be proved constructively, without decidable domain equality or a
   classical axiom. The final theorem still assumes ordinary valid inputs. *)
Local Abbreviation valid := (fun c => forall rho, ~ ~ holds rho c).
Local Abbreviation ev := (eval functions).
Local Abbreviation lh := (literal_holds functions predicates).

Lemma fill_term_equal rho c s t : ev rho s = ev rho t -> ev rho (fill_term c s) = ev rho (fill_term c t).
Proof.
  intros H. induction c; simpl; [exact H|]. f_equal.
  rewrite !map_app. simpl. rewrite IHc. reflexivity.
Qed.
Lemma fill_literal_equal rho c s t : ev rho s = ev rho t -> (lh rho (fill_literal c s) <-> lh rho (fill_literal c t)).
Proof.
  intros H. destruct c as [b ctx]. unfold fill_literal, literal_holds; simpl.
  assert (Ha : atom_holds functions predicates rho (fill_atom ctx s) <-> atom_holds functions predicates rho (fill_atom ctx t)).
  { destruct ctx as [p before context after|context rhs|lhs context]; unfold fill_atom, atom_holds; simpl;
      rewrite ?map_app; simpl; rewrite (fill_term_equal rho context s t H); tauto. }
  destruct b; tauto.
Qed.
Lemma nth_valid (db : list clause) i c : Forall valid db -> nth_error db i = Some c -> valid c.
Proof.
  intros H Hin. assert (Hin2 : In c db) by (eapply nth_error_In; eauto).
  exact (proj1 (Forall_forall valid db) H c Hin2).
Qed.
Lemma replace_member {A} (xs : list A) n old new l :
  nth_error xs n = Some old -> In l xs -> l = old \/ In l (replace_at n new xs).
Proof.
  revert n. induction xs as [|x xs IH]; intros [|n] H Hin; simpl in *; try discriminate.
  - inversion H; subst. destruct Hin; [left;congruence|right;right;assumption].
  - destruct Hin as [->|Hin]; [right;left;reflexivity|].
    destruct (IH n H Hin); [left;assumption|right;right;assumption].
Qed.
Lemma replaced_present {A} (xs : list A) n old new : nth_error xs n = Some old -> In new (replace_at n new xs).
Proof. intros H. unfold replace_at. apply in_or_app. right. left. reflexivity. Qed.
Lemma infer_sound (inputs db : list clause) (r : rule) (expected : clause) :
  Forall valid inputs -> Forall valid db -> infer inputs db r = Some expected -> valid expected.
Proof.
  intros Hinputs Hdb H.
  destruct r as [i|p s|p|p i q j|p i|p i rev q j ctx|p i rev_i j rev_j]; simpl in H.
  - exact (nth_valid inputs i expected Hinputs H).
  - destruct (nth_error db p) as [c|] eqn:Hp; try rewrite Hp in H; try discriminate.
    inversion H; subst. rewrite fast_subst_clause_correct. intros rho Hnot.
    apply (nth_valid db p c Hdb Hp (fun v => ev rho (lookup s v))).
    intros [l [Hin Hholds]]. apply Hnot.
    exists (subst_literal s l). split; [apply in_map;exact Hin|].
    destruct l as [b a]. unfold literal_holds, subst_literal; simpl.
    pose proof (atom_substitution functions predicates rho s a).
    unfold literal_holds in Hholds. destruct b; simpl in *; tauto.
  - exact (nth_valid db p expected Hdb H).
  - destruct (nth_error db p) as [xs|] eqn:Hp; try rewrite Hp in H; try discriminate.
    destruct (nth_error db q) as [ys|] eqn:Hq; try rewrite Hq in H; try discriminate.
    destruct (nth_error xs i) as [l|] eqn:Hi; try rewrite Hi in H; try discriminate.
    destruct (nth_error ys j) as [r|] eqn:Hj; try rewrite Hj in H; try discriminate.
    destruct (negb (Bool.eqb (fst l) (fst r)) && atom_equiv (snd l) (snd r)) eqn:Htest; try rewrite Htest in H; try discriminate.
    inversion H; subst. apply andb_true_iff in Htest. destruct Htest as [Hsign Heq].
    apply negb_true_iff in Hsign. intros rho Hnot.
    apply (nth_valid db p xs Hdb Hp rho). intro Hxs.
    apply (nth_valid db q ys Hdb Hq rho). intro Hys.
    apply Hnot. eapply resolution_sound; eauto.
    + intro E. rewrite E, Bool.eqb_reflx in Hsign. discriminate.
  - destruct (nth_error db p) as [xs|] eqn:Hp; try rewrite Hp in H; try discriminate.
    destruct (nth_error xs i) as [[b a]|] eqn:Hi; try rewrite Hi in H; try discriminate.
    destruct b; try discriminate. destruct a as [f ts|x y]; try discriminate.
    unfold term_eqb in H. destruct (term_eq_dec x y); try discriminate. subst y.
    inversion H; subst. intros rho Hnot.
    apply (nth_valid db p xs Hdb Hp rho). intros [l [Hin Hl]].
    destruct (remove_member xs i (false,Eq x x) l Hi Hin) as [->|Hin2].
    + unfold literal_holds, atom_holds in Hl; simpl in Hl. contradiction Hl. reflexivity.
    + apply Hnot. exists l; auto.
  - destruct (nth_error db p) as [xs|] eqn:Hp; try rewrite Hp in H; try discriminate.
    destruct (nth_error db q) as [ys|] eqn:Hq; try rewrite Hq in H; try discriminate.
    destruct (nth_error xs i) as [[b a]|] eqn:Hi; try rewrite Hi in H; try discriminate.
    destruct b; try discriminate. destruct a as [f ts|x y]; try discriminate.
    destruct (nth_error ys j) as [target|] eqn:Hj; try rewrite Hj in H; try discriminate.
    destruct (literal_equiv target (fill_literal ctx (if rev then y else x))) eqn:Hmatch; try rewrite Hmatch in H; try discriminate.
    inversion H; subst. intros rho Hnot.
    apply (nth_valid db p xs Hdb Hp rho). intros [l [Hin Hl]].
    destruct (remove_member xs i (true,Eq x y) l Hi Hin) as [->|Hin2].
    + assert (E : ev rho (if rev then y else x) = ev rho (if rev then x else y)).
      { unfold literal_holds, atom_holds in Hl; simpl in Hl. destruct rev; simpl; auto. }
      apply (nth_valid db q ys Hdb Hq rho). intros [k [Hk Hholds]].
      destruct (replace_member ys j target (fill_literal ctx (if rev then x else y)) k Hj Hk) as [->|Hk2].
      * apply Hnot. exists (fill_literal ctx (if rev then x else y)). split.
        -- apply in_or_app. right. eapply replaced_present; eauto.
        -- apply (fill_literal_equal rho ctx _ _ E).
           apply (literal_equiv_sound functions predicates rho _ _ Hmatch). exact Hholds.
      * apply Hnot. exists k. split; [apply in_or_app;right;exact Hk2|exact Hholds].
    + apply Hnot. exists l. split; [apply in_or_app;left;exact Hin2|exact Hl].
  - destruct (nth_error db p) as [xs|] eqn:Hp; try rewrite Hp in H; try discriminate.
    destruct (nth_error xs i) as [[bi ai]|] eqn:Hi; try rewrite Hi in H; try discriminate.
    destruct bi; try discriminate. destruct ai as [f args|s t]; try discriminate.
    destruct (nth_error xs j) as [[bj aj]|] eqn:Hj; try rewrite Hj in H; try discriminate.
    destruct bj; try discriminate. destruct aj as [f args|u v]; try discriminate.
    unfold term_eqb in H.
    destruct (term_eq_dec (if rev_i then t else s) (if rev_j then v else u)) as [E|]; try discriminate.
    inversion H; subst. intros rho Hnot.
    apply (nth_valid db p xs Hdb Hp rho). intros [l [Hin Hl]].
    destruct (remove_member xs i (true,Eq s t) l Hi Hin) as [->|Hin2].
    + apply Hnot. exists (false,Eq (if rev_i then s else t) (if rev_j then u else v)).
      split; [left;reflexivity|]. unfold literal_holds, atom_holds; simpl. intro Erhs.
      apply Hnot. exists (true,Eq u v). split; [right;left;reflexivity|].
      unfold literal_holds, atom_holds in *; simpl in *.
      assert (Elhs : ev rho (if rev_i then t else s) = ev rho (if rev_j then v else u)) by now rewrite E.
      destruct rev_i,rev_j; simpl in *; congruence.
    + apply Hnot. exists l. split; [right;right;exact Hin2|exact Hl].
Qed.
Lemma replay_sound (inputs : list clause) (steps : certificate) (db result : list clause) :
  Forall valid inputs -> Forall valid db -> replay inputs db steps = Some result -> Forall valid result.
Proof.
  revert db result. induction steps as [|[r c] rest IH]; intros db result Hinputs Hdb H; simpl in H.
  - inversion H; subst; assumption.
  - destruct (infer inputs db r) as [expected|] eqn:Hinfer; try discriminate.
    destruct (included expected c) eqn:Hinc; try discriminate.
    apply (IH (db ++ [c]) result Hinputs); [|exact H].
    apply Forall_app. split; [exact Hdb|]. constructor; [|constructor].
    intros rho Hnot. apply (infer_sound inputs db r expected Hinputs Hdb Hinfer rho).
    intro Hholds. apply Hnot. eapply included_sound; eauto.
Qed.
Theorem check_sound (inputs : list clause) (steps : certificate) : check inputs steps = true ->
  forall (inhabitant : D), ~ Forall (AxiomFuzzer.Clause.Kernel.valid functions predicates) inputs.
Proof.
  rewrite check_correct. unfold check_list. destruct (replay inputs [] steps) as [db|] eqn:Hreplay; try discriminate.
  intros Hcheck inhabitant Hinputs. apply existsb_exists in Hcheck.
  destruct Hcheck as [c [Hin Hempty]]. destruct c; try discriminate.
  assert (Hsafe : Forall valid inputs).
  { eapply Forall_impl; [|exact Hinputs]. intros c Hc rho Hnot. apply Hnot. apply Hc. }
  pose proof (replay_sound inputs steps [] db Hsafe (Forall_nil _) Hreplay) as Hvalid.
  apply Forall_forall with (x:=[]) in Hvalid; [|exact Hin].
  apply (Hvalid (fun _ => inhabitant)). intros [l [H _]]. contradiction.
Qed.
End Soundness.
Print Assumptions check_sound.
Print Assumptions check_correct.
Print Assumptions cached_correct.
Print Assumptions fast_subst_clause_correct.
