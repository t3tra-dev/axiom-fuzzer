(* Finite authority witnesses, natural-deduction certificates, and completeness. *)
From Stdlib Require Import List Bool Arith.PeanoNat String.
Require Import AxiomFuzzer.Source.Language AxiomFuzzer.Source.Validation AxiomFuzzer.Reference.Encoding.
Import ListNotations.
Local Open Scope list_scope.
Inductive permission :=
  | FixedPermission (index : nat)
  | SchemaPermission (key : schema) (variables : list nat) (fresh : nat) (condition : formula)
  | RegisteredPermission (name revision data : string) (formula : formula)
  | EquivalentPermission (parent : permission) (formula : formula).
Fixpoint authorize (t : theory) (p : permission) : option formula := match p with
  | FixedPermission i => option_map axiom_formula (nth_error (fixed_axioms t) i)
  | SchemaPermission key variables fresh phi =>
      if admitted (allowed_schemas t) key && signature_ok t phi then
        match builtin key with Some kind => checked_schema kind "member"%string variables fresh phi | None => None end
      else None
  | RegisteredPermission n r data f =>
      if admitted (allowed_schemas t) (RegisteredSchema n r) && formula_scoped 0 true f &&
         signature_ok t f && registered_check t n r data f
      then Some f else None
  | EquivalentPermission p f => match authorize t p with
      | Some a => if equivalent a f then Some f else None | None => None end
  end.
Lemma admitted_complete schemas key : In key schemas -> admitted schemas key=true.
Proof.
  intros In. unfold admitted. apply existsb_exists. exists key; split; [exact In|].
  destruct key; simpl; try reflexivity. now rewrite !String.eqb_refl.
Qed.
Theorem authorize_sound t p f : authorize t p=Some f -> authorized t f.
Proof.
  revert f; induction p; intros f; cbn [authorize].
  - destruct (nth_error (fixed_axioms t) index) as [a|] eqn:Ax; [|discriminate].
    intros H; inversion H; subst. apply AuthorizedFixed. now apply nth_error_In in Ax.
  - destruct (_ && _) eqn:Valid; [|discriminate]. apply andb_true_iff in Valid as [Allowed Signature].
    destruct (builtin key) as [kind|] eqn:Kind; [|discriminate]. intros Expansion.
    eapply (AuthorizedSchema t key kind variables fresh condition f); [now apply admitted_sound in Allowed|exact Kind|exact Signature|exact Expansion].
  - destruct (_ && _) eqn:Valid; [|discriminate].
    rewrite !andb_true_iff in Valid. destruct Valid as [[[Allowed Scope] Signature] Checked].
    intros H; inversion H; subst. eapply (AuthorizedRegistered t name revision data f);
      [now apply admitted_sound in Allowed|exact Scope|exact Signature|exact Checked].
  - destruct (authorize t p) as [a|] eqn:Parent; [|discriminate].
    destruct (equivalent a formula) eqn:Equivalent; [|discriminate].
    intros H; inversion H; subst. eapply AuthorizedEquivalent; [now apply IHp|exact Equivalent].
Qed.
Theorem authorize_complete t f : authorized t f -> exists p, authorize t p=Some f.
Proof.
  induction 1.
  - apply In_nth_error in H as [i Ax]. exists (FixedPermission i); simpl; now rewrite Ax.
  - exists (SchemaPermission key variables fresh phi); simpl.
    rewrite (admitted_complete _ _ H),H0,H1; simpl; exact H2.
  - exists (RegisteredPermission name revision data f); simpl.
    now rewrite (admitted_complete _ _ H),H0,H1,H2.
  - destruct IHauthorized as [p Parent]. exists (EquivalentPermission p b); simpl; now rewrite Parent,H0.
Qed.
Fixpoint permission_code p := match p with
  | FixedPermission i => Pair (Number 0) (Number i)
  | SchemaPermission key variables fresh phi => Pair (Number 1)
      (Pair (schema_code key) (Pair (list_code Number variables) (Pair (Number fresh) (source_code phi))))
  | RegisteredPermission n r data f => Pair (Number 2)
      (Pair (string_code n) (Pair (string_code r) (Pair (string_code data) (source_code f))))
  | EquivalentPermission p f => Pair (Number 3) (Pair (permission_code p) (source_code f)) end.
Fixpoint permission_value c := match c with
  | Pair (Number 0) (Number i) => Some (FixedPermission i)
  | Pair (Number 1) (Pair key (Pair variables (Pair (Number fresh) phi))) =>
      match schema_value key,list_value number_value variables,source_value phi with
      | Some key,Some variables,Some phi => Some (SchemaPermission key variables fresh phi) | _,_,_ => None end
  | Pair (Number 2) (Pair n (Pair r (Pair data f))) =>
      match string_value n,string_value r,string_value data,source_value f with
      | Some n,Some r,Some data,Some f => Some (RegisteredPermission n r data f) | _,_,_,_ => None end
  | Pair (Number 3) (Pair p f) => match permission_value p,source_value f with
      | Some p,Some f => Some (EquivalentPermission p f) | _,_ => None end
  | _ => None end.
Lemma permission_roundtrip p : permission_value (permission_code p)=Some p.
Proof.
  induction p; simpl; try reflexivity.
  - rewrite schema_roundtrip, (list_roundtrip Number number_value (fun _ => eq_refl)), source_roundtrip; reflexivity.
  - now rewrite !string_roundtrip, source_roundtrip.
  - now rewrite IHp,source_roundtrip.
Qed.
Print Assumptions authorize_complete.

Require Import AxiomFuzzer.Source.Standard AxiomFuzzer.Logic.Deduction.
Local Set Implicit Arguments.
Definition fol_term_code := Syntax.term_code.
Definition fol_term_value := Syntax.term_value.
Definition fol_formula_code := form_code.
Definition fol_formula_value := form_value.

Inductive equality_witness :=
  | Refl (t : Syntax.term) | Sym (t u : Syntax.term) | Trans (t u v : Syntax.term)
  | Function (f : string) (xs ys : list Syntax.term) | Predicate (p : string) (xs ys : list Syntax.term).
Definition equality_formula w : form := match w with
  | Refl t => Standard.equal t t
  | Sym t u => Imp (Standard.equal t u) (Standard.equal u t)
  | Trans t u v => Imp (Standard.equal t u) (Imp (Standard.equal u v) (Standard.equal t v))
  | Function f xs ys => Imp (equal_arguments xs ys) (Standard.equal (Fun f xs) (Fun f ys))
  | Predicate p xs ys => Imp (equal_arguments xs ys) (Imp (named_predicate p xs) (named_predicate p ys)) end.
Lemma equality_formula_sound w : equality_axiom (equality_formula w).
Proof. destruct w; constructor. Qed.
Lemma equality_formula_complete f : equality_axiom f -> exists w, equality_formula w=f.
Proof. destruct 1; [exists (Refl t)|exists (Sym t u)|exists (Trans t u v)|exists (Function f xs ys)|exists (Predicate p xs ys)]; reflexivity. Qed.
Definition equality_code w := match w with
  | Refl t => Pair (Number 0) (fol_term_code t)
  | Sym t u => Pair (Number 1) (Pair (fol_term_code t) (fol_term_code u))
  | Trans t u v => Pair (Number 2) (Pair (fol_term_code t) (Pair (fol_term_code u) (fol_term_code v)))
  | Function f xs ys => Pair (Number 3) (Pair (string_code f) (Pair (list_code fol_term_code xs) (list_code fol_term_code ys)))
  | Predicate p xs ys => Pair (Number 4) (Pair (string_code p) (Pair (list_code fol_term_code xs) (list_code fol_term_code ys))) end.
Definition equality_value c := match c with
  | Pair (Number 0) t => option_map Refl (fol_term_value t)
  | Pair (Number 1) (Pair t u) => match fol_term_value t,fol_term_value u with Some t,Some u => Some (Sym t u) | _,_ => None end
  | Pair (Number 2) (Pair t (Pair u v)) => match fol_term_value t,fol_term_value u,fol_term_value v with Some t,Some u,Some v => Some (Trans t u v) | _,_,_ => None end
  | Pair (Number 3) (Pair f (Pair xs ys)) => match string_value f,list_value fol_term_value xs,list_value fol_term_value ys with Some f,Some xs,Some ys => Some (Function f xs ys) | _,_,_ => None end
  | Pair (Number 4) (Pair p (Pair xs ys)) => match string_value p,list_value fol_term_value xs,list_value fol_term_value ys with Some p,Some xs,Some ys => Some (Predicate p xs ys) | _,_,_ => None end
  | _ => None end.
Lemma equality_roundtrip w : equality_value (equality_code w)=Some w.
Proof.
  destruct w; simpl; rewrite ?Syntax.term_roundtrip, ?string_roundtrip,
    ?(list_roundtrip _ _ Syntax.term_roundtrip); reflexivity.
Qed.
Definition axiom_at t c : option form := match c with
  | Pair (Number 0) p => match permission_value p with Some p => option_map source_sentence (authorize t p) | None => None end
  | Pair (Number 1) w => option_map (fun w => close (equality_formula w)) (equality_value w)
  | _ => None end.
Lemma axiom_at_sound t c f : axiom_at t c=Some f -> source_theory t f.
Proof.
  unfold axiom_at. destruct c as [n|tag payload]; [discriminate|].
  destruct tag as [n|x y]; [|discriminate]. destruct n as [|[|n]]; [| |discriminate].
  - destruct (permission_value payload) as [p|] eqn:P; [|discriminate].
    destruct (authorize t p) as [a|] eqn:A; [|discriminate].
    intros H; inversion H; subst. right; exists a; split; [now apply authorize_sound in A|reflexivity].
  - destruct (equality_value payload) as [w|] eqn:W; [|discriminate].
    intros H; inversion H; subst. left; exists (equality_formula w); split; [apply equality_formula_sound|reflexivity].
Qed.
Lemma axiom_at_complete t f : source_theory t f -> exists c, axiom_at t c=Some f.
Proof.
  intros [[a [Equality ->]]|[a [Allowed ->]]].
  - destruct (equality_formula_complete Equality) as [w <-]. exists (Pair (Number 1) (equality_code w)).
    unfold axiom_at; now rewrite equality_roundtrip.
  - destruct (authorize_complete t a Allowed) as [p Authorized]. exists (Pair (Number 0) (permission_code p)).
    unfold axiom_at; now rewrite permission_roundtrip,Authorized.
Qed.

Require Import AxiomFuzzer.Reference.Encoding AxiomFuzzer.Reference.Enumeration AxiomFuzzer.Source.Kernel AxiomFuzzer.Wire.Refutation.
From Stdlib Require Import List Bool String.
Import ListNotations.
Local Open Scope list_scope.
Local Set Implicit Arguments.

Fixpoint proof_code (p : proof) := match p with
  | Assume n => Pair (Number 0) (Number n)
  | ImplicationIntroduction a p => Pair (Number 1) (Pair (fol_formula_code a) (proof_code p))
  | ImplicationElimination p q => Pair (Number 2) (Pair (proof_code p) (proof_code q))
  | UniversalIntroduction p => Pair (Number 3) (proof_code p)
  | UniversalElimination t p => Pair (Number 4) (Pair (fol_term_code t) (proof_code p))
  | Explosion a p => Pair (Number 5) (Pair (fol_formula_code a) (proof_code p))
  | Peirce a b => Pair (Number 6) (Pair (fol_formula_code a) (fol_formula_code b)) end.
Fixpoint proof_value c : option proof := match c with
  | Pair (Number 0) (Number n) => Some (Assume n)
  | Pair (Number 1) (Pair a p) => match fol_formula_value a,proof_value p with Some a,Some p => Some (ImplicationIntroduction a p) | _,_ => None end
  | Pair (Number 2) (Pair p q) => match proof_value p,proof_value q with Some p,Some q => Some (ImplicationElimination p q) | _,_ => None end
  | Pair (Number 3) p => option_map UniversalIntroduction (proof_value p)
  | Pair (Number 4) (Pair t p) => match fol_term_value t,proof_value p with Some t,Some p => Some (UniversalElimination t p) | _,_ => None end
  | Pair (Number 5) (Pair a p) => match fol_formula_value a,proof_value p with Some a,Some p => Some (Explosion a p) | _,_ => None end
  | Pair (Number 6) (Pair a b) => match fol_formula_value a,fol_formula_value b with Some a,Some b => Some (Peirce a b) | _,_ => None end
  | _ => None end.
Lemma proof_roundtrip p : proof_value (proof_code p)=Some p.
Proof. induction p; simpl; now rewrite ?form_roundtrip, ?Syntax.term_roundtrip, ?IHp, ?IHp1, ?IHp2. Qed.
Definition certificate_code (c : @Deduction.certificate code) :=
  Pair (list_code (fun x => x) (assumptions c)) (proof_code (deduction c)).
Definition certificate_value c := match c with
  | Pair ids p => match list_value (fun x => Some x) ids,proof_value p with
      | Some ids,Some p => Some {| assumptions:=ids; deduction:=p |} | _,_ => None end
  | _ => None end.
Lemma certificate_roundtrip c : certificate_value (certificate_code c)=Some c.
Proof. destruct c; unfold certificate_code,certificate_value; simpl.
  rewrite list_roundtrip by reflexivity. now rewrite proof_roundtrip. Qed.
(* Indexed natural-deduction replay. Deduction.infer maps shift over the whole context at
   each universal introduction. Here the context is an AVL map from insertion positions to
   entries that remember how many universal introductions enclosed them, and a lookup
   shifts its entry once by the difference. infer_indexed computes Deduction.infer. The
   assumption index is only compared, never incremented: machine integers wrap. *)
From Stdlib Require Import Lia.
Require AxiomFuzzer.Clause.Kernel.
Module ContextMap := AxiomFuzzer.Clause.Kernel.ClauseMap.
Module ContextFacts := AxiomFuzzer.Clause.Kernel.ClauseFacts.
Definition lift k := subst (fun i => Var (k+i)).
Lemma lift_zero a : lift 0 a=a.
Proof. unfold lift. transitivity (subst Var a); [now apply subst_ext|apply subst_id]. Qed.
Lemma shift_lift k a : shift (lift k a)=lift (S k) a.
Proof. unfold shift,lift. rewrite subst_comp. now apply subst_ext. Qed.
Fixpoint infer_indexed (context : ContextMap.t (form * nat)) (size depth : nat) (p : proof) : option form :=
  match p with
  | Assume i => if (0 <=? i) && negb (size <=? i) then
      match ContextMap.find (size-S i) context with Some (a,d) => Some (lift (depth-d) a) | None => None end
      else None
  | ImplicationIntroduction a p =>
      option_map (Imp a) (infer_indexed (ContextMap.add size (a,depth) context) (S size) depth p)
  | ImplicationElimination p q => match infer_indexed context size depth p,infer_indexed context size depth q with
      | Some (Imp a b),Some a' => if form_dec a a' then Some b else None | _,_ => None end
  | UniversalIntroduction p => option_map All (infer_indexed context size (S depth) p)
  | UniversalElimination t p => match infer_indexed context size depth p with
      | Some (All a) => Some (instantiate t a) | _ => None end
  | Explosion a p => match infer_indexed context size depth p with Some Bot => Some a | _ => None end
  | Peirce a b => Some (Imp (Imp (Imp a b) a) a) end.
Definition represents (context : ContextMap.t (form * nat)) (size depth : nat) (G : list form) :=
  List.length G=size /\ forall i, i<size -> exists a d,
    ContextMap.find (size-S i) context=Some (a,d) /\ d<=depth /\ nth_error G i=Some (lift (depth-d) a).
Lemma represents_push context size depth G a : represents context size depth G ->
  represents (ContextMap.add size (a,depth) context) (S size) depth (a::G).
Proof.
  intros [Length Entries]. split; [simpl; now rewrite Length|]. intros [|i] Bound.
  - exists a,depth. replace (S size-S 0) with size by lia.
    rewrite ContextFacts.add_eq_o by reflexivity. rewrite Nat.sub_diag, lift_zero. auto.
  - destruct (Entries i ltac:(lia)) as [b [d [Find [Le Nth]]]]. exists b,d.
    replace (S size-S (S i)) with (size-S i) by lia.
    rewrite ContextFacts.add_neq_o by (hnf; lia). auto.
Qed.
Lemma represents_shift context size depth G : represents context size depth G ->
  represents context size (S depth) (map shift G).
Proof.
  intros [Length Entries]. split; [now rewrite length_map|]. intros i Bound.
  destruct (Entries i Bound) as [a [d [Find [Le Nth]]]]. exists a,d.
  replace (S depth-d) with (S (depth-d)) by lia.
  rewrite nth_error_map, Nth. cbn [option_map]. rewrite shift_lift. auto.
Qed.
Lemma infer_indexed_correct p : forall context size depth G, represents context size depth G ->
  infer_indexed context size depth p=Deduction.infer G p.
Proof.
  induction p as [i|a p IH|p IHp q IHq|p IH|t p IH|a p IH|a b]; intros context size depth G Rep; simpl.
  - destruct (Nat.leb_spec0 size i) as [Ge|Lt]; simpl.
    + symmetry. apply nth_error_None. destruct Rep as [Length _]. lia.
    + destruct Rep as [Length Entries]. destruct (Entries i ltac:(lia)) as [a [d [Find [Le Nth]]]].
      now rewrite Find, Nth.
  - now rewrite (IH _ _ _ (a::G) (@represents_push context size depth G a Rep)).
  - now rewrite (IHp _ _ _ G Rep), (IHq _ _ _ G Rep).
  - now rewrite (IH _ _ _ (map shift G) (@represents_shift context size depth G Rep)).
  - now rewrite (IH _ _ _ G Rep).
  - now rewrite (IH _ _ _ G Rep).
  - reflexivity.
Qed.
Fixpoint index_context (G : list form) : ContextMap.t (form * nat) * nat := match G with
  | [] => (ContextMap.empty (form * nat),0)
  | a::G => let (context,size) := index_context G in (ContextMap.add size (a,0) context,S size) end.
Lemma index_context_represents G : represents (fst (index_context G)) (snd (index_context G)) 0 G.
Proof.
  induction G as [|a G IH]; simpl.
  - split; [reflexivity|]. intros i Bound; lia.
  - destruct (index_context G) as [context size]. now apply represents_push.
Qed.
Fixpoint proof_size p := match p with
  | Assume _ | Peirce _ _ => 1
  | ImplicationIntroduction _ p | UniversalIntroduction p | UniversalElimination _ p | Explosion _ p => S (proof_size p)
  | ImplicationElimination p q => S (proof_size p+proof_size q) end.
(* Small proofs, such as the reference enumerator's candidates, keep the list replay. *)
Definition fast_check {Witness} (axiom_at : Witness -> option form) (c : @Deduction.certificate Witness) :=
  if proof_size (deduction c) <=? 64 then Deduction.check axiom_at c else
  match context_at axiom_at (assumptions c) with
  | Some G => let (context,size) := index_context G in
      match infer_indexed context size 0 (deduction c) with Some Bot => true | _ => false end
  | None => false end.
Lemma fast_check_correct {Witness} (axiom_at : Witness -> option form) c : fast_check axiom_at c=Deduction.check axiom_at c.
Proof.
  unfold fast_check,Deduction.check. destruct (proof_size (deduction c) <=? 64); [reflexivity|].
  destruct (context_at axiom_at (assumptions c)) as [G|]; [|reflexivity].
  pose proof (index_context_represents G) as Rep. destruct (index_context G) as [context size].
  now rewrite (@infer_indexed_correct (deduction c) context size 0 G Rep).
Qed.
Print Assumptions fast_check_correct.
Definition direct_check t c := match certificate_value c with
  | Some c => fast_check (axiom_at t) c | None => false end.
Theorem direct_sound t c : direct_check t c=true -> source_theory t ⊢T Bot.
Proof.
  unfold direct_check. destruct (certificate_value c) as [cert|]; [|discriminate].
  rewrite fast_check_correct.
  intros H. apply Deduction.check_sound in H as [context [Allowed D]].
  exists context; split; [|exact D]. eapply Forall_impl; [|exact Allowed].
  intros a [w A]; now apply axiom_at_sound in A.
Qed.
Theorem direct_complete t : source_theory t ⊢T Bot -> exists c, direct_check t c=true.
Proof.
  intros [context [Allowed D]].
  assert (Derivation : Deduction.theory (axiom_at t) ⊢T Bot).
  { exists context; split; [|exact D]. eapply Forall_impl; [|exact Allowed]. intros a A; apply axiom_at_complete,A. }
  destruct (Deduction.check_complete Derivation) as [c Accepted].
  exists (certificate_code c). unfold direct_check; now rewrite certificate_roundtrip,fast_check_correct.
Qed.
Definition reference_search t n := Enumeration.search Encoding.decode (fun _ => direct_check t) n.
Theorem reference_sound t n c : reference_search t n=Some c -> direct_check t c=true.
Proof. intros H; apply Enumeration.search_sound in H as [budget H]; exact H. Qed.
Theorem reference_complete t : source_theory t ⊢T Bot -> exists n c, reference_search t n=Some c.
Proof.
  intros D. destruct (direct_complete D) as [c Accepted].
  exact (Enumeration.search_complete Encoding.decode (fun _ => direct_check t) (encode c) c 0 (decode_encode c) Accepted).
Qed.

(* A finite prefix of the actual stage loop, retaining its first success. *)
Fixpoint reference_run t n := match n with
  | 0 => reference_search t 0
  | S n => match reference_run t n with Some c => Some c | None => reference_search t (S n) end end.
Theorem reference_run_sound t n c : reference_run t n=Some c -> direct_check t c=true.
Proof.
  induction n; simpl; [apply reference_sound|].
  destruct (reference_run t n) as [found|] eqn:Run.
  - intros H; inversion H; subst; apply IHn; reflexivity.
  - apply reference_sound.
Qed.
Lemma reference_run_reaches t n c : reference_search t n=Some c -> exists found, reference_run t n=Some found.
Proof.
  destruct n; simpl; [eauto|]. destruct (reference_run t n) as [found|]; eauto.
Qed.
Theorem reference_run_complete t : source_theory t ⊢T Bot -> exists n c, reference_run t n=Some c.
Proof.
  intros H; destruct (reference_complete H) as [n [c Run]].
  destruct (@reference_run_reaches t n c Run) as [found Found]. eauto.
Qed.

Module Kernel (Order : WireOrder with Definition function_name := string with Definition predicate_name := string).
Module Clausal := AxiomFuzzer.Source.Kernel.Kernel Order.
Module StandardConnection := Standard.Connection Order.
Inductive certificate :=
  | Clauses (c : AxiomFuzzer.Source.Kernel.certificate)
  | Natural (c : code)
  | Avatar (c : AxiomFuzzer.Source.Kernel.certificate) (proof : AxiomFuzzer.Clause.Avatar.certificate).
Definition check visit limit budget encode_variable decode_function decode_predicate t c := match c with
  | Clauses c => Clausal.check visit limit budget encode_variable decode_function decode_predicate t c
  | Natural c => direct_check t c
  | Avatar c proof => Clausal.avatar_check visit limit budget encode_variable decode_function decode_predicate t c proof end.
Theorem check_sound visit limit budget encode_variable decode_function decode_predicate t c :
  check visit limit budget encode_variable decode_function decode_predicate t c=true -> source_theory t ⊢T Bot.
Proof. destruct c; simpl; [apply StandardConnection.check_is_standard|apply direct_sound|apply StandardConnection.avatar_check_is_standard]. Qed.
Theorem check_complete visit limit budget encode_variable decode_function decode_predicate t :
  source_theory t ⊢T Bot -> exists c, check visit limit budget encode_variable decode_function decode_predicate t c=true.
Proof. intros D; destruct (direct_complete D) as [c Accepted]; exists (Natural c); exact Accepted. Qed.
Theorem check_iff_standard visit limit budget encode_variable decode_function decode_predicate t :
  (exists c, check visit limit budget encode_variable decode_function decode_predicate t c=true) <-> source_theory t ⊢T Bot.
Proof. split; [intros [c H]; now apply check_sound in H|apply check_complete]. Qed.
Theorem accepted_eventually_found visit limit budget encode_variable decode_function decode_predicate t c :
  check visit limit budget encode_variable decode_function decode_predicate t c=true ->
  exists n found, reference_run t n=Some found /\
    check visit limit budget encode_variable decode_function decode_predicate t (Natural found)=true.
Proof.
  intros H; apply check_sound in H. destruct (reference_run_complete H) as [n [found Run]].
  exists n,found; split; [exact Run|now apply reference_run_sound in Run].
Qed.
End Kernel.
Print Assumptions direct_complete.
Print Assumptions reference_complete.
Print Assumptions reference_run_complete.
