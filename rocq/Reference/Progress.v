(* A resumable, extracted traversal of the finite enumeration stages. Expansion
   stores only the frontier, never the exponentially large list of all words. *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia Wf_nat.
Require Import AxiomFuzzer.Reference.Certificate.
Import ListNotations.
Local Open Scope list_scope.

Definition task := (list nat * nat)%type.
Definition children alphabet prefix depth : list task :=
  map (fun x => (prefix ++ [x],depth)) (seq 0 alphabet).
Definition meaning alphabet (job : task) :=
  map (fun suffix => fst job ++ suffix) (Enumeration.words alphabet (snd job)).
Definition remaining alphabet jobs := flat_map (meaning alphabet) jobs.
Fixpoint weight alphabet depth := match depth with
  | 0 => 1 | S d => 1 + alphabet * weight alphabet d end.
Definition measure alphabet (jobs : list task) :=
  fold_right (fun job n => weight alphabet (snd job) + n) 0 jobs.
Definition initial_jobs level : list task := map (fun d => ([],d)) (seq 0 (S level)).
Record cursor := { level : nat; pending : list task; witness : option Encoding.code }.
Definition initial_at n := {|level:=n; pending:=initial_jobs n; witness:=None|}.
Definition initial := initial_at 0.
Definition tick theory c := match witness c with
  | Some _ => c
  | None => match pending c with
    | [] => initial_at (S (level c))
    | (prefix,0)::rest =>
        {|level:=level c; pending:=rest;
          witness:=Enumeration.attempt Encoding.decode (fun _ => direct_check theory) 0 prefix|}
    | (prefix,S d)::rest =>
        {|level:=level c; pending:=children (S (level c)) prefix d ++ rest; witness:=None|}
    end end.
Fixpoint run theory fuel c := match fuel with
  | 0 => c | S n => run theory n (tick theory c) end.

Lemma run_add t n m c : run t (n+m) c=run t m (run t n c).
Proof. revert c; induction n; intros c; simpl; auto. Qed.
Lemma measure_app a xs ys : measure a (xs++ys)=measure a xs+measure a ys.
Proof. induction xs as [|[p d] xs IH]; simpl; [reflexivity|]. unfold measure in *; simpl in *; lia. Qed.
Lemma measure_children a p d : measure a (children a p d)=a*weight a d.
Proof.
  unfold children,measure.
  assert (E : forall xs, fold_right (fun job n => weight a (snd job)+n) 0
     (map (fun x => (p++[x],d)) xs)=List.length xs*weight a d).
  { induction xs; simpl; lia. }
  now rewrite E,length_seq.
Qed.
Lemma expansion_smaller a p d rest :
  measure a (children a p d ++ rest)<measure a ((p,S d)::rest).
Proof. rewrite measure_app,measure_children. change (a*weight a d+measure a rest < S (a*weight a d)+measure a rest). lia. Qed.
Lemma tail_smaller a p rest : measure a rest<measure a ((p,0)::rest).
Proof. change (measure a rest < 1+measure a rest). lia. Qed.
Lemma expansion_meaning a p d rest word :
  In word (remaining a ((p,S d)::rest)) <->
  In word (remaining a (children a p d ++ rest)).
Proof.
  unfold remaining at 1; simpl. unfold remaining at 1; rewrite flat_map_app.
  rewrite !in_app_iff. apply or_iff_compat_r.
  unfold meaning at 1; cbn [fst snd Enumeration.words].
  unfold children. rewrite in_map_iff,in_flat_map.
  split.
  - intros [suffix [<- InSuffix]]. apply in_flat_map in InSuffix as [x [X Suffix]].
    apply in_map_iff in Suffix as [tail [<- Tail]].
    exists (p++[x],d); split.
    + apply in_map_iff; exists x; split; [reflexivity|exact X].
    + unfold meaning; simpl. apply in_map_iff. exists tail; split; [rewrite <- app_assoc; reflexivity|exact Tail].
  - intros [[prefix depth] [Child Word]]. apply in_map_iff in Child as [x [E X]].
    inversion E; subst prefix depth. unfold meaning in Word; simpl in Word.
    apply in_map_iff in Word as [tail [<- Tail]]. exists (x::tail); split.
    + rewrite <- app_assoc; reflexivity.
    + apply in_flat_map. exists x; split; [exact X|now apply in_map].
Qed.
Lemma initial_meaning n : remaining (S n) (initial_jobs n)=Enumeration.stage n.
Proof.
  unfold remaining,initial_jobs,Enumeration.stage.
  induction (seq 0 (S n)) as [|d ds IH]; simpl; [reflexivity|].
  unfold meaning at 1; simpl. now rewrite map_id,IH.
Qed.
Lemma attempt_sound t word c :
  Enumeration.attempt Encoding.decode (fun _ => direct_check t) 0 word=Some c -> direct_check t c=true.
Proof.
  unfold Enumeration.attempt. destruct (Encoding.decode word) as [decoded|]; [|discriminate].
  destruct (direct_check t decoded) eqn:E; [|discriminate]. intros H; inversion H; subst; exact E.
Qed.
Theorem tick_sound t state :
  (forall c, witness state=Some c -> direct_check t c=true) ->
  forall c, witness (tick t state)=Some c -> direct_check t c=true.
Proof.
  destruct state as [n jobs result]; simpl. destruct result as [found|]; [auto|].
  destruct jobs as [|[p [|d]] rest]; simpl; try discriminate. intros _; apply attempt_sound.
Qed.
Theorem run_sound t fuel state :
  (forall c, witness state=Some c -> direct_check t c=true) ->
  forall c, witness (run t fuel state)=Some c -> direct_check t c=true.
Proof. revert state; induction fuel; intros state H; simpl; [exact H|]. apply IHfuel,tick_sound,H. Qed.
Lemma found_stays t fuel state c : witness state=Some c -> witness (run t fuel state)=Some c.
Proof.
  revert state; induction fuel; intros state H; simpl; [exact H|].
  apply IHfuel. unfold tick; now rewrite H.
Qed.

(* Every finite frontier is processed in finitely many ticks, unless a checked
   proof has already been found. *)
Lemma drain t n jobs : exists k,
  (exists c, witness (run t k {|level:=n;pending:=jobs;witness:=None|})=Some c) \/
  run t k {|level:=n;pending:=jobs;witness:=None|}={|level:=n;pending:=[];witness:=None|}.
Proof.
  remember (measure (S n) jobs) as size eqn:E. revert jobs E.
  induction size using lt_wf_ind; intros jobs E. destruct jobs as [|[p [|d]] rest].
  - exists 0; now right.
  - destruct (Enumeration.attempt Encoding.decode (fun _ => direct_check t) 0 p) as [c|] eqn:A.
    + exists 1; left; exists c; cbn [run tick level pending witness]; now rewrite A.
    + assert (Small : measure (S n) rest<size) by (subst size; apply tail_smaller).
      destruct (H _ Small rest eq_refl) as [k Result].
      exists (S k); cbn [run tick level pending witness]; rewrite A; exact Result.
  - assert (Small : measure (S n) (children (S n) p d++rest)<size)
      by (subst size; apply expansion_smaller).
    destruct (H _ Small _ eq_refl) as [k Result].
    exists (S k); exact Result.
Qed.
Lemma stage_reached t n : exists k,
  (exists c, witness (run t k initial)=Some c) \/ run t k initial=initial_at n.
Proof.
  induction n as [|n [k [Found|Reached]]].
  - exists 0; now right.
  - exists k; now left.
  - destruct (drain t n (initial_jobs n)) as [m [Found|Finished]].
    + exists (k+m); left; rewrite run_add,Reached; exact Found.
    + exists (k+(m+1)); right. rewrite run_add,Reached.
      unfold initial_at at 1. rewrite run_add,Finished; reflexivity.
Qed.
Lemma accepted_word_found t n jobs word c :
  In word (remaining (S n) jobs) -> Encoding.decode word=Some c -> direct_check t c=true ->
  exists k found, witness (run t k {|level:=n;pending:=jobs;witness:=None|})=Some found.
Proof.
  remember (measure (S n) jobs) as size eqn:E. revert jobs E.
  induction size using lt_wf_ind; intros jobs E InWord Decoded Checked.
  destruct jobs as [|[p [|d]] rest]; [contradiction| |].
  - destruct (Enumeration.attempt Encoding.decode (fun _ => direct_check t) 0 p) as [found|] eqn:A.
    + exists 1,found; cbn [run tick level pending witness]; now rewrite A.
    + assert (Tail : In word (remaining (S n) rest)).
      { simpl in InWord. rewrite app_nil_r in InWord. destruct InWord as [<-|InWord]; [|exact InWord].
        unfold Enumeration.attempt in A; rewrite Decoded,Checked in A; discriminate. }
      assert (Small : measure (S n) rest<size) by (subst size; apply tail_smaller).
      destruct (H _ Small rest eq_refl Tail Decoded Checked) as [k [found Run]].
      exists (S k),found; cbn [run tick level pending witness]; now rewrite A.
  - assert (Small : measure (S n) (children (S n) p d++rest)<size)
      by (subst size; apply expansion_smaller).
    apply expansion_meaning in InWord.
    destruct (H _ Small _ eq_refl InWord Decoded Checked) as [k [found Run]].
    exists (S k),found; exact Run.
Qed.
Theorem complete t c : direct_check t c=true ->
  exists ticks found, witness (run t ticks initial)=Some found /\ direct_check t found=true.
Proof.
  intros Accepted. destruct (Enumeration.every_word (Encoding.encode c)) as [n InStage].
  destruct (stage_reached t n) as [k [[found Found]|Reached]].
  - exists k,found; split; [exact Found|]. eapply run_sound; [|exact Found]. discriminate.
  - rewrite <- initial_meaning in InStage.
    destruct (accepted_word_found t n (initial_jobs n) (Encoding.encode c) c InStage
      (Encoding.decode_encode c) Accepted) as [m [found Found]].
    exists (k+m),found; split.
    + rewrite run_add,Reached; exact Found.
    + eapply run_sound; [|exact Found]. discriminate.
Qed.
Theorem refutation_found t : Deduction.tprv (Standard.source_theory t) Syntax.Bot ->
  exists ticks found, witness (run t ticks initial)=Some found /\ direct_check t found=true.
Proof. intros H. destruct (direct_complete H) as [c C]. now apply (complete t c). Qed.
Print Assumptions refutation_found.
