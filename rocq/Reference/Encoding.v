(* A total finite-data decoder, shared by proof search and replay. *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia String Ascii.
Import ListNotations.
Local Open Scope list_scope.
Inductive code := Number (n : nat) | Pair (left right : code).
Fixpoint encode c := match c with Number n => [0;n] | Pair x y => 1 :: encode x ++ encode y end.
Fixpoint height c := match c with Number _ => 1 | Pair x y => S (Nat.max (height x) (height y)) end.
Fixpoint parse fuel words : option (code * list nat) := match fuel,words with
  | S _,0::n::rest => Some (Number n,rest)
  | S fuel,1::rest => match parse fuel rest with
      | Some (x,rest) => match parse fuel rest with Some (y,rest) => Some (Pair x y,rest) | None => None end
      | None => None end
  | _,_ => None end.
Lemma parse_encode c : forall fuel rest, height c<=fuel -> parse fuel (encode c ++ rest)=Some (c,rest).
Proof.
  induction c as [n|x IHx y IHy]; intros [|fuel] rest Bound; simpl in Bound; try lia; cbn [encode parse].
  - reflexivity.
  - cbn [List.app]. rewrite <- app_assoc. rewrite IHx by lia. rewrite IHy by lia. reflexivity.
Qed.
Lemma height_length c : height c<=List.length (encode c).
 Proof. induction c; simpl; [lia|]. rewrite length_app. lia. Qed.
Definition decode words := match parse (List.length words) words with Some (c,[]) => Some c | _ => None end.
Theorem decode_encode c : decode (encode c)=Some c.
Proof.
  unfold decode. rewrite <- (app_nil_r (encode c)) at 2.
  rewrite parse_encode by apply height_length. reflexivity.
Qed.
Fixpoint list_code {A} (write : A -> code) xs := match xs with
  | [] => Number 0 | x::xs => Pair (write x) (list_code write xs) end.
Fixpoint list_value {A} (read : code -> option A) c := match c with
  | Number 0 => Some []
  | Pair x xs => match read x,list_value read xs with Some x,Some xs => Some (x::xs) | _,_ => None end
  | _ => None end.
Lemma list_roundtrip {A} (write : A -> code) read :
  (forall x, read (write x)=Some x) -> forall xs, list_value read (list_code write xs)=Some xs.
Proof. intros H xs; induction xs; simpl; [reflexivity|]. now rewrite H, IHxs. Qed.
Lemma list_roundtrip_on {A} (write : A -> code) read xs :
  (forall x, In x xs -> read (write x)=Some x) -> list_value read (list_code write xs)=Some xs.
Proof.
  induction xs; intros H; simpl; [reflexivity|]. rewrite H by now left.
  rewrite IHxs; [reflexivity|]. intros x In; apply H; now right.
Qed.
Definition number_value c := match c with Number n => Some n | _ => None end.
Fixpoint string_code s := match s with
  | EmptyString => Number 0
  | String x xs => Pair (Number (nat_of_ascii x)) (string_code xs) end.
Fixpoint string_value c := match c with
  | Number 0 => Some EmptyString
  | Pair (Number x) xs => match string_value xs with Some s => Some (String (ascii_of_nat x) s) | None => None end
  | _ => None end.
Lemma string_roundtrip s : string_value (string_code s)=Some s.
Proof. induction s; simpl; [reflexivity|]. now rewrite IHs,ascii_nat_embedding. Qed.
Print Assumptions decode_encode.

Require Import AxiomFuzzer.Source.Language AxiomFuzzer.Source.Validation.
Fixpoint term_code (t : source_term string) := match t with
  | SBound n => Pair (Number 0) (Number n)
  | SFree n => Pair (Number 1) (Number n)
  | SApply f ts => Pair (Number 2) (Pair (string_code f) (list_code term_code ts)) end.
Fixpoint term_value c : option (source_term string) := match c with
  | Pair (Number 0) (Number n) => Some (SBound n)
  | Pair (Number 1) (Number n) => Some (SFree n)
  | Pair (Number 2) (Pair f ts) => match string_value f,list_value term_value ts with
      | Some f,Some ts => Some (SApply f ts) | _,_ => None end
  | _ => None end.
Lemma term_roundtrip : forall t, term_value (term_code t)=Some t.
Proof.
  fix IH 1; intros [n|n|f ts]; simpl; try reflexivity. rewrite string_roundtrip.
  assert (Args : list_value term_value (list_code term_code ts)=Some ts).
  { induction ts as [|t ts HT]; simpl; [reflexivity|]. now rewrite IH, HT. }
  now rewrite Args.
Qed.
Fixpoint source_code (f : source_formula string string) := match f with
  | STop => Number 0 | SBot => Number 1
  | SPred p ts => Pair (Number 2) (Pair (string_code p) (list_code term_code ts))
  | SEq x y => Pair (Number 3) (Pair (term_code x) (term_code y))
  | SNeg f => Pair (Number 4) (source_code f)
  | SConj fs => Pair (Number 5) (list_code source_code fs)
  | SDisj fs => Pair (Number 6) (list_code source_code fs)
  | SAll f => Pair (Number 7) (source_code f)
  | SEx f => Pair (Number 8) (source_code f) end.
Fixpoint source_value c : option (source_formula string string) := match c with
  | Number 0 => Some STop | Number 1 => Some SBot
  | Pair (Number 2) (Pair p ts) => match string_value p,list_value term_value ts with
      | Some p,Some ts => Some (SPred p ts) | _,_ => None end
  | Pair (Number 3) (Pair x y) => match term_value x,term_value y with
      | Some x,Some y => Some (SEq x y) | _,_ => None end
  | Pair (Number 4) f => option_map SNeg (source_value f)
  | Pair (Number 5) fs => option_map SConj (list_value source_value fs)
  | Pair (Number 6) fs => option_map SDisj (list_value source_value fs)
  | Pair (Number 7) f => option_map SAll (source_value f)
  | Pair (Number 8) f => option_map SEx (source_value f)
  | _ => None end.
Lemma source_roundtrip : forall f, source_value (source_code f)=Some f.
Proof.
  fix IH 1; intros [| |p ts|x y|f|fs|fs|f|f]; simpl; try reflexivity.
  - rewrite string_roundtrip, (list_roundtrip term_code term_value term_roundtrip); reflexivity.
  - now rewrite !term_roundtrip.
  - now rewrite IH.
  - assert (Args : list_value source_value (list_code source_code fs)=Some fs).
    { induction fs as [|f fs HT]; simpl; [reflexivity|]. now rewrite IH, HT. }
    now rewrite Args.
  - assert (Args : list_value source_value (list_code source_code fs)=Some fs).
    { induction fs as [|f fs HT]; simpl; [reflexivity|]. now rewrite IH, HT. }
    now rewrite Args.
  - now rewrite IH.
  - now rewrite IH.
Qed.
Definition schema_code s := match s with
  | ComprehensionSchema => Number 0 | SeparationSchema => Number 1
  | ReplacementSchema => Number 2 | UnrestrictedSchema => Number 3
  | RegisteredSchema n r => Pair (string_code n) (string_code r) end.
Definition schema_value c := match c with
  | Number 0 => Some ComprehensionSchema | Number 1 => Some SeparationSchema
  | Number 2 => Some ReplacementSchema | Number 3 => Some UnrestrictedSchema
  | Pair n r => match string_value n,string_value r with Some n,Some r => Some (RegisteredSchema n r) | _,_ => None end
  | _ => None end.
Lemma schema_roundtrip s : schema_value (schema_code s)=Some s.
Proof. destruct s; simpl; try reflexivity; now rewrite !string_roundtrip. Qed.
