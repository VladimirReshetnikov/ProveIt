(** Extended-natural minimization with an explicit infinity value. *)

From Stdlib Require Import Arith.Compare_dec Lia
  Logic.ClassicalDescription Logic.ClassicalEpsilon.
From Foundation.Vorspiel.Nat Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.

Definition enat := option nat.
Definition enat_top : enat := None.
Definition enat_of_nat (n : nat) : enat := Some n.

Definition enat_le (x y : enat) : Prop :=
  match x, y with
  | Some m, Some n => m <= n
  | Some _, None => True
  | None, Some _ => False
  | None, None => True
  end.

Definition enat_lt (x y : enat) : Prop :=
  match x, y with
  | Some m, Some n => m < n
  | Some _, None => True
  | None, _ => False
  end.

Definition enat_least_witness (P : nat -> Prop) (H : exists n, P n) :
    {n : nat | P n /\ forall m, m < n -> ~ P m} :=
  constructive_indefinite_description
    (fun n => P n /\ forall m, m < n -> ~ P m)
    (@nat_least_number P H).

Definition enat_find (P : nat -> Prop) : enat :=
  match excluded_middle_informative (exists n, P n) with
  | left H => Some (proj1_sig (@enat_least_witness P H))
  | right _ => None
  end.

Lemma enat_find_exists_spec : forall P,
  (exists n, P n) ->
  exists k,
    enat_find P = Some k /\ P k /\ forall m, m < k -> ~ P m.
Proof.
  intros P Hex. unfold enat_find.
  destruct (excluded_middle_informative (exists n, P n)) as [H | H];
    [|contradiction].
  destruct (@enat_least_witness P H) as [k [Hk Hleast]] eqn:Hw.
  exists k. simpl. now repeat split.
Qed.

Theorem enat_lt_find : forall P n,
  (forall m, m <= n -> ~ P m) ->
  enat_lt (enat_of_nat n) (enat_find P).
Proof.
  intros P n Hnone.
  destruct (excluded_middle_informative (exists m, P m)) as [Hex | Hempty].
  - destruct (@enat_find_exists_spec P Hex) as [k [Hfind [Hk Hleast]]].
    rewrite Hfind. simpl. assert (~ k <= n).
    { intro Hkn. exact (Hnone k Hkn Hk). }
    lia.
  - unfold enat_find.
    destruct (excluded_middle_informative (exists m, P m)); [contradiction |].
    exact I.
Qed.

Theorem enat_exists_of_find_le : forall P n,
  enat_le (enat_find P) (enat_of_nat n) ->
  exists m, m <= n /\ P m.
Proof.
  intros P n Hle.
  destruct (excluded_middle_informative (exists m, P m)) as [Hex | Hempty].
  - destruct (@enat_find_exists_spec P Hex) as [k [Hfind [Hk _]]].
    rewrite Hfind in Hle. exists k. now split.
  - unfold enat_find in Hle.
    destruct (excluded_middle_informative (exists m, P m)); contradiction.
Qed.

Theorem enat_find_eq_top_iff : forall P,
  enat_find P = enat_top <-> forall n, ~ P n.
Proof.
  intro P. split.
  - intro Hfind. intros n Hn.
    assert (Hex : exists m, P m) by now exists n.
    destruct (@enat_find_exists_spec P Hex) as [k [Hsome _]].
    rewrite Hsome in Hfind. discriminate.
  - intro Hnone. unfold enat_find.
    destruct (excluded_middle_informative (exists n, P n)) as [[n Hn] | _].
    + exfalso. exact (Hnone n Hn).
    + reflexivity.
Qed.

Theorem enat_find_le : forall P n,
  P n -> enat_le (enat_find P) (enat_of_nat n).
Proof.
  intros P n Hn.
  assert (Hex : exists m, P m) by now exists n.
  destruct (@enat_find_exists_spec P Hex) as [k [Hfind [Hk Hleast]]].
  rewrite Hfind. simpl.
  destruct (le_lt_dec k n) as [Hkn | Hnk]; [exact Hkn |].
  exfalso. exact (Hleast n Hnk Hn).
Qed.
