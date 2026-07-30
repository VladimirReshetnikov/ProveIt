(** Executable arithmetic truth values and bounded universal quantification. *)

From Stdlib Require Import Arith.Arith Lia.

Definition nat_truth_eq (n m : nat) : nat :=
  if Nat.eq_dec n m then 1 else 0.

Definition nat_truth_lt (n m : nat) : nat :=
  if lt_dec n m then 1 else 0.

Definition nat_truth_le (n m : nat) : nat :=
  if le_dec n m then 1 else 0.

Definition nat_truth_dvd (n m : nat) : nat :=
  if Nat.eq_dec n 0 then nat_truth_eq m 0
  else nat_truth_eq (m mod n) 0.

Lemma nat_positive_of_eq_one : forall n, n = 1 -> 0 < n.
Proof. intros n ->. lia. Qed.

Lemma nat_truth_eq_positive_iff : forall n m,
  0 < nat_truth_eq n m <-> n = m.
Proof. intros n m. unfold nat_truth_eq. destruct (Nat.eq_dec n m); lia. Qed.

Lemma nat_truth_lt_positive_iff : forall n m,
  0 < nat_truth_lt n m <-> n < m.
Proof. intros n m. unfold nat_truth_lt. destruct (lt_dec n m); lia. Qed.

Lemma nat_truth_le_positive_iff : forall n m,
  0 < nat_truth_le n m <-> n <= m.
Proof. intros n m. unfold nat_truth_le. destruct (le_dec n m); lia. Qed.

Lemma nat_truth_dvd_positive_iff : forall n m,
  0 < nat_truth_dvd n m <-> Nat.divide n m.
Proof.
  intros n m. unfold nat_truth_dvd.
  destruct (Nat.eq_dec n 0) as [-> | Hn].
  - rewrite nat_truth_eq_positive_iff. split.
    + intro H. subst m. now exists 0.
    + intros [k Hk]. now rewrite Nat.mul_0_r in Hk.
  - rewrite nat_truth_eq_positive_iff, Nat.mod_divide by exact Hn.
    reflexivity.
Qed.

Definition nat_truth_inv (n : nat) : nat := nat_truth_eq n 0.
Definition nat_truth_pos (n : nat) : nat := nat_truth_lt 0 n.
Definition nat_truth_and (n m : nat) : nat := nat_truth_lt 0 (n * m).
Definition nat_truth_or (n m : nat) : nat := nat_truth_lt 0 (n + m).

Lemma nat_truth_inv_zero : nat_truth_inv 0 = 1.
Proof. reflexivity. Qed.

Lemma nat_truth_inv_eq_zero_iff : forall n,
  nat_truth_inv n = 0 <-> 0 < n.
Proof.
  intro n. unfold nat_truth_inv, nat_truth_eq.
  destruct (Nat.eq_dec n 0); lia.
Qed.

Lemma nat_truth_inv_nonzero : forall n,
  n <> 0 -> nat_truth_inv n = 0.
Proof. intros n H. unfold nat_truth_inv, nat_truth_eq. now destruct Nat.eq_dec. Qed.

Lemma nat_truth_pos_zero : nat_truth_pos 0 = 0.
Proof. reflexivity. Qed.

Lemma nat_truth_pos_nonzero : forall n,
  n <> 0 -> nat_truth_pos n = 1.
Proof. intros n H. unfold nat_truth_pos, nat_truth_lt. destruct lt_dec; lia. Qed.

Lemma nat_truth_and_positive_iff : forall n m,
  0 < nat_truth_and n m <-> 0 < n /\ 0 < m.
Proof.
  intros n m. unfold nat_truth_and. rewrite nat_truth_lt_positive_iff.
  nia.
Qed.

Lemma nat_truth_or_positive_iff : forall n m,
  0 < nat_truth_or n m <-> 0 < n \/ 0 < m.
Proof.
  intros n m. unfold nat_truth_or. rewrite nat_truth_lt_positive_iff.
  lia.
Qed.

Lemma nat_truth_inv_positive_iff : forall n,
  0 < nat_truth_inv n <-> ~ 0 < n.
Proof. intro n. unfold nat_truth_inv. rewrite nat_truth_eq_positive_iff. lia. Qed.

Lemma nat_truth_pos_positive_iff : forall n,
  0 < nat_truth_pos n <-> 0 < n.
Proof. intro n. apply nat_truth_lt_positive_iff. Qed.

Fixpoint nat_bounded_all (n : nat) (phi : nat -> nat) : nat :=
  match n with
  | 0 => 1
  | S k => nat_truth_and (nat_truth_pos (phi k)) (nat_bounded_all k phi)
  end.

Theorem nat_bounded_all_positive_iff : forall n phi,
  0 < nat_bounded_all n phi <->
  forall m, m < n -> 0 < phi m.
Proof.
  induction n as [|n IH]; intro phi; simpl.
  - split; [intros _ m H; lia | intros; lia].
  - rewrite nat_truth_and_positive_iff,
      nat_truth_pos_positive_iff, IH.
    split.
    + intros [Hn Hall] m Hm. destruct (Nat.eq_dec m n) as [-> | Hne].
      * exact Hn.
      * apply Hall. lia.
    + intro Hall. split.
      * apply Hall. lia.
      * intros m Hm. apply Hall. lia.
Qed.

Lemma nat_bounded_all_boolean : forall n phi,
  nat_bounded_all n phi = 0 \/ nat_bounded_all n phi = 1.
Proof.
  induction n as [|n IH]; intro phi; simpl; [now right |].
  unfold nat_truth_and, nat_truth_lt.
  destruct lt_dec; [now right | now left].
Qed.

Lemma nat_truth_pos_eq_zero_iff : forall n,
  nat_truth_pos n = 0 <-> n = 0.
Proof.
  intro n. unfold nat_truth_pos, nat_truth_lt.
  destruct (lt_dec 0 n); lia.
Qed.

Lemma nat_truth_and_eq_zero_iff : forall n m,
  nat_truth_and n m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros n m. unfold nat_truth_and, nat_truth_lt.
  destruct (lt_dec 0 (n * m)) as [Hpos | Hnpos].
  - split; [discriminate | intros [-> | ->]; simpl in Hpos; lia].
  - split; [|intro; reflexivity].
    intro Hzero. apply Nat.eq_mul_0. lia.
Qed.

Theorem nat_bounded_all_eq_zero_iff : forall n phi,
  nat_bounded_all n phi = 0 <->
  exists m, m < n /\ phi m = 0.
Proof.
  induction n as [|n IH]; intro phi; simpl.
  - split; [discriminate | intros [m [Hm _]]; lia].
  - rewrite nat_truth_and_eq_zero_iff,
      nat_truth_pos_eq_zero_iff, IH.
    split.
    + intros [Hn | [m [Hm Hmzero]]].
      * exists n. split; [lia | exact Hn].
      * exists m. split; [lia | exact Hmzero].
    + intros [m [Hm Hzero]].
      destruct (Nat.eq_dec m n) as [-> | Hne].
      * now left.
      * right. exists m. split; [lia | exact Hzero].
Qed.

Theorem nat_bounded_all_eq_one_iff_positive : forall n phi,
  nat_bounded_all n phi = 1 <-> 0 < nat_bounded_all n phi.
Proof.
  intros n phi. destruct (nat_bounded_all_boolean n phi) as [-> | ->]; lia.
Qed.
