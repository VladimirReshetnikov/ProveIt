(**
  Semantic core of Robinson arithmetic Q.

  Foundation encodes these laws as a finite first-order theory.  This module
  exposes exactly the eight non-equality axioms as a model capability and
  derives their reusable arithmetic consequences without depending on a
  particular entailment calculus.
*)

From Stdlib Require Import Arith.PeanoNat Lia Logic.Classical_Prop.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record robinson_q_laws {M : Type} (O : oring_carrier M) : Prop := {
  robinson_q_succ_ne_zero : forall a,
    oring_add O a (oring_one O) <> oring_zero O;
  robinson_q_succ_inj : forall a b,
    oring_add O a (oring_one O) = oring_add O b (oring_one O) -> a = b;
  robinson_q_zero_or_succ : forall a,
    a = oring_zero O \/ exists b, a = oring_add O b (oring_one O);
  robinson_q_add_zero : forall a,
    oring_add O a (oring_zero O) = a;
  robinson_q_add_succ : forall a b,
    oring_add O a (oring_add O b (oring_one O)) =
    oring_add O (oring_add O a b) (oring_one O);
  robinson_q_mul_zero : forall a,
    oring_mul O a (oring_zero O) = oring_zero O;
  robinson_q_mul_succ : forall a b,
    oring_mul O a (oring_add O b (oring_one O)) =
    oring_add O (oring_mul O a b) a;
  robinson_q_lt_def : forall a b,
    oring_lt O a b <->
    exists c, oring_add O a (oring_add O c (oring_one O)) = b
}.

Lemma robinson_q_exists_succ_of_ne_zero : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall a,
  a <> oring_zero O -> exists b, a = oring_add O b (oring_one O).
Proof.
  intros M O H a Hne.
  destruct (@robinson_q_zero_or_succ M O H a) as [Ha | Ha].
  - contradiction.
  - exact Ha.
Qed.

Lemma robinson_q_exists_succ_of_ne_zero' : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall a,
  a <> oring_zero O -> exists b, oring_add O b (oring_one O) = a.
Proof.
  intros M O H a Hne.
  destruct (robinson_q_exists_succ_of_ne_zero H Hne) as [b Hb].
  exists b. now symmetry.
Qed.

Lemma robinson_q_one_ne_zero : forall M (O : oring_carrier M),
  robinson_q_laws O -> oring_one O <> oring_zero O.
Proof.
  intros M O H Hone.
  apply (@robinson_q_succ_ne_zero M O H (oring_zero O)).
  rewrite Hone. apply (@robinson_q_add_zero M O H).
Qed.

(** The source proof of [0 + 1 = 1] uses only successor decomposition,
    successor injectivity, and successor nonzeroness.  Keeping the excluded
    middle localized here mirrors its noncomputable model section. *)
Lemma robinson_q_zero_add_one : forall M (O : oring_carrier M),
  robinson_q_laws O ->
  oring_add O (oring_zero O) (oring_one O) = oring_one O.
Proof.
  intros M O H.
  destruct (robinson_q_exists_succ_of_ne_zero' H
    (robinson_q_one_ne_zero H)) as [a Ha].
  assert (Hazero : a = oring_zero O).
  { destruct (classic (a = oring_zero O)) as [Ha0 | Ha0]; [exact Ha0|].
    destruct (robinson_q_exists_succ_of_ne_zero' H Ha0) as [b Hb].
    exfalso. apply (@robinson_q_succ_ne_zero M O H
      (oring_add O (oring_zero O) b)).
    apply (@robinson_q_succ_inj M O H).
    rewrite <- (@robinson_q_add_succ M O H (oring_zero O) b).
    rewrite Hb.
    rewrite <- (@robinson_q_add_succ M O H (oring_zero O) a).
    now rewrite Ha. }
  subst a. exact Ha.
Qed.

Lemma robinson_q_numeral_succ : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n,
  oring_numeral O (S n) =
  oring_add O (oring_numeral O n) (oring_one O).
Proof.
  intros M O H [|n].
  - simpl. symmetry. apply (robinson_q_zero_add_one H).
  - apply oring_numeral_succ_succ.
Qed.

Lemma robinson_q_numeral_add : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  oring_add O (oring_numeral O n) (oring_numeral O m) =
  oring_numeral O (n + m).
Proof.
  intros M O H n m. induction m as [|m IH].
  - cbn. rewrite Nat.add_0_r. apply (@robinson_q_add_zero M O H).
  - rewrite (robinson_q_numeral_succ H m),
      (@robinson_q_add_succ M O H), IH.
    replace (n + S m) with (S (n + m)) by lia.
    symmetry. apply (robinson_q_numeral_succ H).
Qed.

Lemma robinson_q_numeral_mul : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  oring_mul O (oring_numeral O n) (oring_numeral O m) =
  oring_numeral O (n * m).
Proof.
  intros M O H n m. induction m as [|m IH].
  - cbn. rewrite Nat.mul_0_r. apply (@robinson_q_mul_zero M O H).
  - rewrite (robinson_q_numeral_succ H m),
      (@robinson_q_mul_succ M O H), IH,
      (robinson_q_numeral_add H).
    f_equal. lia.
Qed.

Lemma robinson_q_numeral_zero_succ_ne : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n,
  oring_numeral O 0 <> oring_numeral O (S n).
Proof.
  intros M O H n Heq.
  rewrite (robinson_q_numeral_succ H n) in Heq.
  apply (@robinson_q_succ_ne_zero M O H (oring_numeral O n)).
  now symmetry.
Qed.

Lemma robinson_q_numeral_ne : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  n <> m -> oring_numeral O n <> oring_numeral O m.
Proof.
  intros M O H n. induction n as [|n IH]; intros [|m] Hne Heq.
  - contradiction.
  - exact (robinson_q_numeral_zero_succ_ne H Heq).
  - exact (robinson_q_numeral_zero_succ_ne H (eq_sym Heq)).
  - apply (IH m); [lia|].
    apply (@robinson_q_succ_inj M O H).
    now rewrite <- !(robinson_q_numeral_succ H).
Qed.

Lemma robinson_q_numeral_eq_iff : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  oring_numeral O n = oring_numeral O m <-> n = m.
Proof.
  intros M O H n m. split.
  - intro Heq. destruct (Nat.eq_dec n m); [assumption|].
    exfalso. exact (robinson_q_numeral_ne H n0 Heq).
  - now intros ->.
Qed.

Lemma robinson_q_numeral_lt : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n m,
  n < m -> oring_lt O (oring_numeral O n) (oring_numeral O m).
Proof.
  intros M O H n m Hnm.
  apply (proj2 (@robinson_q_lt_def M O H
    (oring_numeral O n) (oring_numeral O m))).
  exists (oring_numeral O (m - n - 1)).
  rewrite <- (robinson_q_numeral_succ H (m - n - 1)).
  rewrite (robinson_q_numeral_add H).
  f_equal. lia.
Qed.

Lemma robinson_q_not_lt_zero : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall x,
  ~ oring_lt O x (oring_zero O).
Proof.
  intros M O H x Hlt.
  destruct (proj1 (@robinson_q_lt_def M O H x (oring_zero O)) Hlt)
    as [c Hc].
  rewrite (@robinson_q_add_succ M O H) in Hc.
  exact (@robinson_q_succ_ne_zero M O H (oring_add O x c) Hc).
Qed.

Lemma robinson_q_lt_numeral_iff : forall M (O : oring_carrier M),
  robinson_q_laws O -> forall n x,
  oring_lt O x (oring_numeral O n) <->
  exists m, m < n /\ x = oring_numeral O m.
Proof.
  intros M O H n. induction n as [|n IH]; intro x; split.
  - intro Hlt. exfalso. exact (robinson_q_not_lt_zero H Hlt).
  - intros [m [Hm _]]. lia.
  - intro Hlt.
    destruct (proj1 (@robinson_q_lt_def M O H x
      (oring_numeral O (S n))) Hlt) as [a Ha].
    rewrite (@robinson_q_add_succ M O H) in Ha.
    rewrite (robinson_q_numeral_succ H n) in Ha.
    apply (@robinson_q_succ_inj M O H) in Ha.
    destruct (@robinson_q_zero_or_succ M O H a)
      as [Hazero | [b Hb]].
    + subst a. rewrite (@robinson_q_add_zero M O H) in Ha.
      exists n. split; [lia|exact Ha].
    + rewrite Hb in Ha.
      assert (Hlower : oring_lt O x (oring_numeral O n)).
      { apply (proj2 (@robinson_q_lt_def M O H x
          (oring_numeral O n))). now exists b. }
      destruct (proj1 (IH x) Hlower) as [m [Hmn Hm]].
      exists m. split; [lia|exact Hm].
  - intros [m [Hmn ->]]. now apply (robinson_q_numeral_lt H).
Qed.

Definition robinson_q_r0_laws : forall M (O : oring_carrier M),
  robinson_q_laws O -> r0_laws O.
Proof.
  intros M O H. constructor.
  - apply (robinson_q_numeral_add H).
  - apply (robinson_q_numeral_mul H).
  - apply (robinson_q_numeral_ne H).
  - apply (robinson_q_lt_numeral_iff H).
Defined.

Definition nat_robinson_q_laws : robinson_q_laws nat_oring_carrier.
Proof.
  constructor.
  - intros a. change (a + 1 <> 0). lia.
  - intros a b. change (a + 1 = b + 1 -> a = b). lia.
  - intro a. destruct a as [|a].
    + left. reflexivity.
    + right. exists a. change (S a = a + 1). lia.
  - apply Nat.add_0_r.
  - intros a b. change (a + (b + 1) = a + b + 1). lia.
  - apply Nat.mul_0_r.
  - intros a b. change (a * (b + 1) = a * b + a). lia.
  - intros a b. change (a < b <-> exists c, a + (c + 1) = b).
    split.
    + intro Hab. exists (b - a - 1). lia.
    + intros [c Hc]. lia.
Defined.
