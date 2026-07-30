(**
  Semantic laws of Peano arithmetic without induction.

  This ports the model-theoretic algebraic core of
  [Foundation/FirstOrder/Arithmetic/PeanoMinus/Basic.lean].  The source first
  presents the laws as a finite first-order theory and then extracts these
  consequences from a model.  Here the semantic package is explicit, making
  every downstream theorem independent of a particular proof calculus.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition peano_minus_le {M : Type} (O : oring_carrier M)
    (x y : M) : Prop := x = y \/ oring_lt O x y.

Record peano_minus_laws {M : Type} (O : oring_carrier M) : Prop := {
  peano_minus_add_zero : forall x,
    oring_add O x (oring_zero O) = x;
  peano_minus_add_assoc : forall x y z,
    oring_add O (oring_add O x y) z = oring_add O x (oring_add O y z);
  peano_minus_add_comm : forall x y,
    oring_add O x y = oring_add O y x;
  peano_minus_add_eq_of_lt : forall x y,
    oring_lt O x y -> exists z, oring_add O x z = y;
  peano_minus_zero_le : forall x,
    peano_minus_le O (oring_zero O) x;
  peano_minus_zero_lt_one :
    oring_lt O (oring_zero O) (oring_one O);
  peano_minus_one_le_of_zero_lt : forall x,
    oring_lt O (oring_zero O) x -> peano_minus_le O (oring_one O) x;
  peano_minus_add_lt_add : forall x y z,
    oring_lt O x y ->
    oring_lt O (oring_add O x z) (oring_add O y z);
  peano_minus_mul_zero : forall x,
    oring_mul O x (oring_zero O) = oring_zero O;
  peano_minus_mul_one : forall x,
    oring_mul O x (oring_one O) = x;
  peano_minus_mul_assoc : forall x y z,
    oring_mul O (oring_mul O x y) z = oring_mul O x (oring_mul O y z);
  peano_minus_mul_comm : forall x y,
    oring_mul O x y = oring_mul O y x;
  peano_minus_mul_lt_mul : forall x y z,
    oring_lt O x y -> oring_lt O (oring_zero O) z ->
    oring_lt O (oring_mul O x z) (oring_mul O y z);
  peano_minus_mul_add_distr : forall x y z,
    oring_mul O x (oring_add O y z) =
    oring_add O (oring_mul O x y) (oring_mul O x z);
  peano_minus_lt_irrefl : forall x, ~ oring_lt O x x;
  peano_minus_lt_trans : forall x y z,
    oring_lt O x y -> oring_lt O y z -> oring_lt O x z;
  peano_minus_lt_trichotomy : forall x y,
    oring_lt O x y \/ x = y \/ oring_lt O y x
}.

Definition peano_minus_le_refl {M : Type} {O : oring_carrier M} :
    forall x, peano_minus_le O x x := fun x => or_introl eq_refl.

Definition peano_minus_lt_le {M : Type} {O : oring_carrier M} :
    forall x y, oring_lt O x y -> peano_minus_le O x y :=
  fun x y H => or_intror H.

Lemma peano_minus_le_trans : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y z,
  peano_minus_le O x y -> peano_minus_le O y z -> peano_minus_le O x z.
Proof.
  intros M O H x y z [-> | Hxy] [-> | Hyz].
  - apply peano_minus_le_refl.
  - now apply peano_minus_lt_le.
  - now apply peano_minus_lt_le.
  - right. eapply peano_minus_lt_trans; eauto.
Qed.

Lemma peano_minus_le_antisym : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y,
  peano_minus_le O x y -> peano_minus_le O y x -> x = y.
Proof.
  intros M O H x y Hxy Hyx.
  destruct Hxy as [Hxy | Hxy]; [exact Hxy |].
  destruct Hyx as [Hyx | Hyx]; [now symmetry |].
  exfalso. apply (@peano_minus_lt_irrefl M O H x).
  exact (@peano_minus_lt_trans M O H x y x Hxy Hyx).
Qed.

Lemma peano_minus_le_total : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y,
  peano_minus_le O x y \/ peano_minus_le O y x.
Proof.
  intros M O H x y.
  destruct (peano_minus_lt_trichotomy H x y) as [Hxy | [-> | Hyx]].
  - left. now right.
  - left. now left.
  - right. now right.
Qed.

Lemma peano_minus_add_zero_left : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x,
  oring_add O (oring_zero O) x = x.
Proof.
  intros M O H x.
  rewrite (@peano_minus_add_comm M O H (oring_zero O) x).
  apply (@peano_minus_add_zero M O H x).
Qed.

Lemma peano_minus_add_right_cancel : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y z,
  oring_add O x z = oring_add O y z -> x = y.
Proof.
  intros M O H x y z Heq.
  destruct (@peano_minus_lt_trichotomy M O H x y)
    as [Hxy | [Hxy | Hyx]]; [|exact Hxy|].
  - pose proof (@peano_minus_add_lt_add M O H x y z Hxy) as Hlt.
    rewrite <- Heq in Hlt.
    exact (False_rect _ (@peano_minus_lt_irrefl M O H _ Hlt)).
  - pose proof (@peano_minus_add_lt_add M O H y x z Hyx) as Hlt.
    rewrite Heq in Hlt.
    exact (False_rect _ (@peano_minus_lt_irrefl M O H _ Hlt)).
Qed.

Lemma peano_minus_positive_eq_add_one : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x,
  oring_lt O (oring_zero O) x ->
  exists y, x = oring_add O y (oring_one O).
Proof.
  intros M O H x Hpos.
  destruct (@peano_minus_one_le_of_zero_lt M O H x Hpos)
    as [Hone | Hone].
  - exists (oring_zero O).
    rewrite (peano_minus_add_zero_left H). now symmetry.
  - destruct (@peano_minus_add_eq_of_lt M O H
      (oring_one O) x Hone) as [y Hy].
    exists y. rewrite (@peano_minus_add_comm M O H y (oring_one O)).
    now symmetry.
Qed.

Lemma peano_minus_lt_add_one : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x,
  oring_lt O x (oring_add O x (oring_one O)).
Proof.
  intros M O H x.
  pose proof (@peano_minus_add_lt_add M O H
    (oring_zero O) (oring_one O) x
    (@peano_minus_zero_lt_one M O H)) as Hlt.
  rewrite (peano_minus_add_zero_left H),
    (@peano_minus_add_comm M O H (oring_one O) x) in Hlt.
  exact Hlt.
Qed.

Lemma peano_minus_le_lt_add_one : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y,
  peano_minus_le O x y ->
  oring_lt O x (oring_add O y (oring_one O)).
Proof.
  intros M O H x y [-> | Hxy].
  - apply peano_minus_lt_add_one. exact H.
  - eapply (@peano_minus_lt_trans M O H).
    + exact Hxy.
    + apply peano_minus_lt_add_one. exact H.
Qed.

Lemma peano_minus_le_iff_lt_add_one : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y,
  peano_minus_le O x y <->
  oring_lt O x (oring_add O y (oring_one O)).
Proof.
  intros M O H x y. split.
  - apply peano_minus_le_lt_add_one. exact H.
  - intro Hlt.
    destruct (@peano_minus_add_eq_of_lt M O H x
      (oring_add O y (oring_one O)) Hlt) as [z Hz].
    destruct (@peano_minus_zero_le M O H z) as [Hzero | Hpos].
    + subst z. rewrite (@peano_minus_add_zero M O H x) in Hz.
      subst x. exfalso.
      exact (@peano_minus_lt_irrefl M O H
        (oring_add O y (oring_one O)) Hlt).
    + destruct (peano_minus_positive_eq_add_one H Hpos) as [z' Hz'].
      assert (Hxy : oring_add O x z' = y).
      { apply (@peano_minus_add_right_cancel M O H _ _ (oring_one O)).
        rewrite (@peano_minus_add_assoc M O H x z' (oring_one O)).
        rewrite <- Hz'. exact Hz. }
      destruct (@peano_minus_zero_le M O H z') as [Hzero | Hpos'].
      * left. rewrite <- Hxy, <- Hzero.
        symmetry. apply (@peano_minus_add_zero M O H x).
      * right.
        pose proof (@peano_minus_add_lt_add M O H
          (oring_zero O) z' x Hpos') as Hadd.
        rewrite (peano_minus_add_zero_left H),
          (@peano_minus_add_comm M O H z' x), Hxy in Hadd.
        exact Hadd.
Qed.

Definition nat_peano_minus_laws :
    peano_minus_laws nat_oring_carrier.
Proof.
  constructor.
  - apply Nat.add_0_r.
  - intros. symmetry. apply Nat.add_assoc.
  - apply Nat.add_comm.
  - intros x y Hxy. exists (y - x).
    apply Arith_base.le_plus_minus_r_stt.
    apply Nat.lt_le_incl. exact Hxy.
  - intro x. destruct x as [|x].
    + left. reflexivity.
    + right. change (0 < S x). lia.
  - change (0 < 1). lia.
  - intros x Hx. destruct x as [|[|x]].
    + inversion Hx.
    + left. reflexivity.
    + right. change (1 < S (S x)). lia.
  - intros x y z Hxy. change (x < y) in Hxy.
    change (x + z < y + z). lia.
  - apply Nat.mul_0_r.
  - apply Nat.mul_1_r.
  - intros. symmetry. apply Nat.mul_assoc.
  - apply Nat.mul_comm.
  - intros x y z Hxy Hz. change (x < y) in Hxy.
    change (0 < z) in Hz. change (x * z < y * z).
    apply Nat.mul_lt_mono_pos_r; assumption.
  - apply Nat.mul_add_distr_l.
  - intro x. change (~ x < x). lia.
  - intros x y z Hxy Hyz. change (x < y) in Hxy.
    change (y < z) in Hyz. change (x < z). lia.
  - intros x y. change (x < y \/ x = y \/ y < x). lia.
Defined.
