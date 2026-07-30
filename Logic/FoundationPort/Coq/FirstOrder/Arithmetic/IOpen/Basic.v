(** Semantic division from open-induction least-number reasoning. *)

From Stdlib Require Import Logic.ClassicalEpsilon.
From Foundation.FirstOrder.Arithmetic Require Import Schemata.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic Functions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition iopen_div_pos_spec {M} (O : oring_carrier M)
    (a b u : M) : Prop :=
  peano_minus_le O (oring_mul O b u) a /\
  oring_lt O a (oring_mul O b (oring_add O u (oring_one O))).

Lemma iopen_lt_mul_add_one : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O (oring_zero O) b ->
  oring_lt O a (oring_mul O b (oring_add O a (oring_one O))).
Proof.
  intros M O H a b Hb.
  pose proof (@peano_minus_le_mul_self_of_pos_left M O H a b Hb) as Hle.
  pose proof (@peano_minus_add_lt_add M O H
    (oring_zero O) b (oring_mul O b a) Hb) as Hlt.
  rewrite (peano_minus_add_zero_left H),
    (@peano_minus_add_comm M O H b (oring_mul O b a)) in Hlt.
  assert (Hchain : oring_lt O a
      (oring_add O (oring_mul O b a) b)).
  { destruct Hle as [Hle | Hle].
    - rewrite Hle at 1. exact Hlt.
    - exact (@peano_minus_lt_trans M O H _ _ _ Hle Hlt). }
  rewrite (@peano_minus_mul_add_distr M O H b a (oring_one O)),
    (@peano_minus_mul_one M O H b).
  exact Hchain.
Qed.

Lemma iopen_div_exists_unique_pos : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O (oring_zero O) b ->
  exists! u, iopen_div_pos_spec O a b u.
Proof.
  intros M O H Hleast a b Hb.
  assert (Hboundary : exists u,
      peano_minus_le O (oring_mul O b u) a /\
      ~ peano_minus_le O
        (oring_mul O b (oring_add O u (oring_one O))) a).
  { apply (arithmetic_boundary_of_least_number H Hleast
      (P := fun u => peano_minus_le O (oring_mul O b u) a)).
    - rewrite (@peano_minus_mul_zero M O H b).
      apply (@peano_minus_zero_le M O H).
    - exists (oring_add O a (oring_one O)).
      apply (peano_minus_lt_not_ge H
        (iopen_lt_mul_add_one H a Hb)). }
  destruct Hboundary as [u [Hulo Hunext]].
  assert (Hu : iopen_div_pos_spec O a b u).
  { split; [exact Hulo | now apply (peano_minus_lt_of_not_le H)]. }
  exists u. split; [exact Hu |].
  intros v Hv.
  assert (Hnotlt : ~ oring_lt O v u).
  { intro Hvu.
    pose proof (peano_minus_add_one_le_of_lt H Hvu) as Hsucc.
    pose proof (peano_minus_mul_le_mul_left H
      (x := oring_add O v (oring_one O)) (y := u) b Hsucc) as Hmul.
    pose proof (@peano_minus_le_trans M O H _ _ _ Hmul (proj1 Hu)) as Hle.
    exact (peano_minus_lt_not_ge H (proj2 Hv) Hle). }
  assert (Hnotgt : ~ oring_lt O u v).
  { intro Huv.
    pose proof (peano_minus_add_one_le_of_lt H Huv) as Hsucc.
    pose proof (peano_minus_mul_le_mul_left H
      (x := oring_add O u (oring_one O)) (y := v) b Hsucc) as Hmul.
    pose proof (@peano_minus_le_trans M O H _ _ _ Hmul (proj1 Hv)) as Hle.
    exact (peano_minus_lt_not_ge H (proj2 Hu) Hle). }
  destruct (@peano_minus_lt_trichotomy M O H v u)
    as [Hvu | [Heq | Huv]]; [contradiction | symmetry; exact Heq | contradiction].
Qed.

Definition iopen_div_spec {M} (O : oring_carrier M)
    (a b u : M) : Prop :=
  (oring_lt O (oring_zero O) b -> iopen_div_pos_spec O a b u) /\
  (b = oring_zero O -> u = oring_zero O).

Lemma iopen_div_exists_unique : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, exists! u, iopen_div_spec O a b u.
Proof.
  intros M O H Hleast a b.
  destruct (@peano_minus_zero_le M O H b) as [Hbzero | Hbpos].
  - symmetry in Hbzero. subst b. exists (oring_zero O). split.
    + split.
      * intro Hbad. exfalso. exact (@peano_minus_lt_irrefl M O H _ Hbad).
      * intros _. reflexivity.
    + intros u Hu. symmetry. exact (proj2 Hu eq_refl).
  - destruct (iopen_div_exists_unique_pos H Hleast a Hbpos)
      as [u [Hu Huniq]].
    exists u. split.
    + split; [intros _; exact Hu |].
      intro Hbzero. subst b.
      exact (False_rect _ (@peano_minus_lt_irrefl M O H _ Hbpos)).
    + intros v Hv. apply Huniq. exact (proj1 Hv Hbpos).
Qed.

Definition iopen_div {M} (O : oring_carrier M) (a b : M) : M :=
  epsilon (inhabits (oring_zero O)) (iopen_div_spec O a b).

Lemma iopen_div_specification : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, iopen_div_spec O a b (iopen_div O a b).
Proof.
  intros M O H Hleast a b. unfold iopen_div.
  apply epsilon_spec. destruct (iopen_div_exists_unique H Hleast a b)
    as [u [Hu _]]. now exists u.
Qed.

Lemma iopen_mul_div_le_pos : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O (oring_zero O) b ->
  peano_minus_le O (oring_mul O b (iopen_div O a b)) a.
Proof.
  intros M O H Hleast a b Hb.
  exact (proj1 (proj1 (iopen_div_specification H Hleast a b) Hb)).
Qed.

Lemma iopen_lt_mul_div_succ : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O (oring_zero O) b ->
  oring_lt O a
    (oring_mul O b (oring_add O (iopen_div O a b) (oring_one O))).
Proof.
  intros M O H Hleast a b Hb.
  exact (proj2 (proj1 (iopen_div_specification H Hleast a b) Hb)).
Qed.

Lemma iopen_div_zero : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, iopen_div O a (oring_zero O) = oring_zero O.
Proof.
  intros M O H Hleast a.
  exact (proj2 (iopen_div_specification H Hleast a (oring_zero O)) eq_refl).
Qed.
