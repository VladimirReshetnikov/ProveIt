(**
  Functions and relations available in Peano-minus models.

  This begins the port of
  [Foundation/FirstOrder/Arithmetic/PeanoMinus/Functions.lean] with its
  foundational modified subtraction.  The operation is selected from the
  source's exact unique specification; all algebraic reasoning remains
  constructive once that single noncomputable selection has been made.
*)

From Stdlib Require Import Logic.ClassicalEpsilon.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition peano_minus_sub_spec {M : Type} (O : oring_carrier M)
    (a b c : M) : Prop :=
  (peano_minus_le O b a -> a = oring_add O b c) /\
  (oring_lt O a b -> c = oring_zero O).

Lemma peano_minus_sub_spec_exists : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  exists c, peano_minus_sub_spec O a b c.
Proof.
  intros M O H a b.
  destruct (@peano_minus_lt_trichotomy M O H a b)
    as [Hab | [Hab | Hba]].
  - exists (oring_zero O). split.
    + intro Hge. exfalso. exact (peano_minus_lt_not_ge H Hab Hge).
    + intros _. reflexivity.
  - subst b. exists (oring_zero O). split.
    + intro Hge. symmetry. apply (@peano_minus_add_zero M O H).
    + intro Hlt. exfalso. exact (@peano_minus_lt_irrefl M O H _ Hlt).
  - destruct (@peano_minus_add_eq_of_lt M O H b a Hba) as [c Hc].
    exists c. split.
    + intros _. now symmetry.
    + intro Hab. exfalso.
      exact (@peano_minus_lt_irrefl M O H a
        (@peano_minus_lt_trans M O H a b a Hab Hba)).
Qed.

Lemma peano_minus_sub_spec_functional : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b c d,
  peano_minus_sub_spec O a b c ->
  peano_minus_sub_spec O a b d -> c = d.
Proof.
  intros M O H a b c d Hc Hd.
  destruct (@peano_minus_lt_trichotomy M O H a b)
    as [Hab | [Hab | Hba]].
  - rewrite (proj2 Hc Hab), (proj2 Hd Hab). reflexivity.
  - subst b.
    apply (@peano_minus_add_left_cancel M O H c d a).
    rewrite <- (proj1 Hc (peano_minus_le_refl a)),
      <- (proj1 Hd (peano_minus_le_refl a)). reflexivity.
  - apply (@peano_minus_add_left_cancel M O H c d b).
    rewrite <- (proj1 Hc (peano_minus_lt_le Hba)),
      <- (proj1 Hd (peano_minus_lt_le Hba)). reflexivity.
Qed.

Lemma peano_minus_sub_spec_exists_unique : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  exists! c, peano_minus_sub_spec O a b c.
Proof.
  intros M O H a b.
  destruct (peano_minus_sub_spec_exists H a b) as [c Hc].
  exists c. split; [exact Hc|].
  intros d Hd. now apply (peano_minus_sub_spec_functional H Hc Hd).
Qed.

Definition peano_minus_sub {M : Type} (O : oring_carrier M)
    (a b : M) : M :=
  epsilon (inhabits (oring_zero O)) (peano_minus_sub_spec O a b).

Lemma peano_minus_sub_specification : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_sub_spec O a b (peano_minus_sub O a b).
Proof.
  intros M O H a b. unfold peano_minus_sub.
  apply epsilon_spec. apply (peano_minus_sub_spec_exists H).
Qed.

Lemma peano_minus_sub_spec_of_ge : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_le O b a ->
  a = oring_add O b (peano_minus_sub O a b).
Proof.
  intros M O H a b Hge.
  exact (proj1 (peano_minus_sub_specification H a b) Hge).
Qed.

Lemma peano_minus_sub_spec_of_lt : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O a b -> peano_minus_sub O a b = oring_zero O.
Proof.
  intros M O H a b Hlt.
  exact (proj2 (peano_minus_sub_specification H a b) Hlt).
Qed.

Lemma peano_minus_sub_eq_iff : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b c,
  c = peano_minus_sub O a b <-> peano_minus_sub_spec O a b c.
Proof.
  intros M O H a b c. split.
  - intros ->. apply (peano_minus_sub_specification H).
  - intro Hc. apply (peano_minus_sub_spec_functional H Hc).
    apply (peano_minus_sub_specification H).
Qed.

Lemma peano_minus_sub_le_self : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_le O (peano_minus_sub O a b) a.
Proof.
  intros M O H a b.
  destruct (@peano_minus_lt_trichotomy M O H a b)
    as [Hab | [Hab | Hba]].
  - rewrite (peano_minus_sub_spec_of_lt H Hab).
    apply (@peano_minus_zero_le M O H).
  - subst b.
    assert (Hself : peano_minus_sub O a a = oring_zero O).
    { symmetry.
      apply (proj2 (peano_minus_sub_eq_iff H a a (oring_zero O))). split.
      - intro Hle. symmetry. apply (peano_minus_add_zero H).
      - intro Hlt. exfalso. exact (peano_minus_lt_irrefl H Hlt). }
    rewrite Hself. apply (@peano_minus_zero_le M O H).
  - pose proof (peano_minus_sub_spec_of_ge H
      (peano_minus_lt_le Hba)) as Hspec.
    pose proof (peano_minus_add_le_add_right H
      (x := oring_zero O) (y := b) (peano_minus_sub O a b)
      (@peano_minus_zero_le M O H b)) as Hle.
    rewrite (peano_minus_add_zero_left H), <- Hspec in Hle.
    exact Hle.
Qed.

Lemma peano_minus_sub_self : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a,
  peano_minus_sub O a a = oring_zero O.
Proof.
  intros M O H a.
  symmetry.
  apply (proj2 (peano_minus_sub_eq_iff H a a (oring_zero O))). split.
  - intro Hle. symmetry. apply (@peano_minus_add_zero M O H).
  - intro Hlt. exfalso. exact (@peano_minus_lt_irrefl M O H a Hlt).
Qed.

Lemma peano_minus_sub_of_le : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_le O a b -> peano_minus_sub O a b = oring_zero O.
Proof.
  intros M O H a b [Hab | Hab].
  - subst b. apply (peano_minus_sub_self H).
  - now apply (peano_minus_sub_spec_of_lt H).
Qed.

Lemma peano_minus_sub_add_self_of_le : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_le O b a ->
  oring_add O (peano_minus_sub O a b) b = a.
Proof.
  intros M O H a b Hba.
  rewrite (@peano_minus_add_comm M O H).
  symmetry. now apply (peano_minus_sub_spec_of_ge H).
Qed.

Lemma peano_minus_add_sub_self_of_le : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_le O b a ->
  oring_add O b (peano_minus_sub O a b) = a.
Proof.
  intros M O H a b Hba. symmetry.
  now apply (peano_minus_sub_spec_of_ge H).
Qed.

Lemma peano_minus_add_sub_self : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_sub O (oring_add O a b) b = a.
Proof.
  intros M O H a b.
  assert (Hle : peano_minus_le O b (oring_add O a b)).
  { pose proof (peano_minus_add_le_add_left H
      (x := oring_zero O) (y := a) b
      (@peano_minus_zero_le M O H a)) as Hle.
    rewrite (@peano_minus_add_zero M O H b),
      (@peano_minus_add_comm M O H b a) in Hle. exact Hle. }
  pose proof (peano_minus_sub_spec_of_ge H Hle) as Hspec.
  apply (@peano_minus_add_left_cancel M O H _ _ b).
  rewrite <- Hspec, (@peano_minus_add_comm M O H b a). reflexivity.
Qed.

Lemma peano_minus_zero_sub : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a,
  peano_minus_sub O (oring_zero O) a = oring_zero O.
Proof.
  intros M O H a. apply (peano_minus_sub_of_le H).
  apply (@peano_minus_zero_le M O H).
Qed.

Lemma peano_minus_sub_zero : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a,
  peano_minus_sub O a (oring_zero O) = a.
Proof.
  intros M O H a.
  pose proof (peano_minus_sub_spec_of_ge H
    (@peano_minus_zero_le M O H a)) as Hspec.
  rewrite (peano_minus_add_zero_left H) in Hspec. now symmetry.
Qed.

Lemma peano_minus_sub_remove_left : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b c,
  a = oring_add O b c -> peano_minus_sub O a c = b.
Proof.
  intros M O H a b c ->.
  apply (peano_minus_add_sub_self H).
Qed.

Lemma peano_minus_sub_sub : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b c,
  peano_minus_sub O (peano_minus_sub O a b) c =
  peano_minus_sub O a (oring_add O b c).
Proof.
  intros M O H a b c.
  apply (proj2 (peano_minus_sub_eq_iff H a (oring_add O b c)
    (peano_minus_sub O (peano_minus_sub O a b) c))).
  split.
  - intro Hsum.
    assert (Hbadd : peano_minus_le O b (oring_add O b c)).
    { pose proof (peano_minus_add_le_add_left H
        (x := oring_zero O) (y := c) b
        (@peano_minus_zero_le M O H c)) as Hbc.
      now rewrite (@peano_minus_add_zero M O H b) in Hbc. }
    pose proof (@peano_minus_le_trans M O H b (oring_add O b c) a
      Hbadd Hsum) as Hb.
    pose proof (peano_minus_sub_spec_of_ge H Hb) as Hab.
    assert (Hc : peano_minus_le O c (peano_minus_sub O a b)).
    { apply (@peano_minus_le_of_add_le_add_left M O H c
        (peano_minus_sub O a b) b).
      now rewrite <- Hab. }
    pose proof (peano_minus_sub_spec_of_ge H Hc) as Hbc.
    rewrite Hbc in Hab.
    rewrite (@peano_minus_add_assoc M O H b c
      (peano_minus_sub O (peano_minus_sub O a b) c)).
    exact Hab.
  - intro Hsum.
    destruct (@peano_minus_lt_trichotomy M O H a b)
      as [Hab | [Hab | Hba]].
    + rewrite (peano_minus_sub_spec_of_lt H Hab).
      apply (peano_minus_zero_sub H).
    + subst a. rewrite (peano_minus_sub_self H).
      apply (peano_minus_zero_sub H).
    + apply (peano_minus_sub_spec_of_lt H).
      apply (@peano_minus_lt_of_add_lt_add_left M O H
        (peano_minus_sub O a b) c b).
      pose proof (peano_minus_sub_spec_of_ge H
        (peano_minus_lt_le Hba)) as Hab.
      now rewrite <- Hab.
Qed.

Lemma peano_minus_pred_lt_self_of_pos : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall a,
  oring_lt O (oring_zero O) a ->
  oring_lt O (peano_minus_sub O a (oring_one O)) a.
Proof.
  intros M O H a Hpos.
  destruct (peano_minus_positive_eq_add_one H Hpos) as [d ->].
  rewrite (peano_minus_add_sub_self H).
  apply (peano_minus_lt_add_one H).
Qed.

Lemma peano_minus_sub_mul : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b c,
  peano_minus_le O b a ->
  oring_mul O (peano_minus_sub O a b) c =
  peano_minus_sub O (oring_mul O a c) (oring_mul O b c).
Proof.
  intros M O H a b c Hba. symmetry.
  apply (peano_minus_sub_remove_left H).
  pose proof (peano_minus_sub_spec_of_ge H Hba) as Hab.
  rewrite Hab at 1.
  rewrite (@peano_minus_add_mul_distr M O H),
    (@peano_minus_add_comm M O H
      (oring_mul O b c) (oring_mul O (peano_minus_sub O a b) c)).
  reflexivity.
Qed.

Lemma peano_minus_mul_sub : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b c,
  peano_minus_le O b a ->
  oring_mul O c (peano_minus_sub O a b) =
  peano_minus_sub O (oring_mul O c a) (oring_mul O c b).
Proof.
  intros M O H a b c Hba.
  rewrite (@peano_minus_mul_comm M O H c (peano_minus_sub O a b)),
    (@peano_minus_mul_comm M O H c a),
    (@peano_minus_mul_comm M O H c b).
  exact (@peano_minus_sub_mul M O H a b c Hba).
Qed.

Lemma peano_minus_add_sub_of_le : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b c,
  peano_minus_le O c b ->
  peano_minus_sub O (oring_add O a b) c =
  oring_add O a (peano_minus_sub O b c).
Proof.
  intros M O H a b c Hcb.
  apply (peano_minus_sub_remove_left H).
  pose proof (peano_minus_sub_spec_of_ge H Hcb) as Hbc.
  rewrite Hbc at 1.
  rewrite (@peano_minus_add_comm M O H c (peano_minus_sub O b c)) at 1.
  symmetry. apply (@peano_minus_add_assoc M O H).
Qed.

Lemma peano_minus_pos_sub_iff_lt : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O (oring_zero O) (peano_minus_sub O a b) <->
  oring_lt O b a.
Proof.
  intros M O H a b. split.
  - intro Hpos.
    destruct (@peano_minus_lt_trichotomy M O H a b)
      as [Hab | [Hab | Hba]]; [| |exact Hba].
    + rewrite (peano_minus_sub_spec_of_lt H Hab) in Hpos.
      exfalso. exact (@peano_minus_lt_irrefl M O H _ Hpos).
    + subst b. rewrite (peano_minus_sub_self H) in Hpos.
      exfalso. exact (@peano_minus_lt_irrefl M O H _ Hpos).
  - intro Hba.
    destruct (@peano_minus_zero_le M O H (peano_minus_sub O a b))
      as [Hzero | Hpos]; [|exact Hpos].
    exfalso.
    pose proof (peano_minus_sub_spec_of_ge H
      (peano_minus_lt_le Hba)) as Hspec.
    rewrite <- Hzero, (@peano_minus_add_zero M O H b) in Hspec.
    subst a. exact (@peano_minus_lt_irrefl M O H b Hba).
Qed.

Lemma peano_minus_sub_eq_zero_iff_le : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_sub O a b = oring_zero O <-> peano_minus_le O a b.
Proof.
  intros M O H a b. split.
  - intro Hzero.
    destruct (@peano_minus_lt_trichotomy M O H a b)
      as [Hab | [Hab | Hba]].
    + now right.
    + now left.
    + exfalso. apply (@peano_minus_lt_irrefl M O H (oring_zero O)).
      pose proof (proj2 (peano_minus_pos_sub_iff_lt H a b) Hba) as Hpos.
      now rewrite Hzero in Hpos.
  - apply (peano_minus_sub_of_le H).
Qed.
