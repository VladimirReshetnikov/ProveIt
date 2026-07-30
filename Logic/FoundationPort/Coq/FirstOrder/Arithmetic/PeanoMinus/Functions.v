(**
  Functions and relations available in Peano-minus models.

  This begins the port of
  [Foundation/FirstOrder/Arithmetic/PeanoMinus/Functions.lean] with its
  foundational modified subtraction.  The operation is selected from the
  source's exact unique specification; all algebraic reasoning remains
  constructive once that single noncomputable selection has been made.
*)

From Stdlib Require Import Logic.ClassicalEpsilon Logic.ClassicalDescription.
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

Lemma peano_minus_sub_succ_add_succ : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall x y z,
  oring_lt O y x ->
  oring_add O
    (peano_minus_sub O x (oring_add O y (oring_one O)))
    (oring_add O z (oring_one O)) =
  oring_add O (peano_minus_sub O x y) z.
Proof.
  intros M O H x y z Hyx.
  rewrite <- (@peano_minus_sub_sub M O H x y (oring_one O)).
  rewrite (@peano_minus_add_comm M O H z (oring_one O)),
    <- (@peano_minus_add_assoc M O H).
  rewrite (peano_minus_sub_add_self_of_le H).
  - reflexivity.
  - apply (@peano_minus_one_le_of_zero_lt M O H).
    destruct (@peano_minus_zero_le M O H
      (peano_minus_sub O x y)) as [Hzero | Hpos]; [|exact Hpos].
    exfalso.
    pose proof (peano_minus_sub_spec_of_ge H
      (peano_minus_lt_le Hyx)) as Hspec.
    rewrite <- Hzero, (@peano_minus_add_zero M O H y) in Hspec.
    subst x. exact (@peano_minus_lt_irrefl M O H y Hyx).
Qed.

Lemma peano_minus_le_sub_one_of_lt : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O a b ->
  peano_minus_le O a (peano_minus_sub O b (oring_one O)).
Proof.
  intros M O H a b Hab.
  apply (proj2 (peano_minus_le_iff_lt_add_one H a
    (peano_minus_sub O b (oring_one O)))).
  assert (Hb : oring_lt O (oring_zero O) b).
  { destruct (@peano_minus_zero_le M O H a) as [Ha | Ha].
    - now rewrite Ha.
    - exact (@peano_minus_lt_trans M O H _ _ _ Ha Hab). }
  pose proof (@peano_minus_one_le_of_zero_lt M O H b Hb) as Hone.
  now rewrite (peano_minus_sub_add_self_of_le H Hone).
Qed.

Lemma peano_minus_sub_le_iff_right : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall a b c,
  peano_minus_le O (peano_minus_sub O a b) c <->
  peano_minus_le O a (oring_add O c b).
Proof.
  intros M O H a b c.
  destruct (@peano_minus_lt_trichotomy M O H a b)
    as [Hab | [Hab | Hba]].
  - rewrite (peano_minus_sub_spec_of_lt H Hab). split.
    + intro Hzero. eapply (@peano_minus_le_trans M O H a b); [now right|].
      pose proof (peano_minus_add_le_add_right H
        (x := oring_zero O) (y := c) b
        (@peano_minus_zero_le M O H c)) as Hle.
      now rewrite (peano_minus_add_zero_left H) in Hle.
    + intro Hle. apply (@peano_minus_zero_le M O H).
  - subst a. rewrite (peano_minus_sub_self H). split.
    + intro Hzero. pose proof (peano_minus_add_le_add_right H
        (x := oring_zero O) (y := c) b
        (@peano_minus_zero_le M O H c)) as Hle.
      now rewrite (peano_minus_add_zero_left H) in Hle.
    + intro Hle. apply (@peano_minus_zero_le M O H).
  - pose proof (peano_minus_sub_spec_of_ge H
      (peano_minus_lt_le Hba)) as Hspec.
    split.
    + intro Hle.
      pose proof (peano_minus_add_le_add_left H
        (x := peano_minus_sub O a b) (y := c) b Hle) as Hadd.
      rewrite <- Hspec, (@peano_minus_add_comm M O H b c) in Hadd.
      exact Hadd.
    + intro Hle.
      apply (@peano_minus_le_of_add_le_add_left M O H
        (peano_minus_sub O a b) c b).
      rewrite <- Hspec, (@peano_minus_add_comm M O H b c).
      exact Hle.
Qed.

Lemma peano_minus_sub_lt_iff_right : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall a b c,
  peano_minus_le O b a ->
  (oring_lt O (peano_minus_sub O a b) c <->
   oring_lt O a (oring_add O c b)).
Proof.
  intros M O H a b c Hba.
  pose proof (peano_minus_sub_spec_of_ge H Hba) as Hspec.
  split.
  - intro Hlt.
    pose proof (@peano_minus_add_lt_add M O H
      (peano_minus_sub O a b) c b Hlt) as Hadd.
    rewrite (@peano_minus_add_comm M O H
      (peano_minus_sub O a b) b), <- Hspec in Hadd.
    exact Hadd.
  - intro Hlt.
    apply (@peano_minus_lt_of_add_lt_add_left M O H
      (peano_minus_sub O a b) c b).
    rewrite <- Hspec, (@peano_minus_add_comm M O H b c).
    exact Hlt.
Qed.

Definition peano_minus_dvd {M : Type} (O : oring_carrier M)
    (a b : M) : Prop :=
  exists c, b = oring_mul O a c.

Lemma peano_minus_le_mul_self_of_pos_left : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O (oring_zero O) b ->
  peano_minus_le O a (oring_mul O b a).
Proof.
  intros M O H a b Hb.
  pose proof (peano_minus_mul_le_mul_right H
    (x := oring_one O) (y := b) a
    (@peano_minus_one_le_of_zero_lt M O H b Hb)) as Hle.
  now rewrite (@peano_minus_one_mul M O H a) in Hle.
Qed.

Lemma peano_minus_le_mul_self_of_pos_right : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O (oring_zero O) b ->
  peano_minus_le O a (oring_mul O a b).
Proof.
  intros M O H a b Hb.
  rewrite (@peano_minus_mul_comm M O H a b).
  now apply (peano_minus_le_mul_self_of_pos_left H).
Qed.

Lemma peano_minus_dvd_iff_bounded : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_dvd O a b <->
  exists c, peano_minus_le O c b /\ b = oring_mul O a c.
Proof.
  intros M O H a b. split.
  - intros [c Hc].
    destruct (@peano_minus_zero_le M O H a) as [Ha | Ha].
    + symmetry in Ha. subst a.
      rewrite (@peano_minus_zero_mul M O H c) in Hc. subst b.
      exists (oring_zero O). split.
      * apply (@peano_minus_zero_le M O H).
      * symmetry. apply (@peano_minus_zero_mul M O H).
    + exists c. split.
      * rewrite Hc.
        exact (@peano_minus_le_mul_self_of_pos_left M O H c a Ha).
      * exact Hc.
  - intros [c [_ Hc]]. now exists c.
Qed.

Lemma peano_minus_le_of_dvd : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O (oring_zero O) b ->
  peano_minus_dvd O a b -> peano_minus_le O a b.
Proof.
  intros M O H a b Hb [c Hc].
  destruct (@peano_minus_zero_le M O H c) as [Hcz | Hcp].
  - symmetry in Hcz. subst c.
    rewrite (@peano_minus_mul_zero M O H a) in Hc. subst b.
    exfalso. exact (@peano_minus_lt_irrefl M O H _ Hb).
  - rewrite Hc.
    exact (@peano_minus_le_mul_self_of_pos_right M O H a c Hcp).
Qed.

Lemma peano_minus_not_dvd_of_lt : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O (oring_zero O) b -> oring_lt O b a ->
  ~ peano_minus_dvd O a b.
Proof.
  intros M O H a b Hb Hba Hdvd.
  exact (peano_minus_lt_not_ge H Hba
    (peano_minus_le_of_dvd H Hb Hdvd)).
Qed.

Lemma peano_minus_dvd_antisym : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_dvd O a b -> peano_minus_dvd O b a -> a = b.
Proof.
  intros M O H a b Hab Hba.
  destruct (@peano_minus_zero_le M O H a) as [Haz | Hap].
  - symmetry in Haz. subst a.
    destruct Hab as [c Hbc].
    rewrite (@peano_minus_zero_mul M O H c) in Hbc. now symmetry.
  - destruct (@peano_minus_zero_le M O H b) as [Hbz | Hbp].
    + symmetry in Hbz. subst b.
      destruct Hba as [c Hac].
      rewrite (@peano_minus_zero_mul M O H c) in Hac. exact Hac.
    + apply (@peano_minus_le_antisym M O H).
      * exact (peano_minus_le_of_dvd H Hbp Hab).
      * exact (peano_minus_le_of_dvd H Hap Hba).
Qed.

Lemma peano_minus_dvd_one_iff : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a,
  peano_minus_dvd O a (oring_one O) <-> a = oring_one O.
Proof.
  intros M O H a. split.
  - intro Ha. apply (peano_minus_dvd_antisym H Ha).
    exists a. symmetry. apply (@peano_minus_one_mul M O H).
  - intros ->. exists (oring_one O).
    symmetry. apply (@peano_minus_mul_one M O H).
Qed.

Definition peano_minus_is_prime {M : Type} (O : oring_carrier M)
    (p : M) : Prop :=
  oring_lt O (oring_one O) p /\
  forall a, peano_minus_le O a p -> peano_minus_dvd O a p ->
    a = oring_one O \/ a = p.

Lemma peano_minus_prime_gt_one : forall M (O : oring_carrier M),
  forall p, peano_minus_is_prime O p -> oring_lt O (oring_one O) p.
Proof.
  intros M O p Hp. exact (proj1 Hp).
Qed.

Lemma peano_minus_prime_pos : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall p,
  peano_minus_is_prime O p -> oring_lt O (oring_zero O) p.
Proof.
  intros M O H p Hp.
  exact (@peano_minus_lt_trans M O H
    (oring_zero O) (oring_one O) p
    (@peano_minus_zero_lt_one M O H) (proj1 Hp)).
Qed.

Lemma peano_minus_prime_divisor : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall p a,
  peano_minus_is_prime O p -> peano_minus_dvd O a p ->
  a = oring_one O \/ a = p.
Proof.
  intros M O H p a Hp Ha.
  apply (proj2 Hp a).
  - exact (peano_minus_le_of_dvd H (peano_minus_prime_pos H Hp) Ha).
  - exact Ha.
Qed.

Lemma peano_minus_one_not_prime : forall M (O : oring_carrier M),
  peano_minus_laws O -> ~ peano_minus_is_prime O (oring_one O).
Proof.
  intros M O H Hp.
  exact (@peano_minus_lt_irrefl M O H (oring_one O) (proj1 Hp)).
Qed.

Lemma peano_minus_prime_ne_zero : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall p,
  peano_minus_is_prime O p -> p <> oring_zero O.
Proof.
  intros M O H p Hp Heq. subst p.
  exact (@peano_minus_lt_irrefl M O H (oring_zero O)
    (peano_minus_prime_pos H Hp)).
Qed.

Lemma peano_minus_prime_ne_one : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall p,
  peano_minus_is_prime O p -> p <> oring_one O.
Proof.
  intros M O H p Hp Heq. subst p.
  now apply (@peano_minus_one_not_prime M O H).
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

Definition peano_minus_min {M : Type} (O : oring_carrier M)
    (H : peano_minus_laws O) (x y : M) : M :=
  if excluded_middle_informative (peano_minus_le O x y) then x else y.

Definition peano_minus_max {M : Type} (O : oring_carrier M)
    (H : peano_minus_laws O) (x y : M) : M :=
  if excluded_middle_informative (peano_minus_le O x y) then y else x.

Lemma peano_minus_min_of_le : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y,
  peano_minus_le O x y -> @peano_minus_min M O H x y = x.
Proof.
  intros M O H x y Hxy. unfold peano_minus_min.
  destruct (excluded_middle_informative (peano_minus_le O x y))
    as [Hle | Hnle]; [reflexivity | contradiction].
Qed.

Lemma peano_minus_min_of_ge : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y,
  peano_minus_le O y x -> @peano_minus_min M O H x y = y.
Proof.
  intros M O H x y Hyx. unfold peano_minus_min.
  destruct (excluded_middle_informative (peano_minus_le O x y))
    as [Hxy | Hnxy]; [|reflexivity].
  exact (@peano_minus_le_antisym M O H x y Hxy Hyx).
Qed.

Lemma peano_minus_max_of_le : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y,
  peano_minus_le O x y -> @peano_minus_max M O H x y = y.
Proof.
  intros M O H x y Hxy. unfold peano_minus_max.
  destruct (excluded_middle_informative (peano_minus_le O x y))
    as [Hle | Hnle]; [reflexivity | contradiction].
Qed.

Lemma peano_minus_max_of_ge : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y,
  peano_minus_le O y x -> @peano_minus_max M O H x y = x.
Proof.
  intros M O H x y Hyx. unfold peano_minus_max.
  destruct (excluded_middle_informative (peano_minus_le O x y))
    as [Hxy | Hnxy]; [|reflexivity].
  symmetry. exact (@peano_minus_le_antisym M O H x y Hxy Hyx).
Qed.

Lemma peano_minus_min_graph_iff : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y z,
  z = @peano_minus_min M O H x y <->
  (peano_minus_le O x y -> z = x) /\
  (peano_minus_le O y x -> z = y).
Proof.
  intros M O H x y z. split.
  - intros ->. split; intro Hle.
    + apply (peano_minus_min_of_le H Hle).
    + apply (peano_minus_min_of_ge H Hle).
  - intros [Hx Hy].
    destruct (@peano_minus_le_total M O H x y) as [Hxy | Hyx].
    + rewrite (Hx Hxy), (peano_minus_min_of_le H Hxy). reflexivity.
    + rewrite (Hy Hyx), (peano_minus_min_of_ge H Hyx). reflexivity.
Qed.

Lemma peano_minus_max_graph_iff : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y z,
  z = @peano_minus_max M O H x y <->
  (peano_minus_le O y x -> z = x) /\
  (peano_minus_le O x y -> z = y).
Proof.
  intros M O H x y z. split.
  - intros ->. split; intro Hle.
    + apply (peano_minus_max_of_ge H Hle).
    + apply (peano_minus_max_of_le H Hle).
  - intros [Hx Hy].
    destruct (@peano_minus_le_total M O H x y) as [Hxy | Hyx].
    + rewrite (Hy Hxy), (peano_minus_max_of_le H Hxy). reflexivity.
    + rewrite (Hx Hyx), (peano_minus_max_of_ge H Hyx). reflexivity.
Qed.

Lemma peano_minus_min_le_left : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y,
  peano_minus_le O (@peano_minus_min M O H x y) x.
Proof.
  intros M O H x y.
  destruct (@peano_minus_le_total M O H x y) as [Hxy | Hyx].
  - rewrite (peano_minus_min_of_le H Hxy). apply peano_minus_le_refl.
  - rewrite (peano_minus_min_of_ge H Hyx). exact Hyx.
Qed.

Lemma peano_minus_min_le_right : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y,
  peano_minus_le O (@peano_minus_min M O H x y) y.
Proof.
  intros M O H x y.
  destruct (@peano_minus_le_total M O H x y) as [Hxy | Hyx].
  - rewrite (peano_minus_min_of_le H Hxy). exact Hxy.
  - rewrite (peano_minus_min_of_ge H Hyx). apply peano_minus_le_refl.
Qed.

Lemma peano_minus_le_max_left : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y,
  peano_minus_le O x (@peano_minus_max M O H x y).
Proof.
  intros M O H x y.
  destruct (@peano_minus_le_total M O H x y) as [Hxy | Hyx].
  - rewrite (peano_minus_max_of_le H Hxy). exact Hxy.
  - rewrite (peano_minus_max_of_ge H Hyx). apply peano_minus_le_refl.
Qed.

Lemma peano_minus_le_max_right : forall M (O : oring_carrier M)
    (H : peano_minus_laws O) x y,
  peano_minus_le O y (@peano_minus_max M O H x y).
Proof.
  intros M O H x y.
  destruct (@peano_minus_le_total M O H x y) as [Hxy | Hyx].
  - rewrite (peano_minus_max_of_le H Hxy). apply peano_minus_le_refl.
  - rewrite (peano_minus_max_of_ge H Hyx). exact Hyx.
Qed.
