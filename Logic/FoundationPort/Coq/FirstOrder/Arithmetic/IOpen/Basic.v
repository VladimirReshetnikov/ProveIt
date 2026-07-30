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

Lemma iopen_eq_mul_div_add_of_pos : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O (oring_zero O) b ->
  exists r, oring_lt O r b /\
    a = oring_add O (oring_mul O b (iopen_div O a b)) r.
Proof.
  intros M O H Hleast a b Hb.
  pose (q := iopen_div O a b).
  pose (r := peano_minus_sub O a (oring_mul O b q)).
  assert (Hq : peano_minus_le O (oring_mul O b q) a).
  { unfold q. apply (iopen_mul_div_le_pos H Hleast a Hb). }
  assert (Heq : a = oring_add O (oring_mul O b q) r).
  { unfold r. apply (peano_minus_sub_spec_of_ge H Hq). }
  exists r. split; [| exact Heq].
  apply NNPP. intro Hnlt.
  pose proof (peano_minus_le_of_not_lt H Hnlt) as Hbr.
  pose proof (peano_minus_add_le_add_left H
    (x := b) (y := r) (oring_mul O b q) Hbr) as Hadd.
  pose proof (iopen_lt_mul_div_succ H Hleast a Hb) as Hupper.
  fold q in Hupper.
  rewrite (@peano_minus_mul_add_distr M O H b q (oring_one O)),
    (@peano_minus_mul_one M O H b) in Hupper.
  rewrite <- Heq in Hadd.
  exact (peano_minus_lt_not_ge H Hupper Hadd).
Qed.

Lemma iopen_div_graph : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b c,
  c = iopen_div O a b <-> iopen_div_spec O a b c.
Proof.
  intros M O H Hleast a b c. split.
  - intros ->. apply (iopen_div_specification H Hleast).
  - intro Hc.
    destruct (iopen_div_exists_unique H Hleast a b) as [u [Hu Huniq]].
    transitivity u.
    + symmetry. now apply Huniq.
    + apply Huniq. apply (iopen_div_specification H Hleast).
Qed.

Lemma iopen_div_eq_of : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b c,
  peano_minus_le O (oring_mul O b c) a ->
  oring_lt O a (oring_mul O b (oring_add O c (oring_one O))) ->
  iopen_div O a b = c.
Proof.
  intros M O H Hleast a b c Hlo Hhi.
  assert (Hb : oring_lt O (oring_zero O) b).
  { destruct (@peano_minus_zero_le M O H b) as [Hb | Hb]; [| exact Hb].
    symmetry in Hb. subst b.
    rewrite (@peano_minus_zero_mul M O H
      (oring_add O c (oring_one O))) in Hhi.
    exfalso. exact (peano_minus_not_lt_zero H Hhi). }
  destruct (iopen_div_exists_unique_pos H Hleast a Hb)
    as [u [Hu Huniq]].
  transitivity u.
  - symmetry. apply Huniq.
    split; [apply (iopen_mul_div_le_pos H Hleast a Hb) |
      apply (iopen_lt_mul_div_succ H Hleast a Hb)].
  - apply Huniq. now split.
Qed.

Lemma iopen_div_mul_add : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b r, oring_lt O r b ->
  iopen_div O (oring_add O (oring_mul O a b) r) b = a.
Proof.
  intros M O H Hleast a b r Hr.
  apply (iopen_div_eq_of H Hleast).
  - pose proof (@peano_minus_zero_le M O H r) as Hzero.
    pose proof (peano_minus_add_le_add_left H
      (x := oring_zero O) (y := r) (oring_mul O a b) Hzero) as Hadd.
    rewrite (@peano_minus_add_zero M O H (oring_mul O a b)) in Hadd.
    rewrite (@peano_minus_mul_comm M O H b a).
    exact Hadd.
  - pose proof (@peano_minus_add_lt_add M O H r b
      (oring_mul O a b) Hr) as Hadd.
    rewrite (@peano_minus_add_comm M O H r (oring_mul O a b)),
      (@peano_minus_add_comm M O H b (oring_mul O a b)) in Hadd.
    rewrite (@peano_minus_mul_add_distr M O H b a (oring_one O)),
      (@peano_minus_mul_one M O H b),
      (@peano_minus_mul_comm M O H b a).
    exact Hadd.
Qed.

Lemma iopen_div_mul_add_left : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b r, oring_lt O r b ->
  iopen_div O (oring_add O (oring_mul O b a) r) b = a.
Proof.
  intros M O H Hleast a b r Hr.
  rewrite (@peano_minus_mul_comm M O H b a).
  now apply (iopen_div_mul_add H Hleast).
Qed.

Lemma iopen_zero_div : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, iopen_div O (oring_zero O) a = oring_zero O.
Proof.
  intros M O H Hleast a.
  destruct (@peano_minus_zero_le M O H a) as [Ha | Ha].
  - symmetry in Ha. subst a. apply (iopen_div_zero H Hleast).
  - apply (iopen_div_eq_of H Hleast).
    + rewrite (@peano_minus_mul_zero M O H a).
      apply peano_minus_le_refl.
    + rewrite (peano_minus_add_zero_left H),
        (@peano_minus_mul_one M O H a).
      exact Ha.
Qed.

Lemma iopen_div_one : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, iopen_div O a (oring_one O) = a.
Proof.
  intros M O H Hleast a.
  apply (iopen_div_eq_of H Hleast).
  - rewrite (@peano_minus_one_mul M O H a).
    apply peano_minus_le_refl.
  - rewrite (@peano_minus_one_mul M O H
      (oring_add O a (oring_one O))).
    apply (peano_minus_lt_add_one H).
Qed.

Lemma iopen_div_eq_zero_of_lt : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O a b ->
  iopen_div O a b = oring_zero O.
Proof.
  intros M O H Hleast a b Hab.
  pose proof (iopen_div_mul_add H Hleast
    (oring_zero O) (b := b) (r := a) Hab) as Hdiv.
  rewrite (@peano_minus_zero_mul M O H b),
    (peano_minus_add_zero_left H) in Hdiv.
  exact Hdiv.
Qed.

Lemma iopen_mul_div_le : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b,
  peano_minus_le O (oring_mul O b (iopen_div O a b)) a.
Proof.
  intros M O H Hleast a b.
  destruct (@peano_minus_zero_le M O H b) as [Hb | Hb].
  - symmetry in Hb. subst b.
    rewrite (@peano_minus_zero_mul M O H (iopen_div O a (oring_zero O))).
    apply (@peano_minus_zero_le M O H).
  - apply (iopen_mul_div_le_pos H Hleast a Hb).
Qed.

Lemma iopen_div_mul_left : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O (oring_zero O) b ->
  iopen_div O (oring_mul O a b) b = a.
Proof.
  intros M O H Hleast a b Hb.
  pose proof (iopen_div_mul_add H Hleast a
    (b := b) (r := oring_zero O) Hb) as Hdiv.
  now rewrite (@peano_minus_add_zero M O H (oring_mul O a b)) in Hdiv.
Qed.

Lemma iopen_div_mul_right : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O (oring_zero O) b ->
  iopen_div O (oring_mul O b a) b = a.
Proof.
  intros M O H Hleast a b Hb.
  rewrite (@peano_minus_mul_comm M O H b a).
  now apply (iopen_div_mul_left H Hleast).
Qed.

Lemma iopen_div_self : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, oring_lt O (oring_zero O) a ->
  iopen_div O a a = oring_one O.
Proof.
  intros M O H Hleast a Ha.
  pose proof (iopen_div_mul_right H Hleast (oring_one O) Ha) as Hdiv.
  now rewrite (@peano_minus_mul_one M O H a) in Hdiv.
Qed.

Definition iopen_rem {M} (O : oring_carrier M) (a b : M) : M :=
  peano_minus_sub O a (oring_mul O b (iopen_div O a b)).

Lemma iopen_rem_graph : forall M (O : oring_carrier M),
  forall a b c,
  c = iopen_rem O a b <->
  c = peano_minus_sub O a (oring_mul O b (iopen_div O a b)).
Proof.
  intros M O a b c. reflexivity.
Qed.

Lemma iopen_div_add_rem : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b,
  oring_add O (oring_mul O b (iopen_div O a b)) (iopen_rem O a b) = a.
Proof.
  intros M O H Hleast a b. unfold iopen_rem.
  apply (peano_minus_add_sub_self_of_le H).
  apply (iopen_mul_div_le H Hleast).
Qed.

Lemma iopen_rem_zero : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, iopen_rem O a (oring_zero O) = a.
Proof.
  intros M O H Hleast a. unfold iopen_rem.
  rewrite (@peano_minus_zero_mul M O H
    (iopen_div O a (oring_zero O))).
  apply (peano_minus_sub_zero H).
Qed.

Lemma iopen_zero_rem : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, iopen_rem O (oring_zero O) a = oring_zero O.
Proof.
  intros M O H Hleast a. unfold iopen_rem.
  rewrite (iopen_zero_div H Hleast a),
    (@peano_minus_mul_zero M O H a).
  apply (peano_minus_sub_self H).
Qed.

Lemma iopen_rem_mul_add_of_lt : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b r, oring_lt O r b ->
  iopen_rem O (oring_add O (oring_mul O a b) r) b = r.
Proof.
  intros M O H Hleast a b r Hr. unfold iopen_rem.
  rewrite (iopen_div_mul_add H Hleast a Hr),
    (@peano_minus_mul_comm M O H b a),
    (@peano_minus_add_comm M O H (oring_mul O a b) r).
  apply (peano_minus_add_sub_self H).
Qed.

Lemma iopen_rem_eq_self_of_lt : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O a b -> iopen_rem O a b = a.
Proof.
  intros M O H Hleast a b Hab.
  pose proof (iopen_rem_mul_add_of_lt H Hleast
    (oring_zero O) (b := b) (r := a) Hab) as Hrem.
  rewrite (@peano_minus_zero_mul M O H b),
    (peano_minus_add_zero_left H) in Hrem.
  exact Hrem.
Qed.

Lemma iopen_rem_lt : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O (oring_zero O) b ->
  oring_lt O (iopen_rem O a b) b.
Proof.
  intros M O H Hleast a b Hb. unfold iopen_rem.
  apply (proj2 (@peano_minus_sub_lt_iff_right M O H a
    (oring_mul O b (iopen_div O a b)) b
    (iopen_mul_div_le H Hleast a b))).
  pose proof (iopen_lt_mul_div_succ H Hleast a Hb) as Hupper.
  rewrite (@peano_minus_mul_add_distr M O H b
      (iopen_div O a b) (oring_one O)),
    (@peano_minus_mul_one M O H b) in Hupper.
  rewrite (@peano_minus_add_comm M O H b
    (oring_mul O b (iopen_div O a b))).
  exact Hupper.
Qed.

Lemma iopen_rem_le : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  peano_minus_le O (iopen_rem O a b) a.
Proof.
  intros M O H a b. unfold iopen_rem.
  apply (peano_minus_sub_le_self H).
Qed.

Lemma iopen_rem_mul_self_left : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b,
  iopen_rem O (oring_mul O a b) b = oring_zero O.
Proof.
  intros M O H Hleast a b.
  destruct (@peano_minus_zero_le M O H b) as [Hb | Hb].
  - symmetry in Hb. subst b.
    rewrite (@peano_minus_mul_zero M O H a).
    apply (iopen_zero_rem H Hleast).
  - pose proof (iopen_rem_mul_add_of_lt H Hleast a
      (b := b) (r := oring_zero O) Hb) as Hrem.
    now rewrite (@peano_minus_add_zero M O H (oring_mul O a b)) in Hrem.
Qed.

Lemma iopen_rem_mul_self_right : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b,
  iopen_rem O (oring_mul O b a) b = oring_zero O.
Proof.
  intros M O H Hleast a b.
  rewrite (@peano_minus_mul_comm M O H b a).
  apply (iopen_rem_mul_self_left H Hleast).
Qed.

Lemma iopen_rem_self : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, iopen_rem O a a = oring_zero O.
Proof.
  intros M O H Hleast a.
  pose proof (iopen_rem_mul_self_right H Hleast
    (oring_one O) a) as Hrem.
  now rewrite (@peano_minus_mul_one M O H a) in Hrem.
Qed.

Lemma iopen_rem_eq_zero_iff_dvd : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b,
  iopen_rem O b a = oring_zero O <-> peano_minus_dvd O a b.
Proof.
  intros M O H Hleast a b. split.
  - intro Hrem. unfold iopen_rem in Hrem.
    exists (iopen_div O b a).
    apply (peano_minus_le_antisym H).
    + apply (proj1 (peano_minus_sub_eq_zero_iff_le H b
        (oring_mul O a (iopen_div O b a)))).
      exact Hrem.
    + apply (iopen_mul_div_le H Hleast).
  - intros [c Hc].
    destruct (@peano_minus_zero_le M O H a) as [Ha | Ha].
    + symmetry in Ha. subst a.
      rewrite (@peano_minus_zero_mul M O H c) in Hc. subst b.
      apply (iopen_zero_rem H Hleast).
    + subst b. unfold iopen_rem.
      rewrite (iopen_div_mul_right H Hleast c Ha).
      apply (peano_minus_sub_self H).
Qed.

Definition iopen_sqrt_spec {M} (O : oring_carrier M)
    (a x : M) : Prop :=
  peano_minus_le O (oring_mul O x x) a /\
  oring_lt O a
    (oring_mul O (oring_add O x (oring_one O))
      (oring_add O x (oring_one O))).

Lemma iopen_sqrt_exists_unique : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, exists! x, iopen_sqrt_spec O a x.
Proof.
  intros M O H Hleast a.
  assert (Hlarge : oring_lt O a
      (oring_mul O (oring_add O a (oring_one O))
        (oring_add O a (oring_one O)))).
  { destruct (@peano_minus_zero_le M O H a) as [Ha | Ha].
    - symmetry in Ha. subst a.
      rewrite (peano_minus_add_zero_left H),
        (@peano_minus_mul_one M O H (oring_one O)).
      apply (@peano_minus_zero_lt_one M O H).
    - apply (@peano_minus_le_lt_trans M O H _ (oring_mul O a a) _).
      + apply (peano_minus_le_mul_self_of_pos_left H a Ha).
      + apply (peano_minus_square_lt_square H).
        apply (peano_minus_lt_add_one H). }
  assert (Hboundary : exists x,
      peano_minus_le O (oring_mul O x x) a /\
      ~ peano_minus_le O
        (oring_mul O (oring_add O x (oring_one O))
          (oring_add O x (oring_one O))) a).
  { apply (arithmetic_boundary_of_least_number H Hleast
      (P := fun x => peano_minus_le O (oring_mul O x x) a)).
    - rewrite (@peano_minus_zero_mul M O H (oring_zero O)).
      apply (@peano_minus_zero_le M O H).
    - exists (oring_add O a (oring_one O)).
      exact (peano_minus_lt_not_ge H Hlarge). }
  destruct Hboundary as [x [Hxlo Hxnext]].
  assert (Hx : iopen_sqrt_spec O a x).
  { split; [exact Hxlo | now apply (peano_minus_lt_of_not_le H)]. }
  exists x. split; [exact Hx |].
  intros y Hy.
  assert (Hnotxy : ~ oring_lt O x y).
  { intro Hxy.
    pose proof (peano_minus_add_one_le_of_lt H Hxy) as Hsucc.
    pose proof (peano_minus_square_le_square H Hsucc) as Hsq.
    pose proof (@peano_minus_le_trans M O H _ _ _ Hsq (proj1 Hy)) as Hle.
    exact (peano_minus_lt_not_ge H (proj2 Hx) Hle). }
  assert (Hnotyx : ~ oring_lt O y x).
  { intro Hyx.
    pose proof (peano_minus_add_one_le_of_lt H Hyx) as Hsucc.
    pose proof (peano_minus_square_le_square H Hsucc) as Hsq.
    pose proof (@peano_minus_le_trans M O H _ _ _ Hsq (proj1 Hx)) as Hle.
    exact (peano_minus_lt_not_ge H (proj2 Hy) Hle). }
  destruct (@peano_minus_lt_trichotomy M O H y x)
    as [Hyx | [Heq | Hxy]]; [contradiction | symmetry; exact Heq | contradiction].
Qed.

Definition iopen_sqrt {M} (O : oring_carrier M) (a : M) : M :=
  epsilon (inhabits (oring_zero O)) (iopen_sqrt_spec O a).

Lemma iopen_sqrt_specification : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, iopen_sqrt_spec O a (iopen_sqrt O a).
Proof.
  intros M O H Hleast a. unfold iopen_sqrt.
  apply epsilon_spec.
  destruct (iopen_sqrt_exists_unique H Hleast a) as [x [Hx _]].
  now exists x.
Qed.

Lemma iopen_sqrt_graph : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a x, x = iopen_sqrt O a <-> iopen_sqrt_spec O a x.
Proof.
  intros M O H Hleast a x. split.
  - intros ->. apply (iopen_sqrt_specification H Hleast).
  - intro Hx.
    destruct (iopen_sqrt_exists_unique H Hleast a) as [y [Hy Huniq]].
    transitivity y.
    + symmetry. now apply Huniq.
    + apply Huniq. apply (iopen_sqrt_specification H Hleast).
Qed.

Lemma iopen_sqrt_eq_of : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a x, iopen_sqrt_spec O a x -> iopen_sqrt O a = x.
Proof.
  intros M O H Hleast a x Hx.
  apply (proj2 (iopen_sqrt_graph H Hleast a x)) in Hx.
  now symmetry.
Qed.

Lemma iopen_sqrt_square : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, iopen_sqrt O (oring_mul O a a) = a.
Proof.
  intros M O H Hleast a. apply (iopen_sqrt_eq_of H Hleast).
  split.
  - apply peano_minus_le_refl.
  - apply (peano_minus_square_lt_square H).
    apply (peano_minus_lt_add_one H).
Qed.

Lemma iopen_sqrt_zero : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  iopen_sqrt O (oring_zero O) = oring_zero O.
Proof.
  intros M O H Hleast.
  pose proof (iopen_sqrt_square H Hleast (oring_zero O)) as Hsqrt.
  now rewrite (@peano_minus_zero_mul M O H (oring_zero O)) in Hsqrt.
Qed.

Lemma iopen_sqrt_one : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  iopen_sqrt O (oring_one O) = oring_one O.
Proof.
  intros M O H Hleast.
  pose proof (iopen_sqrt_square H Hleast (oring_one O)) as Hsqrt.
  now rewrite (@peano_minus_mul_one M O H (oring_one O)) in Hsqrt.
Qed.

Lemma iopen_sqrt_square_le : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a,
  peano_minus_le O
    (oring_mul O (iopen_sqrt O a) (iopen_sqrt O a)) a.
Proof.
  intros M O H Hleast a.
  exact (proj1 (iopen_sqrt_specification H Hleast a)).
Qed.

Lemma iopen_sqrt_lt_square_succ : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a,
  oring_lt O a
    (oring_mul O (oring_add O (iopen_sqrt O a) (oring_one O))
      (oring_add O (iopen_sqrt O a) (oring_one O))).
Proof.
  intros M O H Hleast a.
  exact (proj2 (iopen_sqrt_specification H Hleast a)).
Qed.

Lemma iopen_sqrt_le_self : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, peano_minus_le O (iopen_sqrt O a) a.
Proof.
  intros M O H Hleast a.
  apply NNPP. intro Hnle.
  pose proof (peano_minus_lt_of_not_le H Hnle) as Halt.
  pose proof (peano_minus_square_lt_square H Halt) as Hsq.
  pose proof (@peano_minus_lt_le_trans M O H _ _ _ Hsq
    (iopen_sqrt_square_le H Hleast a)) as Hsq_a.
  exact (peano_minus_lt_not_ge H Hsq_a (peano_minus_le_square H a)).
Qed.

Lemma iopen_sqrt_le_of_le_square : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, peano_minus_le O a (oring_mul O b b) ->
  peano_minus_le O (iopen_sqrt O a) b.
Proof.
  intros M O H Hleast a b Hab.
  apply NNPP. intro Hnle.
  pose proof (peano_minus_lt_of_not_le H Hnle) as Hlt.
  pose proof (peano_minus_square_lt_square H Hlt) as Hsq.
  pose proof (@peano_minus_lt_le_trans M O H _ _ _ Hsq
    (iopen_sqrt_square_le H Hleast a)) as Hsq_a.
  pose proof (@peano_minus_lt_le_trans M O H _ _ _ Hsq_a Hab) as Hbad.
  exact (@peano_minus_lt_irrefl M O H _ Hbad).
Qed.

Lemma iopen_square_lt_of_lt_sqrt : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O a (iopen_sqrt O b) ->
  oring_lt O (oring_mul O a a) b.
Proof.
  intros M O H Hleast a b Hab.
  apply (@peano_minus_lt_le_trans M O H _
    (oring_mul O (iopen_sqrt O b) (iopen_sqrt O b)) _).
  - now apply (peano_minus_square_lt_square H).
  - apply (iopen_sqrt_square_le H Hleast).
Qed.

Lemma iopen_sqrt_lt_self_of_one_lt : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, oring_lt O (oring_one O) a ->
  oring_lt O (iopen_sqrt O a) a.
Proof.
  intros M O H Hleast a Ha.
  destruct (iopen_sqrt_le_self H Hleast a) as [Heq | Hlt]; [| exact Hlt].
  pose proof (iopen_sqrt_square_le H Hleast a) as Hle.
  rewrite Heq in Hle.
  exfalso.
  exact (peano_minus_lt_not_ge H (peano_minus_lt_square_of_one_lt H Ha)
    Hle).
Qed.

Definition iopen_pair {M} (O : oring_carrier M) (a b : M) : M :=
  if excluded_middle_informative (oring_lt O a b)
  then oring_add O (oring_mul O b b) a
  else oring_add O (oring_add O (oring_mul O a a) a) b.

Lemma iopen_pair_graph : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall a b c,
  c = iopen_pair O a b <->
  (oring_lt O a b /\ c = oring_add O (oring_mul O b b) a) \/
  (peano_minus_le O b a /\
    c = oring_add O (oring_add O (oring_mul O a a) a) b).
Proof.
  intros M O H a b c. unfold iopen_pair.
  destruct (excluded_middle_informative (oring_lt O a b)) as [Hab | Hab].
  - split.
    + intro Hc. now left.
    + intros [[_ Hc] | [Hba _]]; [exact Hc |].
      exfalso. exact (peano_minus_lt_not_ge H Hab Hba).
  - pose proof (peano_minus_le_of_not_lt H Hab) as Hba.
    split.
    + intro Hc. now right.
    + intros [[Hlt _] | [_ Hc]]; [contradiction | exact Hc].
Qed.

Definition iopen_unpair {M} (O : oring_carrier M) (a : M) : M * M :=
  let q := iopen_sqrt O a in
  let d := peano_minus_sub O a (oring_mul O q q) in
  if excluded_middle_informative (oring_lt O d q)
  then (d, q)
  else (q, peano_minus_sub O d q).

Lemma iopen_pair_unpair : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a,
  iopen_pair O (fst (iopen_unpair O a)) (snd (iopen_unpair O a)) = a.
Proof.
  intros M O H Hleast a.
  pose (q := iopen_sqrt O a).
  pose (d := peano_minus_sub O a (oring_mul O q q)).
  assert (Hq : peano_minus_le O (oring_mul O q q) a).
  { unfold q. apply (iopen_sqrt_square_le H Hleast). }
  assert (Heq : oring_add O (oring_mul O q q) d = a).
  { unfold d. apply (peano_minus_add_sub_self_of_le H Hq). }
  unfold iopen_unpair. fold q d.
  destruct (excluded_middle_informative (oring_lt O d q)) as [Hdq | Hdq].
  - simpl. unfold iopen_pair.
    destruct (excluded_middle_informative (oring_lt O d q)) as [Hdq' | Hdq'];
      [exact Heq | contradiction].
  - simpl.
    assert (Hqd : peano_minus_le O q d).
    { apply (peano_minus_le_of_not_lt H Hdq). }
    assert (Hdqq : peano_minus_le O d (oring_add O q q)).
    { pose proof (iopen_sqrt_lt_square_succ H Hleast a) as Hupper.
      fold q in Hupper.
      rewrite (peano_minus_square_succ H q) in Hupper.
      pose proof (proj2 (peano_minus_le_iff_lt_add_one H a
        (oring_add O (oring_add O (oring_mul O q q) q) q)) Hupper) as Hale.
      rewrite <- Heq,
        (@peano_minus_add_assoc M O H (oring_mul O q q) q q) in Hale.
      exact (@peano_minus_le_of_add_le_add_left M O H d
        (oring_add O q q) (oring_mul O q q) Hale). }
    assert (Hsub : peano_minus_le O (peano_minus_sub O d q) q).
    { apply (proj2 (peano_minus_sub_le_iff_right H d q q)). exact Hdqq. }
    assert (Hnot : ~ oring_lt O q (peano_minus_sub O d q)).
    { intro Hlt. exact (peano_minus_lt_not_ge H Hlt Hsub). }
    unfold iopen_pair.
    destruct (excluded_middle_informative
      (oring_lt O q (peano_minus_sub O d q))) as [Hlt | _];
      [contradiction |].
    rewrite (@peano_minus_add_assoc M O H (oring_mul O q q) q
      (peano_minus_sub O d q)),
      (peano_minus_add_sub_self_of_le H Hqd).
    exact Heq.
Qed.

Lemma iopen_sqrt_pair_left : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, oring_lt O a b ->
  iopen_sqrt O (iopen_pair O a b) = b.
Proof.
  intros M O H Hleast a b Hab.
  assert (Hpair : iopen_pair O a b =
      oring_add O (oring_mul O b b) a).
  { unfold iopen_pair.
    destruct (excluded_middle_informative (oring_lt O a b));
      [reflexivity | contradiction]. }
  rewrite Hpair. apply (iopen_sqrt_eq_of H Hleast). split.
  - apply (peano_minus_le_add_right H).
  - rewrite (peano_minus_square_succ H b).
    apply (peano_minus_le_lt_add_one H).
    apply (@peano_minus_le_trans M O H _
      (oring_add O (oring_mul O b b) b) _).
    + right. pose proof (@peano_minus_add_lt_add M O H a b
        (oring_mul O b b) Hab) as Hadd.
      rewrite (@peano_minus_add_comm M O H a (oring_mul O b b)),
        (@peano_minus_add_comm M O H b (oring_mul O b b)) in Hadd.
      exact Hadd.
    + apply (peano_minus_le_add_right H).
Qed.

Lemma iopen_sqrt_pair_right : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, peano_minus_le O b a ->
  iopen_sqrt O (iopen_pair O a b) = a.
Proof.
  intros M O H Hleast a b Hba.
  assert (Hpair : iopen_pair O a b =
      oring_add O (oring_add O (oring_mul O a a) a) b).
  { unfold iopen_pair.
    destruct (excluded_middle_informative (oring_lt O a b)) as [Hab | _].
    - exfalso. exact (peano_minus_lt_not_ge H Hab Hba).
    - reflexivity. }
  rewrite Hpair. apply (iopen_sqrt_eq_of H Hleast). split.
  - eapply (peano_minus_le_trans H);
      apply (peano_minus_le_add_right H).
  - rewrite (peano_minus_square_succ H a).
    apply (peano_minus_le_lt_add_one H).
    exact (peano_minus_add_le_add_left H
      (x := b) (y := a)
      (oring_add O (oring_mul O a a) a) Hba).
Qed.

Lemma iopen_unpair_pair : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, iopen_unpair O (iopen_pair O a b) = (a, b).
Proof.
  intros M O H Hleast a b.
  destruct (excluded_middle_informative (oring_lt O a b)) as [Hab | Hab].
  - assert (Hpair : iopen_pair O a b =
        oring_add O (oring_mul O b b) a).
    { unfold iopen_pair.
      destruct (excluded_middle_informative (oring_lt O a b));
        [reflexivity | contradiction]. }
    unfold iopen_unpair.
    rewrite (iopen_sqrt_pair_left H Hleast Hab), Hpair.
    assert (Hsub : peano_minus_sub O
        (oring_add O (oring_mul O b b) a) (oring_mul O b b) = a).
    { rewrite (@peano_minus_add_comm M O H (oring_mul O b b) a).
      apply (peano_minus_add_sub_self H). }
    rewrite Hsub.
    destruct (excluded_middle_informative (oring_lt O a b));
      [reflexivity | contradiction].
  - pose proof (peano_minus_le_of_not_lt H Hab) as Hba.
    assert (Hpair : iopen_pair O a b =
        oring_add O (oring_add O (oring_mul O a a) a) b).
    { unfold iopen_pair.
      destruct (excluded_middle_informative (oring_lt O a b));
        [contradiction | reflexivity]. }
    unfold iopen_unpair.
    rewrite (iopen_sqrt_pair_right H Hleast Hba), Hpair.
    assert (Hsub : peano_minus_sub O
        (oring_add O (oring_add O (oring_mul O a a) a) b)
        (oring_mul O a a) = oring_add O a b).
    { rewrite (@peano_minus_add_assoc M O H (oring_mul O a a) a b),
        (@peano_minus_add_comm M O H (oring_mul O a a)
          (oring_add O a b)).
      apply (peano_minus_add_sub_self H). }
    rewrite Hsub.
    assert (Hnot : ~ oring_lt O (oring_add O a b) a).
    { intro Hlt.
      exact (peano_minus_lt_not_ge H Hlt (peano_minus_le_add_right H a b)). }
    destruct (excluded_middle_informative
      (oring_lt O (oring_add O a b) a)) as [Hlt | _]; [contradiction |].
    rewrite (@peano_minus_add_comm M O H a b),
      (peano_minus_add_sub_self H).
    reflexivity.
Qed.

Definition iopen_pi1 {M} (O : oring_carrier M) (a : M) : M :=
  fst (iopen_unpair O a).

Definition iopen_pi2 {M} (O : oring_carrier M) (a : M) : M :=
  snd (iopen_unpair O a).

Lemma iopen_pair_pi : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, iopen_pair O (iopen_pi1 O a) (iopen_pi2 O a) = a.
Proof.
  intros M O H Hleast a.
  apply (iopen_pair_unpair H Hleast).
Qed.

Lemma iopen_pi1_pair : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, iopen_pi1 O (iopen_pair O a b) = a.
Proof.
  intros M O H Hleast a b. unfold iopen_pi1.
  now rewrite (iopen_unpair_pair H Hleast a b).
Qed.

Lemma iopen_pi2_pair : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, iopen_pi2 O (iopen_pair O a b) = b.
Proof.
  intros M O H Hleast a b. unfold iopen_pi2.
  now rewrite (iopen_unpair_pair H Hleast a b).
Qed.

Lemma iopen_pi1_le_self : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, peano_minus_le O (iopen_pi1 O a) a.
Proof.
  intros M O H Hleast a. unfold iopen_pi1, iopen_unpair.
  destruct (excluded_middle_informative
    (oring_lt O
      (peano_minus_sub O a
        (oring_mul O (iopen_sqrt O a) (iopen_sqrt O a)))
      (iopen_sqrt O a))); simpl.
  - apply (peano_minus_sub_le_self H).
  - apply (iopen_sqrt_le_self H Hleast).
Qed.

Lemma iopen_pi2_le_self : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a, peano_minus_le O (iopen_pi2 O a) a.
Proof.
  intros M O H Hleast a. unfold iopen_pi2, iopen_unpair.
  destruct (excluded_middle_informative
    (oring_lt O
      (peano_minus_sub O a
        (oring_mul O (iopen_sqrt O a) (iopen_sqrt O a)))
      (iopen_sqrt O a))); simpl.
  - apply (iopen_sqrt_le_self H Hleast).
  - eapply (peano_minus_le_trans H).
    + apply (peano_minus_sub_le_self H).
    + apply (peano_minus_sub_le_self H).
Qed.

Lemma iopen_le_pair_left : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, peano_minus_le O a (iopen_pair O a b).
Proof.
  intros M O H Hleast a b.
  pose proof (iopen_pi1_le_self H Hleast (iopen_pair O a b)) as Hle.
  rewrite (iopen_pi1_pair H Hleast a b) in Hle.
  exact Hle.
Qed.

Lemma iopen_le_pair_right : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a b, peano_minus_le O b (iopen_pair O a b).
Proof.
  intros M O H Hleast a b.
  pose proof (iopen_pi2_le_self H Hleast (iopen_pair O a b)) as Hle.
  rewrite (iopen_pi2_pair H Hleast a b) in Hle.
  exact Hle.
Qed.

Lemma iopen_pair_injective : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a1 a2 b1 b2,
  iopen_pair O a1 b1 = iopen_pair O a2 b2 ->
  a1 = a2 /\ b1 = b2.
Proof.
  intros M O H Hleast a1 a2 b1 b2 Heq. split.
  - rewrite <- (iopen_pi1_pair H Hleast a1 b1),
      <- (iopen_pi1_pair H Hleast a2 b2).
    now rewrite Heq.
  - rewrite <- (iopen_pi2_pair H Hleast a1 b1),
      <- (iopen_pi2_pair H Hleast a2 b2).
    now rewrite Heq.
Qed.

Lemma iopen_pair_eq_iff : forall M (O : oring_carrier M),
  peano_minus_laws O -> arithmetic_least_number_principle O ->
  forall a1 a2 b1 b2,
  iopen_pair O a1 b1 = iopen_pair O a2 b2 <->
  a1 = a2 /\ b1 = b2.
Proof.
  intros M O H Hleast a1 a2 b1 b2. split.
  - apply (iopen_pair_injective H Hleast).
  - intros [-> ->]. reflexivity.
Qed.
