(**
  Semantic laws of Peano arithmetic without induction.

  This ports the model-theoretic algebraic core of
  [Foundation/FirstOrder/Arithmetic/PeanoMinus/Basic.lean].  The source first
  presents the laws as a finite first-order theory and then extracts these
  consequences from a model.  Here the semantic package is explicit, making
  every downstream theorem independent of a particular proof calculus.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Model Monotone.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.
From Foundation.FirstOrder.Arithmetic.Q Require Import Basic.

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

Lemma peano_minus_zero_or_succ : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x,
  x = oring_zero O \/
  exists y, x = oring_add O y (oring_one O).
Proof.
  intros M O H x.
  destruct (@peano_minus_zero_le M O H x) as [Hzero | Hpos].
  - left. now symmetry.
  - right. now apply (peano_minus_positive_eq_add_one H).
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

Lemma peano_minus_lt_iff_exists_add_succ : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall x y,
  oring_lt O x y <->
  exists z, oring_add O x (oring_add O z (oring_one O)) = y.
Proof.
  intros M O H x y. split.
  - intro Hxy.
    destruct (@peano_minus_add_eq_of_lt M O H x y Hxy) as [c Hc].
    assert (Hcne : c <> oring_zero O).
    { intro Hzero. subst c.
      rewrite (@peano_minus_add_zero M O H x) in Hc. subst y.
      exact (@peano_minus_lt_irrefl M O H x Hxy). }
    destruct (@peano_minus_zero_le M O H c) as [Hzero | Hpos].
    + exfalso. exact (Hcne (eq_sym Hzero)).
    + destruct (peano_minus_positive_eq_add_one H Hpos) as [z Hz].
      exists z. now rewrite <- Hz.
  - intros [z Hz].
    pose proof (peano_minus_le_lt_add_one H
      (@peano_minus_zero_le M O H z)) as Hpos.
    pose proof (@peano_minus_add_lt_add M O H
      (oring_zero O) (oring_add O z (oring_one O)) x Hpos) as Hlt.
    rewrite (peano_minus_add_zero_left H),
      (@peano_minus_add_comm M O H (oring_add O z (oring_one O)) x),
      Hz in Hlt.
    exact Hlt.
Qed.

Lemma peano_minus_add_le_add_right : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y z,
  peano_minus_le O x y ->
  peano_minus_le O (oring_add O x z) (oring_add O y z).
Proof.
  intros M O H x y z [-> | Hxy].
  - apply peano_minus_le_refl.
  - right. now apply (@peano_minus_add_lt_add M O H).
Qed.

Lemma peano_minus_add_le_add_left : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y z,
  peano_minus_le O x y ->
  peano_minus_le O (oring_add O z x) (oring_add O z y).
Proof.
  intros M O H x y z Hxy.
  rewrite (@peano_minus_add_comm M O H z x),
    (@peano_minus_add_comm M O H z y).
  now apply (peano_minus_add_le_add_right H).
Qed.

Lemma peano_minus_add_le_add : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x x' y y',
  peano_minus_le O x x' -> peano_minus_le O y y' ->
  peano_minus_le O (oring_add O x y) (oring_add O x' y').
Proof.
  intros M O H x x' y y' Hx Hy.
  eapply (peano_minus_le_trans H).
  - exact (peano_minus_add_le_add_right H (x := x) (y := x') y Hx).
  - exact (peano_minus_add_le_add_left H (x := y) (y := y') x' Hy).
Qed.

Lemma peano_minus_mul_le_mul_right : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y z,
  peano_minus_le O x y ->
  peano_minus_le O (oring_mul O x z) (oring_mul O y z).
Proof.
  intros M O H x y z [-> | Hxy].
  - apply peano_minus_le_refl.
  - destruct (@peano_minus_zero_le M O H z) as [Hz | Hz].
    + left. rewrite <- Hz.
      now rewrite !(@peano_minus_mul_zero M O H).
    + right. now apply (@peano_minus_mul_lt_mul M O H).
Qed.

Lemma peano_minus_mul_le_mul_left : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x y z,
  peano_minus_le O x y ->
  peano_minus_le O (oring_mul O z x) (oring_mul O z y).
Proof.
  intros M O H x y z Hxy.
  rewrite (@peano_minus_mul_comm M O H z x),
    (@peano_minus_mul_comm M O H z y).
  now apply (peano_minus_mul_le_mul_right H).
Qed.

Lemma peano_minus_mul_le_mul : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x x' y y',
  peano_minus_le O x x' -> peano_minus_le O y y' ->
  peano_minus_le O (oring_mul O x y) (oring_mul O x' y').
Proof.
  intros M O H x x' y y' Hx Hy.
  eapply (peano_minus_le_trans H).
  - exact (peano_minus_mul_le_mul_right H (x := x) (y := x') y Hx).
  - exact (peano_minus_mul_le_mul_left H (x := y) (y := y') x' Hy).
Qed.

Definition peano_minus_structure_monotone : forall M
    (O : oring_carrier M)
    (Str : first_order_structure oring_language M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  first_order_structure_monotone (peano_minus_le O) Str.
Proof.
  intros M O Str Horing Hpa. constructor.
  intros k f v w Hvw. destruct f.
  - change (peano_minus_le O
      (semiterm_operator_val Str v
        (@semiterm_operator_fn oring_language 0 ORing_zero))
      (semiterm_operator_val Str w
        (@semiterm_operator_fn oring_language 0 ORing_zero))).
    rewrite (fin_zero_eta v), (fin_zero_eta w).
    pose proof (structure_zero_operator
      (structure_oring_zero Horing)) as Hzero.
    change (semiterm_operator_val Str fin_zero
      (@semiterm_operator_fn oring_language 0 ORing_zero) =
      oring_zero O) in Hzero.
    rewrite Hzero.
    apply peano_minus_le_refl.
  - change (peano_minus_le O
      (semiterm_operator_val Str v
        (@semiterm_operator_fn oring_language 0 ORing_one))
      (semiterm_operator_val Str w
        (@semiterm_operator_fn oring_language 0 ORing_one))).
    rewrite (fin_zero_eta v), (fin_zero_eta w).
    pose proof (structure_one_operator
      (structure_oring_one Horing)) as Hone.
    change (semiterm_operator_val Str fin_zero
      (@semiterm_operator_fn oring_language 0 ORing_one) =
      oring_one O) in Hone.
    rewrite Hone.
    apply peano_minus_le_refl.
  - change (peano_minus_le O
      (semiterm_operator_val Str v
        (@semiterm_operator_fn oring_language 2 ORing_add))
      (semiterm_operator_val Str w
        (@semiterm_operator_fn oring_language 2 ORing_add))).
    rewrite (fin_two_eta v), (fin_two_eta w).
    pose proof (structure_add_operator (structure_oring_add Horing)
      (v Fin.F1) (v (Fin.FS Fin.F1))) as Hv.
    pose proof (structure_add_operator (structure_oring_add Horing)
      (w Fin.F1) (w (Fin.FS Fin.F1))) as Hw.
    change (semiterm_operator_val Str
      (fin_two (v Fin.F1) (v (Fin.FS Fin.F1)))
      (@semiterm_operator_fn oring_language 2 ORing_add) =
      oring_add O (v Fin.F1) (v (Fin.FS Fin.F1))) in Hv.
    change (semiterm_operator_val Str
      (fin_two (w Fin.F1) (w (Fin.FS Fin.F1)))
      (@semiterm_operator_fn oring_language 2 ORing_add) =
      oring_add O (w Fin.F1) (w (Fin.FS Fin.F1))) in Hw.
    rewrite Hv, Hw.
    apply (peano_minus_add_le_add Hpa); apply Hvw.
  - change (peano_minus_le O
      (semiterm_operator_val Str v
        (@semiterm_operator_fn oring_language 2 ORing_mul))
      (semiterm_operator_val Str w
        (@semiterm_operator_fn oring_language 2 ORing_mul))).
    rewrite (fin_two_eta v), (fin_two_eta w).
    pose proof (structure_mul_operator (structure_oring_mul Horing)
      (v Fin.F1) (v (Fin.FS Fin.F1))) as Hv.
    pose proof (structure_mul_operator (structure_oring_mul Horing)
      (w Fin.F1) (w (Fin.FS Fin.F1))) as Hw.
    change (semiterm_operator_val Str
      (fin_two (v Fin.F1) (v (Fin.FS Fin.F1)))
      (@semiterm_operator_fn oring_language 2 ORing_mul) =
      oring_mul O (v Fin.F1) (v (Fin.FS Fin.F1))) in Hv.
    change (semiterm_operator_val Str
      (fin_two (w Fin.F1) (w (Fin.FS Fin.F1)))
      (@semiterm_operator_fn oring_language 2 ORing_mul) =
      oring_mul O (w Fin.F1) (w (Fin.FS Fin.F1))) in Hw.
    rewrite Hv, Hw.
    apply (peano_minus_mul_le_mul Hpa); apply Hvw.
Defined.

Lemma peano_minus_not_lt_zero : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall x,
  ~ oring_lt O x (oring_zero O).
Proof.
  intros M O H x Hx.
  destruct (@peano_minus_zero_le M O H x) as [Hz | Hz].
  - subst x. exact (@peano_minus_lt_irrefl M O H _ Hx).
  - exact (@peano_minus_lt_irrefl M O H _
      (@peano_minus_lt_trans M O H _ _ _ Hz Hx)).
Qed.

Lemma peano_minus_numeral_succ : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall n,
  oring_numeral O (S n) =
  oring_add O (oring_numeral O n) (oring_one O).
Proof.
  intros M O H [|n].
  - simpl. symmetry. apply (peano_minus_add_zero_left H).
  - apply oring_numeral_succ_succ.
Qed.

Lemma peano_minus_numeral_add : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall n m,
  oring_add O (oring_numeral O n) (oring_numeral O m) =
  oring_numeral O (n + m).
Proof.
  intros M O H n m. induction m as [|m IH].
  - cbn. rewrite Nat.add_0_r. apply (@peano_minus_add_zero M O H).
  - rewrite (peano_minus_numeral_succ H m).
    replace (n + S m) with (S (n + m)) by lia.
    rewrite (peano_minus_numeral_succ H (n + m)).
    rewrite <- (@peano_minus_add_assoc M O H).
    now rewrite IH.
Qed.

Lemma peano_minus_numeral_mul : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall n m,
  oring_mul O (oring_numeral O n) (oring_numeral O m) =
  oring_numeral O (n * m).
Proof.
  intros M O H n m. induction m as [|m IH].
  - cbn. rewrite Nat.mul_0_r. apply (@peano_minus_mul_zero M O H).
  - rewrite (peano_minus_numeral_succ H m).
    rewrite (@peano_minus_mul_add_distr M O H),
      (@peano_minus_mul_one M O H), IH,
      (peano_minus_numeral_add H).
    f_equal. lia.
Qed.

Lemma peano_minus_numeral_lt : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall m n,
  m < n -> oring_lt O (oring_numeral O m) (oring_numeral O n).
Proof.
  intros M O H m n. revert m.
  induction n as [|n IH]; intros m Hmn; [lia|].
  rewrite (peano_minus_numeral_succ H).
  destruct (Nat.eq_dec m n) as [-> | Hne].
  - apply (peano_minus_lt_add_one H).
  - eapply (@peano_minus_lt_trans M O H).
    + apply IH. lia.
    + apply (peano_minus_lt_add_one H).
Qed.

Lemma peano_minus_numeral_ne : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall n m,
  n <> m -> oring_numeral O n <> oring_numeral O m.
Proof.
  intros M O H n m Hne Heq.
  destruct (Nat.lt_total n m) as [Hnm | [Hnm | Hmn]].
  - pose proof (peano_minus_numeral_lt H Hnm) as Hlt.
    rewrite Heq in Hlt. exact (@peano_minus_lt_irrefl M O H _ Hlt).
  - contradiction.
  - pose proof (peano_minus_numeral_lt H Hmn) as Hlt.
    rewrite <- Heq in Hlt. exact (@peano_minus_lt_irrefl M O H _ Hlt).
Qed.

Lemma peano_minus_eq_numeral_of_lt_numeral : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall n x,
  oring_lt O x (oring_numeral O n) ->
  exists m, m < n /\ x = oring_numeral O m.
Proof.
  intros M O H n. induction n as [|n IH]; intros x Hx.
  - exfalso. apply (peano_minus_not_lt_zero H (x := x)). exact Hx.
  - rewrite (peano_minus_numeral_succ H) in Hx.
    destruct (proj2 (peano_minus_le_iff_lt_add_one H x
      (oring_numeral O n)) Hx) as [Heq | Hlt].
    + exists n. split; [lia|exact Heq].
    + destruct (IH x Hlt) as [m [Hmn Hm]].
      exists m. split; [lia|exact Hm].
Qed.

Lemma peano_minus_lt_numeral_iff : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall n x,
  oring_lt O x (oring_numeral O n) <->
  exists m, m < n /\ x = oring_numeral O m.
Proof.
  intros M O H n x. split.
  - apply (peano_minus_eq_numeral_of_lt_numeral H).
  - intros [m [Hmn ->]]. now apply (peano_minus_numeral_lt H).
Qed.

Lemma peano_minus_le_numeral_iff : forall M (O : oring_carrier M),
  peano_minus_laws O -> forall n x,
  peano_minus_le O x (oring_numeral O n) <->
  exists m, m <= n /\ x = oring_numeral O m.
Proof.
  intros M O H n x. split.
  - intros [Heq | Hlt].
    + exists n. split; [lia|exact Heq].
    + destruct (peano_minus_eq_numeral_of_lt_numeral H Hlt)
        as [m [Hmn Hm]].
      exists m. split; [lia|exact Hm].
  - intros [m [Hmn ->]].
    destruct (Nat.eq_dec m n) as [-> | Hne].
    + apply peano_minus_le_refl.
    + right. apply (peano_minus_numeral_lt H). lia.
Qed.

Definition peano_minus_r0_laws : forall M (O : oring_carrier M),
  peano_minus_laws O -> r0_laws O.
Proof.
  intros M O H. constructor.
  - apply (peano_minus_numeral_add H).
  - apply (peano_minus_numeral_mul H).
  - apply (peano_minus_numeral_ne H).
  - apply (peano_minus_lt_numeral_iff H).
Defined.

Definition peano_minus_robinson_q_laws : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> robinson_q_laws O.
Proof.
  intros M O H. constructor.
  - intros a Heq.
    pose proof (peano_minus_lt_add_one H a) as Hlt.
    rewrite Heq in Hlt. exact (peano_minus_not_lt_zero H Hlt).
  - intros a b Hab.
    exact (@peano_minus_add_right_cancel M O H a b (oring_one O) Hab).
  - apply (peano_minus_zero_or_succ H).
  - apply (@peano_minus_add_zero M O H).
  - intros a b. symmetry. apply (@peano_minus_add_assoc M O H).
  - apply (@peano_minus_mul_zero M O H).
  - intros a b. rewrite (@peano_minus_mul_add_distr M O H),
      (@peano_minus_mul_one M O H). reflexivity.
  - apply (peano_minus_lt_iff_exists_add_succ H).
Defined.

Definition peano_minus_ball_lt_succ {X n}
    (t : semiterm oring_language X n)
    (p : semiformula oring_language X (S n)) :
    semiformula oring_language X n :=
  semiformula_ball_lt_succ
    (semiformula_lt_operator_of_language
      (language_oring_lt oring_language_structure))
    (semiterm_one_operator_of_language
      (language_oring_one oring_language_structure))
    (semiterm_add_operator_of_language
      (language_oring_add oring_language_structure)) t p.

Definition peano_minus_bex_lt_succ {X n}
    (t : semiterm oring_language X n)
    (p : semiformula oring_language X (S n)) :
    semiformula oring_language X n :=
  semiformula_bex_lt_succ
    (semiformula_lt_operator_of_language
      (language_oring_lt oring_language_structure))
    (semiterm_one_operator_of_language
      (language_oring_one oring_language_structure))
    (semiterm_add_operator_of_language
      (language_oring_add oring_language_structure)) t p.

Lemma peano_minus_eval_ball_lt_succ : forall M X n
    (Str : first_order_structure oring_language M)
    (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  forall (b : Fin.t n -> M) (f : X -> M)
    (t : semiterm oring_language X n)
    (p : semiformula oring_language X (S n)),
  semiformula_eval Str b f (peano_minus_ball_lt_succ t p) <->
  forall x, peano_minus_le O x (semiterm_val Str b f t) ->
    semiformula_eval Str (fin_env_cons x b) f p.
Proof.
  intros M X n Str O Horing Hpa b f t p.
  unfold peano_minus_ball_lt_succ.
  rewrite (@semiformula_eval_ball_lt_succ oring_language M X n
    Str b f
    (semiformula_lt_operator_of_language
      (language_oring_lt oring_language_structure))
    (semiterm_one_operator_of_language
      (language_oring_one oring_language_structure))
    (semiterm_add_operator_of_language
      (language_oring_add oring_language_structure))
    (oring_lt O) (oring_one O) (oring_add O) t p
    (structure_oring_lt Horing) (structure_oring_one Horing)
    (structure_oring_add Horing)).
  split; intros Hall x Hx; apply Hall.
  - now apply (proj1 (peano_minus_le_iff_lt_add_one Hpa x
      (semiterm_val Str b f t))).
  - now apply (proj2 (peano_minus_le_iff_lt_add_one Hpa x
      (semiterm_val Str b f t))).
Qed.

Lemma peano_minus_eval_bex_lt_succ : forall M X n
    (Str : first_order_structure oring_language M)
    (O : oring_carrier M),
  structure_interprets_oring Str oring_language_structure O ->
  peano_minus_laws O ->
  forall (b : Fin.t n -> M) (f : X -> M)
    (t : semiterm oring_language X n)
    (p : semiformula oring_language X (S n)),
  semiformula_eval Str b f (peano_minus_bex_lt_succ t p) <->
  exists x, peano_minus_le O x (semiterm_val Str b f t) /\
    semiformula_eval Str (fin_env_cons x b) f p.
Proof.
  intros M X n Str O Horing Hpa b f t p.
  unfold peano_minus_bex_lt_succ.
  rewrite (@semiformula_eval_bex_lt_succ oring_language M X n
    Str b f
    (semiformula_lt_operator_of_language
      (language_oring_lt oring_language_structure))
    (semiterm_one_operator_of_language
      (language_oring_one oring_language_structure))
    (semiterm_add_operator_of_language
      (language_oring_add oring_language_structure))
    (oring_lt O) (oring_one O) (oring_add O) t p
    (structure_oring_lt Horing) (structure_oring_one Horing)
    (structure_oring_add Horing)).
  split.
  - intros [x [Hx Hp]]. exists x. split; [|exact Hp].
    now apply (proj2 (peano_minus_le_iff_lt_add_one Hpa x
      (semiterm_val Str b f t))).
  - intros [x [Hx Hp]]. exists x. split; [|exact Hp].
    now apply (proj1 (peano_minus_le_iff_lt_add_one Hpa x
      (semiterm_val Str b f t))).
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
