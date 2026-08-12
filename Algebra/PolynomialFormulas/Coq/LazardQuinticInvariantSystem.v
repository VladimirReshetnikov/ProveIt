From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticProjection LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelations
  LazardQuinticRootInvariantRelationFifthData
  LazardQuinticRootInvariantRelationFifth.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The literal four-by-four linear system in Lazard's Figure 3.

    Once [i4] is fixed, the four equations for [i4^2], ..., [i4^5]
    are affine linear in [(i5,i6,i7,i8)].  This file records their exact
    coefficient matrix and proves, without accepting any new invariant
    certificate, that a nonzero determinant makes the invariant tuple
    unique. *)
Module PolynomialFormulasLazardQuinticInvariantSystem.

Import GRing.Theory.
Module P := PolynomialFormulasLazardQuinticProjection.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module IR := PolynomialFormulasLazardQuinticRootInvariantRelations.
Module D := PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.
Module F5 := PolynomialFormulasLazardQuinticRootInvariantRelationFifth.
Local Open Scope ring_scope.

Section InvariantSystem.

Variable F : fieldType.

(** Rows are the square, cube, fourth, and fifth equations; columns are
    [i5], [i6], [i7], and [i8], in that order. *)
Definition lazard_invariant_system_matrix
    (c : RP.LazardDepressedRootCoefficients F) : 'M[F]_4 :=
  \matrix_(row < 4, column < 4)
    (nth [::]
      [::
        [:: 4%:R * RP.lazard_root_q c;
            - 2%:R * RP.lazard_root_p c;
            0;
            5%:R];
        [:: (3%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c -
                45%:R * RP.lazard_root_p c * RP.lazard_root_s c -
                6%:R * RP.lazard_root_q c * RP.lazard_root_r c) / 2%:R;
            (- 3%:R * RP.lazard_root_p c ^+ 3 +
                28%:R * RP.lazard_root_p c * RP.lazard_root_r c -
                12%:R * RP.lazard_root_q c ^+ 2) / 2%:R;
            (- RP.lazard_root_p c * RP.lazard_root_q c -
                50%:R * RP.lazard_root_s c) / 2%:R;
            (3%:R * RP.lazard_root_p c ^+ 2 -
                20%:R * RP.lazard_root_r c) / 2%:R];
        [:: - 9%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_s c +
                17%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
                  RP.lazard_root_r c -
                8%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 +
                140%:R * RP.lazard_root_p c * RP.lazard_root_r c *
                  RP.lazard_root_s c +
                155%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_s c -
                68%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 2;
            - 4%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c +
                4%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 -
                105%:R * RP.lazard_root_p c * RP.lazard_root_q c *
                  RP.lazard_root_s c -
                16%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 +
                29%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c +
                125%:R * RP.lazard_root_s c ^+ 2;
            15%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c -
                8%:R * RP.lazard_root_p c * RP.lazard_root_q c *
                  RP.lazard_root_r c +
                3%:R * RP.lazard_root_q c ^+ 3 +
                100%:R * RP.lazard_root_r c * RP.lazard_root_s c;
            19%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c -
                9%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 +
                225%:R * RP.lazard_root_q c * RP.lazard_root_s c -
                60%:R * RP.lazard_root_r c ^+ 2];
        [:: D.lazard_fifth_printed_i5
              (RP.lazard_root_p c) (RP.lazard_root_q c)
              (RP.lazard_root_r c) (RP.lazard_root_s c) / 2%:R;
            D.lazard_fifth_printed_i6
              (RP.lazard_root_p c) (RP.lazard_root_q c)
              (RP.lazard_root_r c) (RP.lazard_root_s c) / 2%:R;
            D.lazard_fifth_printed_i7
              (RP.lazard_root_p c) (RP.lazard_root_q c)
              (RP.lazard_root_r c) (RP.lazard_root_s c) / 2%:R;
            D.lazard_fifth_printed_i8
              (RP.lazard_root_p c) (RP.lazard_root_q c)
              (RP.lazard_root_r c) (RP.lazard_root_s c) / 2%:R]] row)`_column.

Definition lazard_invariant_tail
    (i : RP.LazardRootInvariants F) : 'M[F]_(4, 1) :=
  \matrix_(row < 4, column < 1)
    nth 0 [:: RP.lazard_root_i5 i; RP.lazard_root_i6 i;
              RP.lazard_root_i7 i; RP.lazard_root_i8 i] row.

Definition lazard_invariant_i4_base
    (i : RP.LazardRootInvariants F) : RP.LazardRootInvariants F :=
  {| RP.lazard_root_i4 := RP.lazard_root_i4 i;
     RP.lazard_root_i5 := 0;
     RP.lazard_root_i6 := 0;
     RP.lazard_root_i7 := 0;
     RP.lazard_root_i8 := 0 |}.

Definition lazard_invariant_system_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : 'M[F]_(4, 1) :=
  \matrix_(row < 4, column < 1)
    nth 0 [:: IR.lazard_i4_square_rhs c i;
              IR.lazard_i4_cube_rhs c i;
              IR.lazard_i4_fourth_rhs c i;
              F5.lazard_i4_fifth_rhs c i] row.

(** A definitional bridge from the public fifth-equation numerator to the
    coefficient-sharded form used by its kernel certificate. *)
Lemma lazard_i4_fifth_numerator_dataE
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  F5.lazard_i4_fifth_numerator c i =
    D.lazard_fifth_printed_numerator
      (RP.lazard_root_p c) (RP.lazard_root_q c)
      (RP.lazard_root_r c) (RP.lazard_root_s c)
      (RP.lazard_root_i4 i) (RP.lazard_root_i5 i)
      (RP.lazard_root_i6 i) (RP.lazard_root_i7 i)
      (RP.lazard_root_i8 i).
Proof. reflexivity. Qed.

Add Ring lazard_invariant_system_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_invariant_system_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_linear_rhs_affine_mul
    (a8 a7 a6 a5 a4 a0 i4 i5 i6 i7 i8 t : F) :
  (a8 * i8 + a7 * i7 + a6 * i6 + a5 * i5 + a4 * i4 + a0) * t =
    (a4 * i4 + a0) * t +
      ((a5 * t) * i5 + (a6 * t) * i6 +
       (a7 * t) * i7 + (a8 * t) * i8).
Proof.
lazard_numerator_prepare.
match goal with
| |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
end.
ring.
Qed.

Lemma lazard_fifth_printed_rhs_affine_mul
    (p q r s i4 i5 i6 i7 i8 t : F) :
  D.lazard_fifth_printed_numerator p q r s i4 i5 i6 i7 i8 * t =
    D.lazard_fifth_printed_numerator p q r s i4 0 0 0 0 * t +
      ((D.lazard_fifth_printed_i5 p q r s * t) * i5 +
       (D.lazard_fifth_printed_i6 p q r s * t) * i6 +
       (D.lazard_fifth_printed_i7 p q r s * t) * i7 +
       (D.lazard_fifth_printed_i8 p q r s * t) * i8).
Proof.
rewrite /D.lazard_fifth_printed_numerator !mulr0 !add0r.
exact: lazard_linear_rhs_affine_mul.
Qed.

Lemma lazard_fifth_printed_rhs_affine
    (p q r s i4 i5 i6 i7 i8 : F) :
  D.lazard_fifth_printed_numerator p q r s i4 i5 i6 i7 i8 / 2%:R =
    D.lazard_fifth_printed_numerator p q r s i4 0 0 0 0 / 2%:R +
      (D.lazard_fifth_printed_i5 p q r s / 2%:R * i5 +
       D.lazard_fifth_printed_i6 p q r s / 2%:R * i6 +
       D.lazard_fifth_printed_i7 p q r s / 2%:R * i7 +
       D.lazard_fifth_printed_i8 p q r s / 2%:R * i8).
Proof.
change
  (D.lazard_fifth_printed_numerator p q r s i4 i5 i6 i7 i8 *
      (2%:R : F)^-1 =
    D.lazard_fifth_printed_numerator p q r s i4 0 0 0 0 *
      (2%:R : F)^-1 +
      ((D.lazard_fifth_printed_i5 p q r s * (2%:R : F)^-1) * i5 +
       (D.lazard_fifth_printed_i6 p q r s * (2%:R : F)^-1) * i6 +
       (D.lazard_fifth_printed_i7 p q r s * (2%:R : F)^-1) * i7 +
       (D.lazard_fifth_printed_i8 p q r s * (2%:R : F)^-1) * i8)).
exact: lazard_fifth_printed_rhs_affine_mul.
Qed.

(** Each row is sealed independently so the public matrix equality does not
    retain one monolithic normalization proof. *)
Lemma lazard_invariant_system_rhs_affine_row0
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  lazard_invariant_system_rhs c i P.p0 ord0 =
    (lazard_invariant_system_rhs c (lazard_invariant_i4_base i) +
      lazard_invariant_system_matrix c *m lazard_invariant_tail i)
      P.p0 ord0.
Proof.
rewrite /lazard_invariant_system_rhs /lazard_invariant_i4_base
  /lazard_invariant_system_matrix /lazard_invariant_tail
  /IR.lazard_i4_square_rhs !mxE P.lazard_sum_ord4
  /P.p0 /P.p1 /P.p2 /P.p3 !mxE /=.
finish_lazard_invariant_system_ring.
Qed.

Lemma lazard_invariant_system_rhs_affine_row1
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  lazard_invariant_system_rhs c i P.p1 ord0 =
    (lazard_invariant_system_rhs c (lazard_invariant_i4_base i) +
      lazard_invariant_system_matrix c *m lazard_invariant_tail i)
      P.p1 ord0.
Proof.
rewrite /lazard_invariant_system_rhs /lazard_invariant_i4_base
  /lazard_invariant_system_matrix /lazard_invariant_tail
  /IR.lazard_i4_cube_rhs /IR.lazard_i4_cube_numerator
  !mxE P.lazard_sum_ord4 /P.p0 /P.p1 /P.p2 /P.p3 !mxE /=.
finish_lazard_invariant_system_ring.
Qed.

Lemma lazard_invariant_system_rhs_affine_row2
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  lazard_invariant_system_rhs c i P.p2 ord0 =
    (lazard_invariant_system_rhs c (lazard_invariant_i4_base i) +
      lazard_invariant_system_matrix c *m lazard_invariant_tail i)
      P.p2 ord0.
Proof.
rewrite /lazard_invariant_system_rhs /lazard_invariant_i4_base
  /lazard_invariant_system_matrix /lazard_invariant_tail
  /IR.lazard_i4_fourth_rhs !mxE P.lazard_sum_ord4
  /P.p0 /P.p1 /P.p2 /P.p3 !mxE /=.
finish_lazard_invariant_system_ring.
Qed.

Lemma lazard_invariant_system_rhs_affine_row3
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  lazard_invariant_system_rhs c i P.p3 ord0 =
    (lazard_invariant_system_rhs c (lazard_invariant_i4_base i) +
      lazard_invariant_system_matrix c *m lazard_invariant_tail i)
      P.p3 ord0.
Proof.
rewrite /lazard_invariant_system_rhs /lazard_invariant_i4_base
  /lazard_invariant_system_matrix /lazard_invariant_tail
  /F5.lazard_i4_fifth_rhs !lazard_i4_fifth_numerator_dataE
  !mxE P.lazard_sum_ord4 /P.p0 /P.p1 /P.p2 /P.p3 !mxE /=.
exact: lazard_fifth_printed_rhs_affine.
Qed.

Lemma lazard_matrix4x1_eq (A B : 'M[F]_(4, 1))
    (h0 : A P.p0 ord0 = B P.p0 ord0)
    (h1 : A P.p1 ord0 = B P.p1 ord0)
    (h2 : A P.p2 ord0 = B P.p2 ord0)
    (h3 : A P.p3 ord0 = B P.p3 ord0) : A = B.
Proof.
apply/matrixP=> row column; rewrite ord1.
case: row=> [[|[|[|[|row]]]] hrow] //=.
- have -> : (Ordinal hrow : 'I_4) = P.p0 :=
    @val_inj _ _ _ (Ordinal hrow) P.p0 (@Logic.eq_refl nat 0).
  exact: h0.
- have -> : (Ordinal hrow : 'I_4) = P.p1 :=
    @val_inj _ _ _ (Ordinal hrow) P.p1 (@Logic.eq_refl nat 1).
  exact: h1.
- have -> : (Ordinal hrow : 'I_4) = P.p2 :=
    @val_inj _ _ _ (Ordinal hrow) P.p2 (@Logic.eq_refl nat 2).
  exact: h2.
- have -> : (Ordinal hrow : 'I_4) = P.p3 :=
    @val_inj _ _ _ (Ordinal hrow) P.p3 (@Logic.eq_refl nat 3).
  exact: h3.
Qed.

(** The displayed matrix is exactly the homogeneous tail of the four
    printed right sides, not merely a matrix later asserted to be related
    to those equations. *)
Theorem lazard_invariant_system_rhs_affine c i :
  lazard_invariant_system_rhs c i =
    lazard_invariant_system_rhs c (lazard_invariant_i4_base i) +
      lazard_invariant_system_matrix c *m lazard_invariant_tail i.
Proof.
apply: lazard_matrix4x1_eq.
- exact: lazard_invariant_system_rhs_affine_row0.
- exact: lazard_invariant_system_rhs_affine_row1.
- exact: lazard_invariant_system_rhs_affine_row2.
- exact: lazard_invariant_system_rhs_affine_row3.
Qed.

Lemma lazard_invariant_i4_base_eq
    (i j : RP.LazardRootInvariants F)
    (hi4 : RP.lazard_root_i4 i = RP.lazard_root_i4 j) :
  lazard_invariant_i4_base i = lazard_invariant_i4_base j.
Proof.
case: i hi4=> i4 i5 i6 i7 i8 /=.
case: j=> j4 j5 j6 j7 j8 /=.
by move=> ->.
Qed.

Lemma lazard_root_invariants_ext
    (i j : RP.LazardRootInvariants F)
    (h4 : RP.lazard_root_i4 i = RP.lazard_root_i4 j)
    (h5 : RP.lazard_root_i5 i = RP.lazard_root_i5 j)
    (h6 : RP.lazard_root_i6 i = RP.lazard_root_i6 j)
    (h7 : RP.lazard_root_i7 i = RP.lazard_root_i7 j)
    (h8 : RP.lazard_root_i8 i = RP.lazard_root_i8 j) : i = j.
Proof.
case: i h4 h5 h6 h7 h8=> i4 i5 i6 i7 i8 /=.
case: j=> j4 j5 j6 j7 j8 /=.
by move=> -> -> -> -> ->.
Qed.

Lemma lazard_invariant_system_rhs_eq_of_relations
    (c : RP.LazardDepressedRootCoefficients F)
    (i j : RP.LazardRootInvariants F)
    (hi : F5.lazard_invariant_relations c i)
    (hj : F5.lazard_invariant_relations c j)
    (hi4 : RP.lazard_root_i4 i = RP.lazard_root_i4 j) :
  lazard_invariant_system_rhs c i = lazard_invariant_system_rhs c j.
Proof.
case: hi=> hi2 hi3 hi4pow hi5.
case: hj=> hj2 hj3 hj4pow hj5.
apply/matrixP=> row column; rewrite ord1.
case: row=> [[|[|[|[|row]]]] hrow] //=;
  rewrite /lazard_invariant_system_rhs !mxE /=.
- by rewrite -hi2 -hj2 hi4.
- by rewrite -hi3 -hj3 hi4.
- by rewrite -hi4pow -hj4pow hi4.
- by rewrite -hi5 -hj5 hi4.
Qed.

Theorem lazard_invariant_system_matrix_mul_tail_eq
    (c : RP.LazardDepressedRootCoefficients F)
    (i j : RP.LazardRootInvariants F)
    (hi : F5.lazard_invariant_relations c i)
    (hj : F5.lazard_invariant_relations c j)
    (hi4 : RP.lazard_root_i4 i = RP.lazard_root_i4 j) :
  lazard_invariant_system_matrix c *m lazard_invariant_tail i =
    lazard_invariant_system_matrix c *m lazard_invariant_tail j.
Proof.
have hrhs := lazard_invariant_system_rhs_eq_of_relations hi hj hi4.
have hbase :
    lazard_invariant_system_rhs c (lazard_invariant_i4_base i) =
      lazard_invariant_system_rhs c (lazard_invariant_i4_base j).
  by rewrite (lazard_invariant_i4_base_eq hi4).
have htotal :
    lazard_invariant_system_rhs c (lazard_invariant_i4_base i) +
        lazard_invariant_system_matrix c *m lazard_invariant_tail i =
      lazard_invariant_system_rhs c (lazard_invariant_i4_base j) +
        lazard_invariant_system_matrix c *m lazard_invariant_tail j :=
  eq_trans (esym (lazard_invariant_system_rhs_affine c i))
    (eq_trans hrhs (lazard_invariant_system_rhs_affine c j)).
have hbase_add :
    lazard_invariant_system_rhs c (lazard_invariant_i4_base j) +
        lazard_invariant_system_matrix c *m lazard_invariant_tail j =
      lazard_invariant_system_rhs c (lazard_invariant_i4_base i) +
        lazard_invariant_system_matrix c *m lazard_invariant_tail j :=
  congr1
    (fun b : 'M[F]_(4, 1) =>
      b + lazard_invariant_system_matrix c *m lazard_invariant_tail j)
    (esym hbase).
have hsame :
    lazard_invariant_system_rhs c (lazard_invariant_i4_base i) +
        lazard_invariant_system_matrix c *m lazard_invariant_tail i =
      lazard_invariant_system_rhs c (lazard_invariant_i4_base i) +
        lazard_invariant_system_matrix c *m lazard_invariant_tail j :=
  eq_trans htotal hbase_add.
exact: (addrI _) hsame.
Qed.

(** Nonvanishing of the literal determinant is the exact boundary at which
    the four Figure-3 equations determine the tail. *)
Theorem lazard_invariant_relations_eq_of_i4_eq_of_det_neq0
    (c : RP.LazardDepressedRootCoefficients F)
    (i j : RP.LazardRootInvariants F)
    (hi : F5.lazard_invariant_relations c i)
    (hj : F5.lazard_invariant_relations c j)
    (hi4 : RP.lazard_root_i4 i = RP.lazard_root_i4 j)
    (hdet : \det (lazard_invariant_system_matrix c) != 0) : i = j.
Proof.
have hmul := lazard_invariant_system_matrix_mul_tail_eq hi hj hi4.
have hunit : lazard_invariant_system_matrix c \in unitmx.
  by rewrite unitmxE unitfE.
have hcancel :
    cancel
      (fun tail : 'M[F]_(4, 1) =>
        lazard_invariant_system_matrix c *m tail)
      (fun image : 'M[F]_(4, 1) =>
        invmx (lazard_invariant_system_matrix c) *m image).
  move=> tail.
  exact: (mulKmx hunit tail).
have htail : lazard_invariant_tail i = lazard_invariant_tail j.
  apply: (can_inj hcancel).
  exact: hmul.
apply: lazard_root_invariants_ext.
- exact: hi4.
- have h := congr1
    (fun tail : 'M[F]_(4, 1) => tail P.p0 ord0) htail.
  by move: h; rewrite /lazard_invariant_tail !mxE /P.p0 /=.
- have h := congr1
    (fun tail : 'M[F]_(4, 1) => tail P.p1 ord0) htail.
  by move: h; rewrite /lazard_invariant_tail !mxE /P.p1 /=.
- have h := congr1
    (fun tail : 'M[F]_(4, 1) => tail P.p2 ord0) htail.
  by move: h; rewrite /lazard_invariant_tail !mxE /P.p2 /=.
- have h := congr1
    (fun tail : 'M[F]_(4, 1) => tail P.p3 ord0) htail.
  by move: h; rewrite /lazard_invariant_tail !mxE /P.p3 /=.
Qed.

(** Root-origin specialization: the left certificate is constructed from
    the orbit-sum definitions by the preceding two modules. *)
Theorem lazard_root_invariants_unique_from_i4
    (roots : 5.-tuple F) (j : RP.LazardRootInvariants F)
    (two_neq0 : (2%:R : F) != 0)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (hj : F5.lazard_invariant_relations
      (RP.lazard_depressed_of_roots roots) j)
    (hi4 : RP.lazard_root_i4 (RP.lazard_root_invariants roots) =
      RP.lazard_root_i4 j)
    (hdet : \det (lazard_invariant_system_matrix
      (RP.lazard_depressed_of_roots roots)) != 0) :
  RP.lazard_root_invariants roots = j.
Proof.
exact: lazard_invariant_relations_eq_of_i4_eq_of_det_neq0
  (F5.lazard_root_invariant_relations two_neq0 hsum) hj hi4 hdet.
Qed.

End InvariantSystem.

Print Assumptions lazard_invariant_system_rhs_affine.
Print Assumptions lazard_invariant_relations_eq_of_i4_eq_of_det_neq0.
Print Assumptions lazard_root_invariants_unique_from_i4.

End PolynomialFormulasLazardQuinticInvariantSystem.
