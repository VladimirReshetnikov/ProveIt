From Stdlib Require Import Ring Field.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticProjection
  LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelationFifthData
  LazardQuinticRootInvariantRelationFifth
  LazardQuinticInvariantSystem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A compact, independently auditable coefficient certificate for the
    determinant of Lazard's Figure-3 matrix.  The coefficient split is the
    one used by the Lean development: it is polynomial in the constant
    coefficient [s], with the degree-five coefficient identically zero.

    Large printed integers are written by their exact base-10
    factorizations (for example [(50 + 35) * 10000] for [850000] and
    [625 * 15625] for [9765625]).  This preserves the printed coefficients
    while avoiding kernel construction of enormous unary natural terms. *)
Module PolynomialFormulasLazardQuinticDeterminantCertificateMatrix.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module P := PolynomialFormulasLazardQuinticProjection.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module D := PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.
Module F5 := PolynomialFormulasLazardQuinticRootInvariantRelationFifth.
Module IS := PolynomialFormulasLazardQuinticInvariantSystem.
Local Open Scope ring_scope.

Section DeterminantCertificate.

Variable F : fieldType.

Definition lazard_det_certificate_N0
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  RP.lazard_root_q c ^+ 2 *
    (81%:R * RP.lazard_root_p c ^+ 8 * RP.lazard_root_r c ^+ 2 -
      36%:R * RP.lazard_root_p c ^+ 7 * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c +
      4%:R * RP.lazard_root_p c ^+ 6 * RP.lazard_root_q c ^+ 4 -
      1800%:R * RP.lazard_root_p c ^+ 6 * RP.lazard_root_r c ^+ 3 +
      (200%:R * 10%:R + 15%:R) * RP.lazard_root_p c ^+ 5 *
        RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c ^+ 2 -
      (620%:R + 3%:R) * RP.lazard_root_p c ^+ 4 *
        RP.lazard_root_q c ^+ 4 *
        RP.lazard_root_r c +
      10000%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c ^+ 4 +
      (50%:R + 9%:R) * RP.lazard_root_p c ^+ 3 *
        RP.lazard_root_q c ^+ 6 -
      (7%:R * 25%:R * 100%:R) * RP.lazard_root_p c ^+ 3 *
        RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c ^+ 3 +
      (10000%:R + 33%:R * 25%:R) * RP.lazard_root_p c ^+ 2 *
        RP.lazard_root_q c ^+ 4 *
        RP.lazard_root_r c ^+ 2 -
      (2600%:R + 10%:R) * RP.lazard_root_p c *
        RP.lazard_root_q c ^+ 6 *
        RP.lazard_root_r c +
      (6%:R * 6%:R * 6%:R) * RP.lazard_root_q c ^+ 8 +
      625%:R * RP.lazard_root_q c ^+ 4 * RP.lazard_root_r c ^+ 3).

Definition lazard_det_certificate_N1
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - 2%:R * RP.lazard_root_q c *
    ((3%:R * 81%:R) * RP.lazard_root_p c ^+ 9 *
        RP.lazard_root_r c -
      54%:R * RP.lazard_root_p c ^+ 8 * RP.lazard_root_q c ^+ 2 -
      (54%:R * 100%:R) * RP.lazard_root_p c ^+ 7 *
        RP.lazard_root_r c ^+ 2 +
      (6%:R * 81%:R * 10%:R) * RP.lazard_root_p c ^+ 6 *
        RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c -
      (6%:R * 12%:R * 11%:R) * RP.lazard_root_p c ^+ 5 *
        RP.lazard_root_q c ^+ 4 +
      (3%:R * 10000%:R) * RP.lazard_root_p c ^+ 5 *
        RP.lazard_root_r c ^+ 3 -
      ((40%:R + 6%:R) * 1000%:R + 250%:R) *
        RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c ^+ 2 +
      (225%:R * 100%:R + 25%:R) * RP.lazard_root_p c ^+ 3 *
        RP.lazard_root_q c ^+ 4 *
        RP.lazard_root_r c -
      (28%:R * 100%:R + 50%:R) * RP.lazard_root_p c ^+ 2 *
        RP.lazard_root_q c ^+ 6 +
      (25%:R * 1000%:R) * RP.lazard_root_p c ^+ 2 *
        RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c ^+ 3 -
      (16%:R * 1000%:R + 250%:R) * RP.lazard_root_p c *
        RP.lazard_root_q c ^+ 4 *
        RP.lazard_root_r c ^+ 2 +
      (45%:R * 100%:R) * RP.lazard_root_q c ^+ 6 *
        RP.lazard_root_r c).

Definition lazard_det_certificate_N2
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  (9%:R * 81%:R) * RP.lazard_root_p c ^+ 10 -
    (18%:R * 1000%:R + 225%:R) * RP.lazard_root_p c ^+ 8 *
      RP.lazard_root_r c +
    (12%:R * 1000%:R + 15%:R * 10%:R) *
      RP.lazard_root_p c ^+ 7 * RP.lazard_root_q c ^+ 2 +
    ((100%:R + 35%:R) * 1000%:R) * RP.lazard_root_p c ^+ 6 *
      RP.lazard_root_r c ^+ 2 -
    (7%:R * 25%:R * 1000%:R + 500%:R) *
      RP.lazard_root_p c ^+ 5 * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c +
    (6%:R * 10000%:R) * RP.lazard_root_p c ^+ 4 *
      RP.lazard_root_q c ^+ 4 -
    (25%:R * 10000%:R) * RP.lazard_root_p c ^+ 4 *
      RP.lazard_root_r c ^+ 3 +
    ((50%:R + 35%:R) * 10000%:R) * RP.lazard_root_p c ^+ 3 *
      RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c ^+ 2 -
    ((140%:R + 13%:R) * 3125%:R) * RP.lazard_root_p c ^+ 2 *
      RP.lazard_root_q c ^+ 4 *
      RP.lazard_root_r c +
    (3%:R * 2%:R * 15625%:R) * RP.lazard_root_p c *
      RP.lazard_root_q c ^+ 6 +
    15625%:R * RP.lazard_root_q c ^+ 4 * RP.lazard_root_r c ^+ 2.

Definition lazard_det_certificate_N3
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - (4%:R * 3125%:R) * RP.lazard_root_q c *
    (81%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c -
      18%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 -
      100%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 2 +
      95%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
        RP.lazard_root_r c -
      14%:R * RP.lazard_root_q c ^+ 4).

Definition lazard_det_certificate_N4
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  3125%:R *
    ((27%:R * 11%:R) * RP.lazard_root_p c ^+ 5 -
      900%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c +
      600%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 -
      125%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c).

Definition lazard_det_certificate_N6
    (_c : RP.LazardDepressedRootCoefficients F) : F :=
  - (625%:R * 15625%:R).

Definition lazard_det_certificate_compact_numerator
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  lazard_det_certificate_N0 c +
    lazard_det_certificate_N1 c * RP.lazard_root_s c +
    lazard_det_certificate_N2 c * RP.lazard_root_s c ^+ 2 +
    lazard_det_certificate_N3 c * RP.lazard_root_s c ^+ 3 +
    lazard_det_certificate_N4 c * RP.lazard_root_s c ^+ 4 +
    lazard_det_certificate_N6 c * RP.lazard_root_s c ^+ 6.

(** Closed determinant polynomials used to keep the concrete Figure-3
    matrix out of recursive dependent-minor reduction. *)
Definition lazard_det3
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : F) : F :=
  a00 * (a11 * a22 - a12 * a21) -
    a01 * (a10 * a22 - a12 * a20) +
    a02 * (a10 * a21 - a11 * a20).

Definition lazard_det4_of_matrix (M : 'M[F]_4) : F :=
  M P.p0 P.p0 *
      lazard_det3
        (M P.p1 P.p1) (M P.p1 P.p2) (M P.p1 P.p3)
        (M P.p2 P.p1) (M P.p2 P.p2) (M P.p2 P.p3)
        (M P.p3 P.p1) (M P.p3 P.p2) (M P.p3 P.p3) -
  M P.p0 P.p1 *
      lazard_det3
        (M P.p1 P.p0) (M P.p1 P.p2) (M P.p1 P.p3)
        (M P.p2 P.p0) (M P.p2 P.p2) (M P.p2 P.p3)
        (M P.p3 P.p0) (M P.p3 P.p2) (M P.p3 P.p3) +
  M P.p0 P.p2 *
      lazard_det3
        (M P.p1 P.p0) (M P.p1 P.p1) (M P.p1 P.p3)
        (M P.p2 P.p0) (M P.p2 P.p1) (M P.p2 P.p3)
        (M P.p3 P.p0) (M P.p3 P.p1) (M P.p3 P.p3) -
  M P.p0 P.p3 *
      lazard_det3
        (M P.p1 P.p0) (M P.p1 P.p1) (M P.p1 P.p2)
        (M P.p2 P.p0) (M P.p2 P.p1) (M P.p2 P.p2)
        (M P.p3 P.p0) (M P.p3 P.p1) (M P.p3 P.p2).

(** Local packed-field bridge for the standard [field] tactic.  Its ring
    operations are exactly the public numerator-ring operations used by
    [lazard_fifth_prepare], so the two reflective preprocessors agree. *)
Local Definition lazard_det_div :
    NR.lazard_numerator_ring_carrier F ->
      NR.lazard_numerator_ring_carrier F ->
      NR.lazard_numerator_ring_carrier F := fun x y => x / y.
Local Definition lazard_det_inv :
    NR.lazard_numerator_ring_carrier F ->
      NR.lazard_numerator_ring_carrier F := @GRing.inv F.

Lemma lazard_det_divE (x y : F) : x / y = lazard_det_div x y. Proof. reflexivity. Qed.
Lemma lazard_det_invE (x : F) : x^-1 = lazard_det_inv x. Proof. reflexivity. Qed.

Lemma lazard_det_field_theory :
  @field_theory (NR.lazard_numerator_ring_carrier F)
    (@NR.lazard_numerator_ring_zero F)
    (@NR.lazard_numerator_ring_one F)
    (@NR.lazard_numerator_ring_add F)
    (@NR.lazard_numerator_ring_mul F)
    (@NR.lazard_numerator_ring_sub F)
    (@NR.lazard_numerator_ring_opp F)
    lazard_det_div lazard_det_inv
    (@NR.lazard_numerator_ring_eq F).
Proof.
constructor.
- exact: (@NR.lazard_numerator_ring_theory F).
- unfold NR.lazard_numerator_ring_one, NR.lazard_numerator_ring_zero,
    NR.lazard_numerator_ring_eq.
  move=> h10; have h := (@oner_neq0 F).
  by move: h; rewrite h10 eqxx.
- by unfold lazard_det_div, lazard_det_inv,
    NR.lazard_numerator_ring_mul, NR.lazard_numerator_ring_eq.
- move=> x hx.
  unfold lazard_det_inv, NR.lazard_numerator_ring_mul,
    NR.lazard_numerator_ring_one, NR.lazard_numerator_ring_zero,
    NR.lazard_numerator_ring_eq in *.
  apply: mulVr; rewrite unitfE.
  apply/negP=> /eqP hx0; exact: hx hx0.
Qed.

Add Ring lazard_det_ring : (@NR.lazard_numerator_ring_theory F).
Add Field lazard_det_field : lazard_det_field_theory.
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq lazard_det_div lazard_det_inv.

Definition lazard_ord4_enum : seq 'I_4 := [:: P.p0; P.p1; P.p2; P.p3].

Lemma lazard_nth_ord4_enum (i : 'I_4) :
  nth P.p0 lazard_ord4_enum i = i.
Proof.
case: i => [[|[|[|[|i]]]] hi] /=.
- by apply/val_inj.
- by apply/val_inj.
- by apply/val_inj.
- by apply/val_inj.
- by [].
Qed.

Definition lazard_matrix4_canonical (M : 'M[F]_4) : 'M[F]_4 :=
  \matrix_(i, j)
    M (nth P.p0 lazard_ord4_enum i) (nth P.p0 lazard_ord4_enum j).

Lemma lazard_matrix4_canonicalE (M : 'M[F]_4) :
  lazard_matrix4_canonical M = M.
Proof.
apply/matrixP=> i j.
by rewrite /lazard_matrix4_canonical !mxE !lazard_nth_ord4_enum.
Qed.

Lemma lazard_det4_of_matrixE (M : 'M[F]_4) :
  \det M = lazard_det4_of_matrix M.
Proof.
have hcanonical : M = lazard_matrix4_canonical M.
  exact: (esym (lazard_matrix4_canonicalE M)).
pose N := lazard_matrix4_canonical M.
have hN : N = lazard_matrix4_canonical M by reflexivity.
clearbody N.
have hMN : M = N := eq_trans hcanonical (esym hN).
rewrite {1}hMN.
rewrite /lazard_det4_of_matrix /lazard_det3.
do ?[rewrite (expand_det_row _ ord0) //=;
  rewrite ?(big_ord_recl, big_ord0) //= ?mxE //=;
  rewrite /cofactor /= ?(addn0, add0n, expr0, exprS);
  rewrite ?(mul1r, mulr1, mulN1r, mul0r, mulr0, addr0) /=;
  do ?rewrite [row' _ _]mx11_scalar det_scalar1 !mxE /=].
rewrite hN /lazard_matrix4_canonical /lazard_ord4_enum !mxE /=.
lazard_numerator_prepare.
match goal with
| |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
end.
ring.
Qed.

Ltac lazard_det_prepare := lazard_fifth_prepare.

Ltac finish_lazard_det_field :=
  lazard_det_prepare;
  repeat first
    [ rewrite lazard_det_divE | rewrite lazard_det_invE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  field.

(** Direct determinant expansion of the literal Figure-3 matrix. *)
Theorem lazard_invariant_system_matrix_det_formula
    (c : RP.LazardDepressedRootCoefficients F)
    (two_neq0 : (2%:R : F) != 0) :
  \det (IS.lazard_invariant_system_matrix c) =
    lazard_det_certificate_compact_numerator c / 2%:R.
Proof.
have two_not0 : (2%:R : F) <> 0.
  move=> htwo; move: two_neq0.
  by rewrite htwo eqxx.
rewrite lazard_det4_of_matrixE
  /lazard_det4_of_matrix /lazard_det3
  /IS.lazard_invariant_system_matrix
  /D.lazard_fifth_printed_i5 /D.lazard_fifth_printed_i6
  /D.lazard_fifth_printed_i7 /D.lazard_fifth_printed_i8
  /P.p0 /P.p1 /P.p2 /P.p3 !mxE /=.
rewrite /lazard_det_certificate_compact_numerator
  /lazard_det_certificate_N0 /lazard_det_certificate_N1
  /lazard_det_certificate_N2 /lazard_det_certificate_N3
  /lazard_det_certificate_N4 /lazard_det_certificate_N6.
finish_lazard_det_field.
Qed.

End DeterminantCertificate.

Print Assumptions lazard_invariant_system_matrix_det_formula.

End PolynomialFormulasLazardQuinticDeterminantCertificateMatrix.
