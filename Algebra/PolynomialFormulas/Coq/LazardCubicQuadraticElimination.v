From Stdlib Require Import Ring Field.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A denominator-free cubic--quadratic elimination certificate.

    The thirteen-term scalar below is the usual expanded formula for the
    determinant of the [5 x 5] cubic--quadratic Sylvester matrix.  This file
    does not yet identify it with MathComp's library [resultant] (nor define
    and expand that Sylvester determinant internally).  Instead, the proofs
    expose the two pseudo-remainders and directly reduce a zero value of the
    displayed scalar to an explicit common-root or common-factor case. *)
Module PolynomialFormulasLazardCubicQuadraticElimination.

Import GRing.Theory.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Local Open Scope ring_scope.

Section CubicQuadratic.

Variable F : fieldType.

Definition lazard_cubic_value
    (a0 a1 a2 a3 x : F) : F :=
  a0 + a1 * x + a2 * x ^+ 2 + a3 * x ^+ 3.

Definition lazard_quadratic_value
    (b0 b1 b2 x : F) : F :=
  b0 + b1 * x + b2 * x ^+ 2.

(** The explicit thirteen-term scalar matching the standard expanded
    cubic--quadratic resultant formula, with both coefficient lists in
    ascending order. *)
Definition lazard_cubic_quadratic_resultant_value
    (a0 a1 a2 a3 b0 b1 b2 : F) : F :=
  a0 ^+ 2 * b2 ^+ 3 - a0 * a1 * b1 * b2 ^+ 2 -
    2%:R * a0 * a2 * b0 * b2 ^+ 2 +
    a0 * a2 * b1 ^+ 2 * b2 +
    3%:R * a0 * a3 * b0 * b1 * b2 - a0 * a3 * b1 ^+ 3 +
    a1 ^+ 2 * b0 * b2 ^+ 2 - a1 * a2 * b0 * b1 * b2 -
    2%:R * a1 * a3 * b0 ^+ 2 * b2 +
    a1 * a3 * b0 * b1 ^+ 2 + a2 ^+ 2 * b0 ^+ 2 * b2 -
    a2 * a3 * b0 ^+ 2 * b1 + a3 ^+ 2 * b0 ^+ 3.

(** Linear pseudo-remainder of the cubic by the quadratic. *)
Definition lazard_cubic_quadratic_R1
    (a1 a2 a3 b0 b1 b2 : F) : F :=
  a1 * b2 ^+ 2 - a3 * b0 * b2 - a2 * b1 * b2 +
    a3 * b1 ^+ 2.

Definition lazard_cubic_quadratic_R0
    (a0 a2 a3 b0 b1 b2 : F) : F :=
  a0 * b2 ^+ 2 - a2 * b0 * b2 + a3 * b0 * b1.

Definition lazard_cubic_quadratic_pseudo_quotient
    (a2 a3 b1 b2 x : F) : F :=
  a3 * b2 * x + (a2 * b2 - a3 * b1).

Definition lazard_cubic_quadratic_norm
    (a0 a1 a2 a3 b0 b1 b2 : F) : F :=
  let r0 := lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2 in
  let r1 := lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2 in
  b0 * r1 ^+ 2 - b1 * r0 * r1 + b2 * r0 ^+ 2.

Add Ring lazard_cubic_quadratic_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_cubic_quadratic_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** The first pseudo-division identity, valid without a nonzero leading
    coefficient assumption. *)
Theorem lazard_cubic_quadratic_pseudo_division
    a0 a1 a2 a3 b0 b1 b2 x :
  b2 ^+ 2 * lazard_cubic_value a0 a1 a2 a3 x =
    lazard_cubic_quadratic_pseudo_quotient a2 a3 b1 b2 x *
      lazard_quadratic_value b0 b1 b2 x +
    lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2 * x +
    lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2.
Proof.
rewrite /lazard_cubic_value /lazard_quadratic_value
  /lazard_cubic_quadratic_pseudo_quotient
  /lazard_cubic_quadratic_R1 /lazard_cubic_quadratic_R0.
finish_lazard_cubic_quadratic_ring.
Qed.

(** The thirteen-term scalar is the quadratic norm of the linear
    pseudo-remainder after multiplication by [b2^2]. *)
Theorem lazard_cubic_quadratic_resultant_norm
    a0 a1 a2 a3 b0 b1 b2 :
  b2 ^+ 2 *
      lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 =
    lazard_cubic_quadratic_norm a0 a1 a2 a3 b0 b1 b2.
Proof.
rewrite /lazard_cubic_quadratic_resultant_value
  /lazard_cubic_quadratic_norm
  /lazard_cubic_quadratic_R1 /lazard_cubic_quadratic_R0.
finish_lazard_cubic_quadratic_ring.
Qed.

(** Evaluation of the quadratic at the explicit root of the nonzero linear
    pseudo-remainder. *)
Lemma lazard_quadratic_at_pseudo_root
    a0 a1 a2 a3 b0 b1 b2
    (r1_neq0 :
      lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2 != 0) :
  lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2 ^+ 2 *
      lazard_quadratic_value b0 b1 b2
        (- lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2 /
          lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2) =
    lazard_cubic_quadratic_norm a0 a1 a2 a3 b0 b1 b2.
Proof.
pose r0 := lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2.
pose r1 := lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2.
pose y := r0 / r1.
have hr1 : r1 * y = r0.
  by rewrite /y [r1 * _]mulrC divfK.
rewrite /lazard_quadratic_value /lazard_cubic_quadratic_norm.
fold r0 r1.
rewrite mulNr.
fold y.
rewrite -[r0 in RHS]hr1 /y.
finish_lazard_cubic_quadratic_ring.
Qed.

(** If both the resultant and the linear pseudo-remainder coefficient vanish,
    then its constant coefficient vanishes as well (provided [b2 != 0]). *)
Lemma lazard_cubic_quadratic_R0_eq0_of_resultant_eq0
    a0 a1 a2 a3 b0 b1 b2
    (b2_neq0 : b2 != 0)
    (hresultant :
      lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 = 0)
    (hR1 : lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2 = 0) :
  lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2 = 0.
Proof.
have hnorm := lazard_cubic_quadratic_resultant_norm
  a0 a1 a2 a3 b0 b1 b2.
rewrite hresultant mulr0 /lazard_cubic_quadratic_norm hR1
  !expr2 ?mulr0 ?mul0r ?subr0 in hnorm.
have hprod :
    b2 *
      (lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2 *
        lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2) = 0.
  rewrite add0r in hnorm.
  exact: esym hnorm.
apply/eqP.
move/eqP: hprod.
rewrite mulf_eq0 (negPf b2_neq0) /=.
move=> hsq.
have /orP [hzero | hzero] :
    (lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2 == 0) ||
    (lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2 == 0).
  by move: hsq; rewrite mulf_eq0.
all: exact: hzero.
Qed.

(** In the genuinely linear-remainder case, the common root is an element of
    the ground field and is displayed explicitly. *)
Theorem lazard_cubic_quadratic_common_root_of_R1_neq0
    a0 a1 a2 a3 b0 b1 b2
    (b2_neq0 : b2 != 0)
    (r1_neq0 :
      lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2 != 0)
    (hresultant :
      lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 = 0) :
  let x :=
    - lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2 /
      lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2 in
  lazard_cubic_value a0 a1 a2 a3 x = 0 /\
    lazard_quadratic_value b0 b1 b2 x = 0.
Proof.
pose r0 := lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2.
pose r1 := lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2.
pose x := - r0 / r1.
have hnorm := lazard_cubic_quadratic_resultant_norm
  a0 a1 a2 a3 b0 b1 b2.
rewrite hresultant mulr0 in hnorm.
have hquad_scaled := @lazard_quadratic_at_pseudo_root
  a0 a1 a2 a3 b0 b1 b2 r1_neq0.
fold r0 r1 x in hquad_scaled.
rewrite -hnorm in hquad_scaled.
have r1_sq_neq0 : r1 ^+ 2 != 0 := expf_neq0 2 r1_neq0.
have hquad : lazard_quadratic_value b0 b1 b2 x = 0.
  apply/eqP.
  move/eqP: hquad_scaled.
  by rewrite mulf_eq0 (negPf r1_sq_neq0).
have hlinear : r1 * x + r0 = 0.
  rewrite /x mulNr mulrN [r1 * (r0 / r1)]mulrC divfK //.
  by rewrite addNr.
have hpseudo := lazard_cubic_quadratic_pseudo_division
  a0 a1 a2 a3 b0 b1 b2 x.
fold r0 r1 x in hpseudo.
rewrite hquad mulr0 add0r hlinear in hpseudo.
have b2_sq_neq0 : b2 ^+ 2 != 0 := expf_neq0 2 b2_neq0.
have hcubic : lazard_cubic_value a0 a1 a2 a3 x = 0.
  apply/eqP.
  move/eqP: hpseudo.
  by rewrite mulf_eq0 (negPf b2_sq_neq0).
by split.
Qed.

(** When the quadratic term vanishes but the linear term does not, the same
    determinant has the evident linear common root. *)
Theorem lazard_cubic_quadratic_common_root_of_b2_eq0
    a0 a1 a2 a3 b0 b1 b2
    (a3_neq0 : a3 != 0)
    (hb2 : b2 = 0) (b1_neq0 : b1 != 0)
    (hresultant :
      lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 = 0) :
  let x := - b0 / b1 in
  lazard_cubic_value a0 a1 a2 a3 x = 0 /\
    lazard_quadratic_value b0 b1 b2 x = 0.
Proof.
pose y := b0 / b1.
pose x := - y.
have hb1 : b1 * y = b0.
  by rewrite /y [b1 * _]mulrC divfK.
have hb0 : b0 = b1 * y := esym hb1.
have hx : x = - b0 / b1.
  by rewrite /x /y mulNr.
rewrite -hx.
have hscaled :
    lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 =
      - a3 * (b1 ^+ 3 * lazard_cubic_value a0 a1 a2 a3 x).
  rewrite hb2 /lazard_cubic_quadratic_resultant_value
    /lazard_cubic_value hb0 /x.
  finish_lazard_cubic_quadratic_ring.
have b1_cube_neq0 : b1 ^+ 3 != 0 := expf_neq0 3 b1_neq0.
have hcubic : lazard_cubic_value a0 a1 a2 a3 x = 0.
  apply/eqP.
  move/eqP: hresultant.
  rewrite hscaled mulf_eq0 oppr_eq0 (negPf a3_neq0) /=.
  by rewrite mulf_eq0 (negPf b1_cube_neq0).
have hquad : lazard_quadratic_value b0 b1 b2 x = 0.
  rewrite /lazard_quadratic_value hb2 mul0r addr0 hb0 /x.
  finish_lazard_cubic_quadratic_ring.
by split.
Qed.

(** Fully constant remainder case. *)
Lemma lazard_cubic_quadratic_b0_eq0_of_constant_remainder
    a0 a1 a2 a3 b0 b1 b2
    (a3_neq0 : a3 != 0)
    (hb2 : b2 = 0) (hb1 : b1 = 0)
    (hresultant :
      lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 = 0) :
  b0 = 0.
Proof.
have hreduce :
    lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 = a3 ^+ 2 * b0 ^+ 3.
  rewrite hb2 hb1 /lazard_cubic_quadratic_resultant_value.
  finish_lazard_cubic_quadratic_ring.
rewrite hreduce in hresultant.
apply/eqP.
move/eqP: hresultant.
rewrite mulf_eq0 expf_eq0 (negPf a3_neq0) /=.
by rewrite expf_eq0.
Qed.

(** Complete denominator-free zero certificate.  The middle disjunct means
    that the whole quadratic divides the scaled cubic; the last means that
    the quadratic remainder is the zero polynomial. *)
Theorem lazard_cubic_quadratic_zero_certificate
    a0 a1 a2 a3 b0 b1 b2
    (a3_neq0 : a3 != 0)
    (hresultant :
      lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 = 0) :
  (exists x,
      lazard_cubic_value a0 a1 a2 a3 x = 0 /\
      lazard_quadratic_value b0 b1 b2 x = 0) \/
  (b2 != 0 /\
    lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2 = 0 /\
    lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2 = 0) \/
  (b2 = 0 /\ b1 = 0 /\ b0 = 0).
Proof.
case hb2: (b2 == 0).
- have hb2P : b2 = 0 := eqP hb2.
  case hb1: (b1 == 0).
  + right; right; split=> //; split; first exact: eqP hb1.
    exact: lazard_cubic_quadratic_b0_eq0_of_constant_remainder
      a3_neq0 hb2P (eqP hb1) hresultant.
  + left.
    have hroot := lazard_cubic_quadratic_common_root_of_b2_eq0
      a3_neq0 hb2P (negbT hb1) hresultant.
    exists (- b0 / b1); exact: hroot.
- have b2_neq0 : b2 != 0 := negbT hb2.
  case hR1 :
    (lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2 == 0).
  + right; left.
    split.
    { by []. }
    split.
    { exact: eqP hR1. }
    exact: lazard_cubic_quadratic_R0_eq0_of_resultant_eq0
      b2_neq0 hresultant (eqP hR1).
  + left.
    have hroot := lazard_cubic_quadratic_common_root_of_R1_neq0
      b2_neq0 (negbT hR1) hresultant.
    exists
      (- lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2 /
        lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2).
    exact: hroot.
Qed.

End CubicQuadratic.

Print Assumptions lazard_cubic_quadratic_pseudo_division.
Print Assumptions lazard_cubic_quadratic_resultant_norm.
Print Assumptions lazard_cubic_quadratic_zero_certificate.

End PolynomialFormulasLazardCubicQuadraticElimination.
