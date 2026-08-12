From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootFourierNumeratorRing
  LazardCubicQuadraticElimination
  LazardCriticalPolynomialCommonDivisor
  LazardQuinticCriticalElimination.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The critical cubic--quadratic scalar as a Sylvester determinant.

    Lazard's paper does not call this scalar a resultant and does not use a
    Sylvester matrix in its separability argument.  This is an exact library
    bridge for the corrected formal proof.

    MathComp defines [resultant p q] using the actual, trimmed sizes of [p]
    and [q].  Thus the unconditional statement is first made for a fixed
    formal [5 x 5] Sylvester matrix.  Its identification with MathComp's
    [resultant] additionally assumes that the displayed cubic and quadratic
    leading coefficients are nonzero.  The already-proved direct
    common-divisor endpoint remains unconditional in the quadratic leading
    coefficient and is re-exported below. *)
Module PolynomialFormulasLazardCriticalSylvesterResultantBridge.

Import GRing.Theory.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module CQ := PolynomialFormulasLazardCubicQuadraticElimination.
Module PC := PolynomialFormulasLazardCriticalPolynomialCommonDivisor.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module CE := PolynomialFormulasLazardQuinticCriticalElimination.
Local Open Scope ring_scope.

Section SylvesterResultant.

Variable F : fieldType.

(** MathComp's row convention: two shifted cubic rows, followed by three
    shifted quadratic rows.  The matrix displayed by Mathlib is its
    transpose after an even [2 x 3] block exchange, so there is no sign
    change. *)
Definition lazard_cubic_quadratic_formal_sylvester_matrix
    (a0 a1 a2 a3 b0 b1 b2 : F) : 'M[F]_5 :=
  \matrix_(i < 5, j < 5)
    (nth [::]
      [:: [:: a0; a1; a2; a3; 0];
          [:: 0; a0; a1; a2; a3];
          [:: b0; b1; b2; 0; 0];
          [:: 0; b0; b1; b2; 0];
          [:: 0; 0; b0; b1; b2]] i)`_j.

Add Ring lazard_critical_sylvester_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_critical_sylvester_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** Direct kernel-checked expansion of the fixed formal Sylvester
    determinant.  This statement has no leading-coefficient hypotheses. *)
Theorem lazard_formal_sylvester_det_eq_resultant_value
    (a0 a1 a2 a3 b0 b1 b2 : F) :
  \det (lazard_cubic_quadratic_formal_sylvester_matrix
    a0 a1 a2 a3 b0 b1 b2) =
  CQ.lazard_cubic_quadratic_resultant_value
    a0 a1 a2 a3 b0 b1 b2.
Proof.
rewrite /lazard_cubic_quadratic_formal_sylvester_matrix.
do ?[rewrite (expand_det_row _ ord0) //=;
  rewrite ?(big_ord_recl, big_ord0) //= ?mxE //=;
  rewrite /cofactor /= ?(addn0, add0n, expr0, exprS);
  rewrite ?(mul1r, mulr1, mulN1r, mul0r, mulr0, addr0, add0r) /=;
  do ?rewrite [row' _ _]mx11_scalar det_scalar1 !mxE /=].
rewrite /CQ.lazard_cubic_quadratic_resultant_value !expr2.
finish_lazard_critical_sylvester_ring.
Qed.

Lemma lazard_cubic_polynomial_coefficient a0 a1 a2 a3 n :
  (PC.lazard_cubic_polynomial a0 a1 a2 a3)`_n =
    nth 0 [:: a0; a1; a2; a3] n.
Proof.
case: n => [|[|[|[|n]]]].
all: rewrite /PC.lazard_cubic_polynomial !coefD !coefMX !coefC /=.
all: repeat first
  [ rewrite mulr0 | rewrite mulr1 | rewrite add0r | rewrite addr0 ].
all: by [].
Qed.

Lemma lazard_quadratic_polynomial_coefficient b0 b1 b2 n :
  (PC.lazard_quadratic_polynomial b0 b1 b2)`_n =
    nth 0 [:: b0; b1; b2] n.
Proof.
case: n => [|[|[|n]]].
all: rewrite /PC.lazard_quadratic_polynomial !coefD !coefMX !coefC /=.
all: repeat first
  [ rewrite mulr0 | rewrite mulr1 | rewrite add0r | rewrite addr0 ].
all: by [].
Qed.

(** With actual degrees three and two, MathComp's size-dependent Sylvester
    matrix is the fixed matrix above. *)
Lemma lazard_library_sylvester_det_eq_formal
    (a0 a1 a2 a3 b0 b1 b2 : F)
    (a3_neq0 : a3 != 0) (b2_neq0 : b2 != 0) :
  \det (Sylvester_mx
    (PC.lazard_cubic_polynomial a0 a1 a2 a3)
    (PC.lazard_quadratic_polynomial b0 b1 b2)) =
  \det (lazard_cubic_quadratic_formal_sylvester_matrix
    a0 a1 a2 a3 b0 b1 b2).
Proof.
rewrite (PC.lazard_cubic_polynomial_size a3_neq0)
  (PC.lazard_quadratic_polynomial_size b2_neq0) /=.
congr (\det _).
apply/matrixP=> i j.
rewrite Sylvester_mxE
  /lazard_cubic_quadratic_formal_sylvester_matrix !mxE.
case: i => [[|[|[|[|[|i]]]]] hi] //=;
case: j => [[|[|[|[|[|j]]]]] hj] //=;
rewrite ?lazard_cubic_polynomial_coefficient
  ?lazard_quadratic_polynomial_coefficient //=.
Qed.

(** Exact identification with MathComp's actual-degree library resultant.
    Both leading-coefficient assumptions are essential to this formulation,
    because MathComp trims leading zero coefficients before choosing the
    Sylvester matrix dimension. *)
Theorem lazard_mathcomp_resultant_eq_resultant_value
    (a0 a1 a2 a3 b0 b1 b2 : F)
    (a3_neq0 : a3 != 0) (b2_neq0 : b2 != 0) :
  resultant
      (PC.lazard_cubic_polynomial a0 a1 a2 a3)
      (PC.lazard_quadratic_polynomial b0 b1 b2) =
    CQ.lazard_cubic_quadratic_resultant_value
      a0 a1 a2 a3 b0 b1 b2.
Proof.
rewrite /resultant
  (lazard_library_sylvester_det_eq_formal a3_neq0 b2_neq0).
exact: lazard_formal_sylvester_det_eq_resultant_value.
Qed.

(** The standard zero/common-factor consequence through MathComp's library
    resultant, in the nondegenerate actual-degree case. *)
Theorem lazard_mathcomp_resultant_zero_iff_common_divisor
    (a0 a1 a2 a3 b0 b1 b2 : F)
    (a3_neq0 : a3 != 0) (b2_neq0 : b2 != 0) :
  CQ.lazard_cubic_quadratic_resultant_value
      a0 a1 a2 a3 b0 b1 b2 == 0 =
    (1 < size (gcdp
      (PC.lazard_cubic_polynomial a0 a1 a2 a3)
      (PC.lazard_quadratic_polynomial b0 b1 b2)))%N.
Proof.
rewrite -lazard_mathcomp_resultant_eq_resultant_value //.
exact: resultant_eq0.
Qed.

(** Re-export of the stronger direct endpoint.  It also covers a constant or
    zero displayed quadratic, where MathComp's actual-degree resultant is not
    represented by the fixed [5 x 5] matrix. *)
Theorem lazard_formal_resultant_zero_nonconstant_common_divisor
    (a0 a1 a2 a3 b0 b1 b2 : F)
    (a3_neq0 : a3 != 0)
    (hresultant :
      CQ.lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 = 0) :
  exists u : {poly F},
    (1 < size u)%N /\
    (u %| PC.lazard_cubic_polynomial a0 a1 a2 a3) /\
    (u %| PC.lazard_quadratic_polynomial b0 b1 b2).
Proof.
exact: PC.lazard_resultant_zero_nonconstant_common_divisor.
Qed.

(** The literal specialization used by the Figure-3 determinant
    certificate. *)
Definition lazard_critical_formal_sylvester_matrix
    (c : RP.LazardDepressedRootCoefficients F) : 'M[F]_5 :=
  lazard_cubic_quadratic_formal_sylvester_matrix
    (CE.lazard_critical_g c -
      2%:R * CE.lazard_critical_b c * CE.lazard_critical_e c)
    (- 4%:R * CE.lazard_critical_a c * CE.lazard_critical_e c -
      CE.lazard_critical_b c)
    (- 3%:R * CE.lazard_critical_a c - 6%:R * CE.lazard_critical_e c)
    (- 5%:R)
    (CE.lazard_critical_remainder0 c)
    (CE.lazard_critical_remainder1 c)
    (CE.lazard_critical_remainder2 c).

(** Exact, unconditional fixed-Sylvester interpretation of the scalar that
    appears in [lazard_critical_resultant_value_certificate]. *)
Theorem lazard_critical_resultant_value_eq_formal_sylvester_det
    (c : RP.LazardDepressedRootCoefficients F) :
  CE.lazard_critical_resultant_value c =
    \det (lazard_critical_formal_sylvester_matrix c).
Proof.
rewrite /CE.lazard_critical_resultant_value
  /lazard_critical_formal_sylvester_matrix.
symmetry.
exact: lazard_formal_sylvester_det_eq_resultant_value.
Qed.

End SylvesterResultant.

Print Assumptions lazard_formal_sylvester_det_eq_resultant_value.
Print Assumptions lazard_mathcomp_resultant_eq_resultant_value.
Print Assumptions lazard_formal_resultant_zero_nonconstant_common_divisor.
Print Assumptions lazard_critical_resultant_value_eq_formal_sylvester_det.

End PolynomialFormulasLazardCriticalSylvesterResultantBridge.
