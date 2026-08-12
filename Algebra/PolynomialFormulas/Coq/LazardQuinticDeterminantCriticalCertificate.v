From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticDeterminantCertificateMatrix
  LazardCubicQuadraticElimination
  LazardQuinticCriticalElimination
  LazardQuinticDeterminantCriticalData
  LazardQuinticDeterminantCriticalInputA
  LazardQuinticDeterminantCriticalInputB
  LazardQuinticDeterminantCriticalPolynomial
  LazardQuinticDeterminantCriticalCoefficient0
  LazardQuinticDeterminantCriticalCoefficient1
  LazardQuinticDeterminantCriticalCoefficient2
  LazardQuinticDeterminantCriticalCoefficient3
  LazardQuinticDeterminantCriticalCoefficient4
  LazardQuinticDeterminantCriticalCoefficient5
  LazardQuinticDeterminantCriticalCoefficient6
  LazardQuinticDeterminantCriticalCoefficient7
  LazardQuinticDeterminantCriticalCoefficient8
  LazardQuinticDeterminantCriticalCoefficient9
  LazardQuinticDeterminantCriticalCoefficient10
  LazardQuinticDeterminantCriticalCoefficient11
  LazardQuinticDeterminantCriticalCoefficient12.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Proof-light assembly of the coefficient shards, followed by evaluation at
    the depressed-quintic coefficient [s]. *)
Module PolynomialFormulasLazardQuinticDeterminantCriticalCertificate.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module DM := PolynomialFormulasLazardQuinticDeterminantCertificateMatrix.
Module CQ := PolynomialFormulasLazardCubicQuadraticElimination.
Module CE := PolynomialFormulasLazardQuinticCriticalElimination.
Module D := PolynomialFormulasLazardQuinticDeterminantCriticalData.
Module IA := PolynomialFormulasLazardQuinticDeterminantCriticalInputA.
Module IB := PolynomialFormulasLazardQuinticDeterminantCriticalInputB.
Module P := PolynomialFormulasLazardQuinticDeterminantCriticalPolynomial.
Module C0 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient0.
Module C1 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient1.
Module C2 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient2.
Module C3 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient3.
Module C4 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient4.
Module C5 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient5.
Module C6 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient6.
Module C7 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient7.
Module C8 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient8.
Module C9 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient9.
Module C10 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient10.
Module C11 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient11.
Module C12 := PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient12.
Local Open Scope ring_scope.

Section Certificate.

Variable F : fieldType.

Theorem lazard_detcritical_polynomial_certificate c
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0) :
  D.lazard_detcritical_V_polynomial c =
    D.lazard_detcritical_target_polynomial c.
Proof.
apply/polyP=> i.
case: i => [|i].
- exact: C0.lazard_detcritical_coefficient_0 c two_neq0 five_neq0.
case: i => [|i].
- exact: C1.lazard_detcritical_coefficient_1 c two_neq0 five_neq0.
case: i => [|i].
- exact: C2.lazard_detcritical_coefficient_2 c two_neq0 five_neq0.
case: i => [|i].
- exact: C3.lazard_detcritical_coefficient_3 c two_neq0 five_neq0.
case: i => [|i].
- exact: C4.lazard_detcritical_coefficient_4 c two_neq0 five_neq0.
case: i => [|i].
- exact: C5.lazard_detcritical_coefficient_5 c two_neq0 five_neq0.
case: i => [|i].
- exact: C6.lazard_detcritical_coefficient_6 c two_neq0 five_neq0.
case: i => [|i].
- exact: C7.lazard_detcritical_coefficient_7 c two_neq0 five_neq0.
case: i => [|i].
- exact: C8.lazard_detcritical_coefficient_8 c two_neq0 five_neq0.
case: i => [|i].
- exact: C9.lazard_detcritical_coefficient_9 c two_neq0 five_neq0.
case: i => [|i].
- exact: C10.lazard_detcritical_coefficient_10 c two_neq0 five_neq0.
case: i => [|i].
- exact: C11.lazard_detcritical_coefficient_11 c two_neq0 five_neq0.
case: i => [|i].
- exact: C12.lazard_detcritical_coefficient_12 c two_neq0 five_neq0.
change
  (coef (D.lazard_detcritical_V_polynomial c) (13 + i) =
    coef (D.lazard_detcritical_target_polynomial c) (13 + i)).
have hge : (13 <= 13 + i)%N.
  by apply/leP; lia.
have hleft :
    coef (D.lazard_detcritical_V_polynomial c) (13 + i) = 0.
  exact: (elimT (leq_sizeP _ 13)
    (P.lazard_detcritical_V_polynomial_size c) _ hge).
have hright :
    coef (D.lazard_detcritical_target_polynomial c) (13 + i) = 0.
  exact: (elimT (leq_sizeP _ 13)
    (P.lazard_detcritical_target_polynomial_size c) _ hge).
by rewrite hleft hright.
Qed.

(** The specialized explicit thirteen-term cubic/quadratic scalar is the
    negative square of the compact Figure-3 determinant numerator, divided
    by 125.  This is exactly the sign and normalization used by the Lean
    certificate; no identification with MathComp's [resultant] is asserted
    here. *)
Theorem lazard_critical_resultant_value_certificate c
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0) :
  CE.lazard_critical_resultant_value c =
    - (DM.lazard_det_certificate_compact_numerator c ^+ 2) / 125%:R.
Proof.
rewrite /CE.lazard_critical_resultant_value.
transitivity
  ((D.lazard_detcritical_V_polynomial c).[RP.lazard_root_s c]).
- rewrite /D.lazard_detcritical_V_polynomial
    P.lazard_detcritical_polynomial_value_horner
    (IA.lazard_detcritical_PA0_eval c two_neq0)
    (IA.lazard_detcritical_PA1_eval c two_neq0)
    (IA.lazard_detcritical_PA2_eval c two_neq0)
    (IA.lazard_detcritical_PA3_eval c)
    (IB.lazard_detcritical_PB0_eval c two_neq0 five_neq0)
    (IB.lazard_detcritical_PB1_eval c two_neq0 five_neq0)
    (IB.lazard_detcritical_PB2_eval c two_neq0 five_neq0).
  reflexivity.
- rewrite (lazard_detcritical_polynomial_certificate c
      two_neq0 five_neq0)
    /D.lazard_detcritical_target_polynomial
    hornerN hornerZ horner_exp
    P.lazard_detcritical_N_polynomial_horner.
  by rewrite divNr div1r [(125%:R : F)^-1 * _]mulrC.
Qed.

End Certificate.

Print Assumptions lazard_detcritical_polynomial_certificate.
Print Assumptions lazard_critical_resultant_value_certificate.

End PolynomialFormulasLazardQuinticDeterminantCriticalCertificate.
