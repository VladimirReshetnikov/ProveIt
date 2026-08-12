From Stdlib Require Import Ring Field.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticDeterminantCertificateMatrix
  LazardQuinticCriticalElimination
  LazardQuinticDeterminantCriticalData
  LazardQuinticDeterminantCriticalSupport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Degree-9 shard of the polynomial-in-s determinant certificate. *)
Module PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient9.

Import GRing.Theory.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module DM := PolynomialFormulasLazardQuinticDeterminantCertificateMatrix.
Module CE := PolynomialFormulasLazardQuinticCriticalElimination.
Module D := PolynomialFormulasLazardQuinticDeterminantCriticalData.
Local Open Scope ring_scope.

Section Coefficient9.

Variable F : fieldType.

Add Ring lazard_detcritical_coefficient_9_ring :
  (@NR.lazard_numerator_ring_theory F).
Add Field lazard_detcritical_coefficient_9_field :
  (@CE.lazard_critical_field_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq CE.lazard_critical_div
  CE.lazard_critical_inv.

Theorem lazard_detcritical_coefficient_9 c
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0) :
  coef (D.lazard_detcritical_V_polynomial c) 9 =
    coef (D.lazard_detcritical_target_polynomial c) 9.
Proof.
have two_not0 : (2%:R : F) <> 0.
  move=> htwo; move: two_neq0; by rewrite htwo eqxx.
have five_not0 : (5%:R : F) <> 0.
  move=> hfive; move: five_neq0; by rewrite hfive eqxx.
rewrite /D.lazard_detcritical_V_polynomial
  /D.lazard_detcritical_polynomial_value
  /D.lazard_detcritical_target_polynomial
  /D.lazard_detcritical_N_polynomial
  /D.lazard_detcritical_PA0 /D.lazard_detcritical_PA1
  /D.lazard_detcritical_PA2 /D.lazard_detcritical_PA3
  /D.lazard_detcritical_PB0 /D.lazard_detcritical_PB1
  /D.lazard_detcritical_PB2.
lazard_detcritical_expand_powers.
lazard_detcritical_expand_coefficients.
  rewrite /D.lazard_detcritical_A00 /D.lazard_detcritical_A01 /D.lazard_detcritical_A02
    /D.lazard_detcritical_A10 /D.lazard_detcritical_A11 /D.lazard_detcritical_A20
    /D.lazard_detcritical_A30 /D.lazard_detcritical_B00 /D.lazard_detcritical_B01
    /D.lazard_detcritical_B02 /D.lazard_detcritical_B03 /D.lazard_detcritical_B04
    /D.lazard_detcritical_B10 /D.lazard_detcritical_B11 /D.lazard_detcritical_B12
    /D.lazard_detcritical_B20 /D.lazard_detcritical_B21 /D.lazard_detcritical_B22
    /DM.lazard_det_certificate_N3 /DM.lazard_det_certificate_N6.
finish_lazard_detcritical_coefficient_field.
Qed.

End Coefficient9.

Print Assumptions lazard_detcritical_coefficient_9.

End PolynomialFormulasLazardQuinticDeterminantCriticalCoefficient9.
