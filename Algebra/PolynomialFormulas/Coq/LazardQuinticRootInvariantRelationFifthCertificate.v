From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticRootInvariantRelations
  LazardQuinticRootInvariantRelationFifthData
  LazardQuinticRootInvariantRelationFifthSupport
  LazardQuinticRootInvariantRelationFifthDecomposition
  LazardQuinticRootInvariantRelationFifthCoefficientI8
  LazardQuinticRootInvariantRelationFifthCoefficientI7
  LazardQuinticRootInvariantRelationFifthCoefficientI6
  LazardQuinticRootInvariantRelationFifthCoefficientI5
  LazardQuinticRootInvariantRelationFifthCoefficientI4
  LazardQuinticRootInvariantRelationFifthCoefficientConstant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Proof-light assembly of the six scalar coefficient shards. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationFifthCertificate.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module IR := PolynomialFormulasLazardQuinticRootInvariantRelations.
Module D := PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.
Module S := PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.
Module E := PolynomialFormulasLazardQuinticRootInvariantRelationFifthDecomposition.
Module C8 := PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientI8.
Module C7 := PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientI7.
Module C6 := PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientI6.
Module C5 := PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientI5.
Module C4 := PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientI4.
Module C0 := PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientConstant.
Local Open Scope ring_scope.

Section Certificate.

Variable F : fieldType.

Theorem lazard_i4_fifth_residual_certificate
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  2%:R * RP.lazard_root_i4 i ^+ 5 -
      D.lazard_fifth_printed_numerator
        (RP.lazard_root_p c) (RP.lazard_root_q c)
        (RP.lazard_root_r c) (RP.lazard_root_s c)
        (RP.lazard_root_i4 i) (RP.lazard_root_i5 i)
        (RP.lazard_root_i6 i) (RP.lazard_root_i7 i)
        (RP.lazard_root_i8 i) =
    2%:R * RP.lazard_root_i4 i *
      (RP.lazard_root_i4 i ^+ 4 - IR.lazard_i4_fourth_rhs c i) +
    D.lazard_fifth_fourth_i8
      (RP.lazard_root_p c) (RP.lazard_root_q c)
      (RP.lazard_root_r c) (RP.lazard_root_s c) *
      (2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i8 i) -
        IR.lazard_twice_i4_mul_i8_rhs c i) +
    2%:R * D.lazard_fifth_fourth_i7
      (RP.lazard_root_p c) (RP.lazard_root_q c)
      (RP.lazard_root_r c) (RP.lazard_root_s c) *
      (RP.lazard_root_i4 i * RP.lazard_root_i7 i -
        IR.lazard_i4_mul_i7_rhs c i) +
    D.lazard_fifth_fourth_i6
      (RP.lazard_root_p c) (RP.lazard_root_q c)
      (RP.lazard_root_r c) (RP.lazard_root_s c) *
      (2%:R * (RP.lazard_root_i4 i * RP.lazard_root_i6 i) -
        IR.lazard_twice_i4_mul_i6_rhs c i) +
    2%:R * D.lazard_fifth_fourth_i5
      (RP.lazard_root_p c) (RP.lazard_root_q c)
      (RP.lazard_root_r c) (RP.lazard_root_s c) *
      (RP.lazard_root_i4 i * RP.lazard_root_i5 i -
        IR.lazard_i4_mul_i5_rhs c i) +
    2%:R * D.lazard_fifth_fourth_i4
      (RP.lazard_root_p c) (RP.lazard_root_q c)
      (RP.lazard_root_r c) (RP.lazard_root_s c) *
      (RP.lazard_root_i4 i ^+ 2 - IR.lazard_i4_square_rhs c i).
Proof.
rewrite E.lazard_fifth_fourth_rhsE E.lazard_fifth_product_i8_rhsE
  E.lazard_fifth_product_i7_rhsE E.lazard_fifth_product_i6_rhsE
  E.lazard_fifth_product_i5_rhsE E.lazard_fifth_square_rhsE
  /D.lazard_fifth_printed_numerator.
apply: S.lazard_fifth_linear_residual.
- exact: C8.lazard_fifth_coefficient_i8.
- exact: C7.lazard_fifth_coefficient_i7.
- exact: C6.lazard_fifth_coefficient_i6.
- exact: C5.lazard_fifth_coefficient_i5.
- exact: C4.lazard_fifth_coefficient_i4.
- exact: C0.lazard_fifth_coefficient_constant.
Qed.

End Certificate.

Print Assumptions lazard_i4_fifth_residual_certificate.

End PolynomialFormulasLazardQuinticRootInvariantRelationFifthCertificate.
