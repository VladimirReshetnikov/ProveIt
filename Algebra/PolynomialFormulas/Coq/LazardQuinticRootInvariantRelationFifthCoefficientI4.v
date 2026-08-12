From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelationFifthData
  LazardQuinticRootInvariantRelationFifthSupport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** [i4]-coefficient shard of the fifth Figure-3 identity. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientI4.

Import GRing.Theory.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module D := PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.
Local Open Scope ring_scope.

Section CoefficientI4.

Variable F : fieldType.

Add Ring lazard_fifth_coefficient_i4_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Theorem lazard_fifth_coefficient_i4 (p q r s : F) :
  D.lazard_fifth_printed_i4 p q r s =
    D.lazard_fifth_reconstructed_i4 p q r s.
Proof.
rewrite /D.lazard_fifth_printed_i4 /D.lazard_fifth_reconstructed_i4
  /D.lazard_fifth_fourth_constant /D.lazard_fifth_fourth_i8
  /D.lazard_fifth_fourth_i7 /D.lazard_fifth_fourth_i6
  /D.lazard_fifth_fourth_i5 /D.lazard_fifth_fourth_i4
  /D.lazard_fifth_product_i8_i4 /D.lazard_fifth_product_i7_i4
  /D.lazard_fifth_product_i6_i4 /D.lazard_fifth_product_i5_i4
  /D.lazard_fifth_square_i4.
lazard_fifth_coefficient_prepare.
match goal with
| |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
end.
ring.
Qed.

End CoefficientI4.

Print Assumptions lazard_fifth_coefficient_i4.

End PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientI4.
