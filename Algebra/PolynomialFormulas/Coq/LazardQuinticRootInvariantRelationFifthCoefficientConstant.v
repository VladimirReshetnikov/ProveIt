From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelationFifthData
  LazardQuinticRootInvariantRelationFifthSupport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Constant-coefficient shard of the fifth Figure-3 identity.  This is the
    largest shard, but it contains no invariant variables and only the five
    scalar products that contribute to the constant term. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientConstant.

Import GRing.Theory.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module D := PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.
Local Open Scope ring_scope.

Section CoefficientConstant.

Variable F : fieldType.

Add Ring lazard_fifth_coefficient_constant_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Theorem lazard_fifth_coefficient_constant (p q r s : F) :
  D.lazard_fifth_printed_constant p q r s =
    D.lazard_fifth_reconstructed_constant p q r s.
Proof.
rewrite /D.lazard_fifth_printed_constant
  /D.lazard_fifth_reconstructed_constant
  /D.lazard_fifth_fourth_i8 /D.lazard_fifth_fourth_i7
  /D.lazard_fifth_fourth_i6 /D.lazard_fifth_fourth_i5
  /D.lazard_fifth_fourth_i4 /D.lazard_fifth_product_i8_constant
  /D.lazard_fifth_product_i7_constant
  /D.lazard_fifth_product_i6_constant
  /D.lazard_fifth_product_i5_constant
  /D.lazard_fifth_square_constant.
lazard_fifth_coefficient_prepare.
match goal with
| |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
end.
ring.
Qed.

End CoefficientConstant.

Print Assumptions lazard_fifth_coefficient_constant.

End PolynomialFormulasLazardQuinticRootInvariantRelationFifthCoefficientConstant.
