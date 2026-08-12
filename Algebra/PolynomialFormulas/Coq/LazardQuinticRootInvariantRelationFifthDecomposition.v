From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelations
  LazardQuinticRootInvariantRelationFifthData
  LazardQuinticRootInvariantRelationFifthSupport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Linear decompositions of the six previously proved right sides used by
    the fifth certificate.  Each proof only regroups one displayed formula. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationFifthDecomposition.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module IR := PolynomialFormulasLazardQuinticRootInvariantRelations.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module D := PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.
Local Open Scope ring_scope.

Section Decomposition.

Variable F : fieldType.

Add Ring lazard_fifth_decomposition_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_decomposition :=
  lazard_fifth_coefficient_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_fifth_fourth_rhsE
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  IR.lazard_i4_fourth_rhs c i =
    D.lazard_fifth_fourth_i8 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c) *
      RP.lazard_root_i8 i +
    D.lazard_fifth_fourth_i7 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c) *
      RP.lazard_root_i7 i +
    D.lazard_fifth_fourth_i6 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c) *
      RP.lazard_root_i6 i +
    D.lazard_fifth_fourth_i5 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c) *
      RP.lazard_root_i5 i +
    D.lazard_fifth_fourth_i4 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c) *
      RP.lazard_root_i4 i +
    D.lazard_fifth_fourth_constant (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c).
Proof.
rewrite /IR.lazard_i4_fourth_rhs
  /D.lazard_fifth_fourth_i8 /D.lazard_fifth_fourth_i7
  /D.lazard_fifth_fourth_i6 /D.lazard_fifth_fourth_i5
  /D.lazard_fifth_fourth_i4 /D.lazard_fifth_fourth_constant.
finish_decomposition.
Qed.

Lemma lazard_fifth_square_rhsE
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  IR.lazard_i4_square_rhs c i =
    (@D.lazard_fifth_square_i8 F) *
      RP.lazard_root_i8 i +
    (@D.lazard_fifth_square_i7 F) *
      RP.lazard_root_i7 i +
    D.lazard_fifth_square_i6 (RP.lazard_root_p c) *
      RP.lazard_root_i6 i +
    D.lazard_fifth_square_i5 (RP.lazard_root_q c) *
      RP.lazard_root_i5 i +
    D.lazard_fifth_square_i4 (RP.lazard_root_p c) *
      RP.lazard_root_i4 i +
    D.lazard_fifth_square_constant (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c).
Proof.
rewrite /IR.lazard_i4_square_rhs
  /D.lazard_fifth_square_i8 /D.lazard_fifth_square_i7
  /D.lazard_fifth_square_i6 /D.lazard_fifth_square_i5
  /D.lazard_fifth_square_i4 /D.lazard_fifth_square_constant.
finish_decomposition.
Qed.

Lemma lazard_fifth_product_i5_rhsE
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  IR.lazard_i4_mul_i5_rhs c i =
    (@D.lazard_fifth_product_i5_i8 F) *
      RP.lazard_root_i8 i +
    D.lazard_fifth_product_i5_i7 (RP.lazard_root_p c) *
      RP.lazard_root_i7 i +
    D.lazard_fifth_product_i5_i6 (RP.lazard_root_q c) *
      RP.lazard_root_i6 i +
    D.lazard_fifth_product_i5_i5 (RP.lazard_root_r c) *
      RP.lazard_root_i5 i +
    D.lazard_fifth_product_i5_i4 (RP.lazard_root_p c)
      (RP.lazard_root_q c) *
      RP.lazard_root_i4 i +
    D.lazard_fifth_product_i5_constant (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c).
Proof.
rewrite /IR.lazard_i4_mul_i5_rhs
  /D.lazard_fifth_product_i5_i8 /D.lazard_fifth_product_i5_i7
  /D.lazard_fifth_product_i5_i6 /D.lazard_fifth_product_i5_i5
  /D.lazard_fifth_product_i5_i4 /D.lazard_fifth_product_i5_constant.
finish_decomposition.
Qed.

Lemma lazard_fifth_product_i6_rhsE
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  IR.lazard_twice_i4_mul_i6_rhs c i =
    D.lazard_fifth_product_i6_i8 (RP.lazard_root_p c) *
      RP.lazard_root_i8 i +
    D.lazard_fifth_product_i6_i7 (RP.lazard_root_q c) *
      RP.lazard_root_i7 i +
    D.lazard_fifth_product_i6_i6 (RP.lazard_root_p c)
      (RP.lazard_root_r c) *
      RP.lazard_root_i6 i +
    D.lazard_fifth_product_i6_i5 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_s c) *
      RP.lazard_root_i5 i +
    D.lazard_fifth_product_i6_i4 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) *
      RP.lazard_root_i4 i +
    D.lazard_fifth_product_i6_constant (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c).
Proof.
rewrite /IR.lazard_twice_i4_mul_i6_rhs
  /D.lazard_fifth_product_i6_i8 /D.lazard_fifth_product_i6_i7
  /D.lazard_fifth_product_i6_i6 /D.lazard_fifth_product_i6_i5
  /D.lazard_fifth_product_i6_i4 /D.lazard_fifth_product_i6_constant.
finish_decomposition.
Qed.

Lemma lazard_fifth_product_i7_rhsE
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  IR.lazard_i4_mul_i7_rhs c i =
    D.lazard_fifth_product_i7_i8 (RP.lazard_root_q c) *
      RP.lazard_root_i8 i +
    D.lazard_fifth_product_i7_i7 (RP.lazard_root_r c) *
      RP.lazard_root_i7 i +
    D.lazard_fifth_product_i7_i6 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_s c) *
      RP.lazard_root_i6 i +
    D.lazard_fifth_product_i7_i5 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) *
      RP.lazard_root_i5 i +
    D.lazard_fifth_product_i7_i4 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c) *
      RP.lazard_root_i4 i +
    D.lazard_fifth_product_i7_constant (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c).
Proof.
rewrite /IR.lazard_i4_mul_i7_rhs
  /D.lazard_fifth_product_i7_i8 /D.lazard_fifth_product_i7_i7
  /D.lazard_fifth_product_i7_i6 /D.lazard_fifth_product_i7_i5
  /D.lazard_fifth_product_i7_i4 /D.lazard_fifth_product_i7_constant.
finish_decomposition.
Qed.

Lemma lazard_fifth_product_i8_rhsE
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  IR.lazard_twice_i4_mul_i8_rhs c i =
    D.lazard_fifth_product_i8_i8 (RP.lazard_root_p c)
      (RP.lazard_root_r c) *
      RP.lazard_root_i8 i +
    D.lazard_fifth_product_i8_i7 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_s c) *
      RP.lazard_root_i7 i +
    D.lazard_fifth_product_i8_i6 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) *
      RP.lazard_root_i6 i +
    D.lazard_fifth_product_i8_i5 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c) *
      RP.lazard_root_i5 i +
    D.lazard_fifth_product_i8_i4 (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c) *
      RP.lazard_root_i4 i +
    D.lazard_fifth_product_i8_constant (RP.lazard_root_p c)
      (RP.lazard_root_q c) (RP.lazard_root_r c) (RP.lazard_root_s c).
Proof.
rewrite /IR.lazard_twice_i4_mul_i8_rhs
  /D.lazard_fifth_product_i8_i8 /D.lazard_fifth_product_i8_i7
  /D.lazard_fifth_product_i8_i6 /D.lazard_fifth_product_i8_i5
  /D.lazard_fifth_product_i8_i4 /D.lazard_fifth_product_i8_constant.
finish_decomposition.
Qed.

End Decomposition.

Print Assumptions lazard_fifth_fourth_rhsE.
Print Assumptions lazard_fifth_square_rhsE.
Print Assumptions lazard_fifth_product_i5_rhsE.
Print Assumptions lazard_fifth_product_i6_rhsE.
Print Assumptions lazard_fifth_product_i7_rhsE.
Print Assumptions lazard_fifth_product_i8_rhsE.

End PolynomialFormulasLazardQuinticRootInvariantRelationFifthDecomposition.
