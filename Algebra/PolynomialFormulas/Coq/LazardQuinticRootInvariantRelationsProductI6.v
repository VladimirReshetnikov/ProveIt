From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelationsProductsCore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootInvariantRelationsProductI6.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module PC := PolynomialFormulasLazardQuinticRootInvariantRelationsProductsCore.
Local Open Scope ring_scope.

Section ProductI6.

Variable F : fieldType.

Add Ring lazard_root_invariant_relations_product_i6_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Lemma lazard_product_i6_nine_natrE : (9%:R : F) = 8%:R + 1.
Proof. exact: (@natrD F 8 1). Qed.
Lemma lazard_product_i6_twenty_seven_natrE : (27%:R : F) = 26%:R + 1.
Proof. exact: (@natrD F 26 1). Qed.

Ltac finish_product_i6_ring :=
  repeat first
    [ rewrite lazard_product_i6_twenty_seven_natrE
    | rewrite lazard_product_i6_nine_natrE ];
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Theorem lazard_root_invariant_product_i6
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  2%:R * (RP.lazard_root_i4 (RP.lazard_root_invariants roots) *
      RP.lazard_root_i6 (RP.lazard_root_invariants roots)) =
    PC.lazard_twice_i4_mul_i6_rhs (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots).
Proof.
have hx4 := RP.lazard_root_sum_zero_last hsum.
rewrite /PC.lazard_twice_i4_mul_i6_rhs /RP.lazard_depressed_of_roots
  /RP.lazard_root_invariants /RP.lazard_root_orbit_formula
  /RP.lazard_root_esymm2 /RP.lazard_root_esymm3
  /RP.lazard_root_esymm4 /RP.lazard_root_esymm5 hx4 /=.
finish_product_i6_ring.
Qed.

End ProductI6.

End PolynomialFormulasLazardQuinticRootInvariantRelationsProductI6.
