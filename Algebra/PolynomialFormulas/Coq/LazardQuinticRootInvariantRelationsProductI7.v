From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelationsProductsCore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootInvariantRelationsProductI7.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module PC := PolynomialFormulasLazardQuinticRootInvariantRelationsProductsCore.
Local Open Scope ring_scope.

Section ProductI7.

Variable F : fieldType.

Add Ring lazard_root_invariant_relations_product_i7_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_product_i7_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Theorem lazard_root_invariant_product_i7
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  RP.lazard_root_i4 (RP.lazard_root_invariants roots) *
      RP.lazard_root_i7 (RP.lazard_root_invariants roots) =
    PC.lazard_i4_mul_i7_rhs (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots).
Proof.
have hx4 := RP.lazard_root_sum_zero_last hsum.
rewrite /PC.lazard_i4_mul_i7_rhs /RP.lazard_depressed_of_roots
  /RP.lazard_root_invariants /RP.lazard_root_orbit_formula
  /RP.lazard_root_esymm2 /RP.lazard_root_esymm3
  /RP.lazard_root_esymm4 /RP.lazard_root_esymm5 hx4 /=.
finish_product_i7_ring.
Qed.

End ProductI7.

End PolynomialFormulasLazardQuinticRootInvariantRelationsProductI7.
