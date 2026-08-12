From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The first Figure-3 identity, isolated so its reflective certificate is
    checked independently of the four Figure-2 product identities. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationsSquare.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Local Open Scope ring_scope.

Section Square.

Variable F : fieldType.

Definition lazard_i4_square_rhs
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  5%:R * RP.lazard_root_i8 i -
    2%:R * RP.lazard_root_p c * RP.lazard_root_i6 i +
    4%:R * RP.lazard_root_q c * RP.lazard_root_i5 i -
    2%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_i4 i -
    6%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c +
    2%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 +
    10%:R * RP.lazard_root_q c * RP.lazard_root_s c +
    4%:R * RP.lazard_root_r c ^+ 2.

Add Ring lazard_root_invariant_relations_square_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_invariant_relations_square_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Theorem lazard_root_invariants_square
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  RP.lazard_root_i4 (RP.lazard_root_invariants roots) ^+ 2 =
    lazard_i4_square_rhs (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots).
Proof.
have hx4 := RP.lazard_root_sum_zero_last hsum.
rewrite /lazard_i4_square_rhs /RP.lazard_depressed_of_roots
  /RP.lazard_root_invariants /RP.lazard_root_orbit_formula
  /RP.lazard_root_esymm2 /RP.lazard_root_esymm3
  /RP.lazard_root_esymm4 /RP.lazard_root_esymm5 hx4 /=.
finish_lazard_root_invariant_relations_square_ring.
Qed.

End Square.

End PolynomialFormulasLazardQuinticRootInvariantRelationsSquare.
