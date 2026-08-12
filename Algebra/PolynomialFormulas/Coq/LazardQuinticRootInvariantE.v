From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticQuadratic LazardQuinticFourierNumerators
  LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Root reduction of Lazard's displayed invariant E.  This is kept in its
    own certificate module because it is shared by both remaining Fourier
    numerator identities. *)
Module PolynomialFormulasLazardQuinticRootInvariantE.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Local Open Scope ring_scope.

Section RootInvariantE.

Variable F : fieldType.

Add Ring lazard_root_invariant_E_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_invariant_E_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** The coefficient expression [E] evaluated on an ordered depressed root
    tuple is the negative sum of the two cyclic-product squares. *)
Theorem lazard_root_invariant_E_eq
    (roots : 5.-tuple F) (hsum : lazard_root_esymm1 roots = 0) :
  lazard_invariant_E (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots) =
    Q.lazard_root_E roots.
Proof.
have hx4 := lazard_root_sum_zero_last hsum.
rewrite /lazard_invariant_E /lazard_depressed_of_roots
  /lazard_root_invariants /lazard_root_orbit_formula
  /lazard_root_esymm2 /lazard_root_esymm3 /lazard_root_esymm4
  /lazard_root_esymm5 /Q.lazard_root_E
  /RR.lazard_root_T_prime /RR.lazard_root_U_prime hx4 /=.
finish_lazard_root_invariant_E_ring.
Qed.

End RootInvariantE.

End PolynomialFormulasLazardQuinticRootInvariantE.
