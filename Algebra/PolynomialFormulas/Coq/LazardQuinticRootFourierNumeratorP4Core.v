From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorP4Common
  LazardQuinticRootFourierNumeratorP4Coeff01
  LazardQuinticRootFourierNumeratorP4Coeff12
  LazardQuinticRootFourierNumeratorP4Coeff23
  LazardQuinticRootFourierNumeratorP4Coeff34.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Assembly of the four independently checked adjacent-coefficient
    certificates underlying Lazard's cleared P4 numerator identity. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP4Core.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticRootFourierNumeratorP4Common.
Module C01 := PolynomialFormulasLazardQuinticRootFourierNumeratorP4Coeff01.
Module C12 := PolynomialFormulasLazardQuinticRootFourierNumeratorP4Coeff12.
Module C23 := PolynomialFormulasLazardQuinticRootFourierNumeratorP4Coeff23.
Module C34 := PolynomialFormulasLazardQuinticRootFourierNumeratorP4Coeff34.
Local Open Scope ring_scope.

Section RootFourierNumeratorP4Core.

Variable F : fieldType.

Theorem lazard_cyclic_p42_difference_coefficients_equal
    (roots : 5.-tuple F) (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic0 (lazard_cyclic_p42_difference roots) =
      lazard_cyclic1 (lazard_cyclic_p42_difference roots) /\
  lazard_cyclic1 (lazard_cyclic_p42_difference roots) =
      lazard_cyclic2 (lazard_cyclic_p42_difference roots) /\
  lazard_cyclic2 (lazard_cyclic_p42_difference roots) =
      lazard_cyclic3 (lazard_cyclic_p42_difference roots) /\
  lazard_cyclic3 (lazard_cyclic_p42_difference roots) =
      lazard_cyclic4 (lazard_cyclic_p42_difference roots).
Proof.
repeat split.
- exact: (C01.lazard_cyclic_p42_difference_coefficient01
    (roots := roots) (hsum := hsum)).
- exact: (C12.lazard_cyclic_p42_difference_coefficient12
    (roots := roots) (hsum := hsum)).
- exact: (C23.lazard_cyclic_p42_difference_coefficient23
    (roots := roots) (hsum := hsum)).
- exact: (C34.lazard_cyclic_p42_difference_coefficient34
    (roots := roots) (hsum := hsum)).
Qed.

End RootFourierNumeratorP4Core.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP4Core.
