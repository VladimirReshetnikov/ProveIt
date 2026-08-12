From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticRootFourierNumeratorP2Common
  LazardQuinticRootFourierNumeratorP2Coeff01
  LazardQuinticRootFourierNumeratorP2Coeff12
  LazardQuinticRootFourierNumeratorP2Coeff23
  LazardQuinticRootFourierNumeratorP2Coeff34.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP2Core.
Import PolynomialFormulasLazardQuinticRootProjections.
Module Common := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Common.
Module C01 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Coeff01.
Module C12 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Coeff12.
Module C23 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Coeff23.
Module C34 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Coeff34.

Section RootFourierNumeratorP2Core.
Variable F : fieldType.

Theorem lazard_cyclic_p2_numerator_difference_coefficients_equal
    (roots : 5.-tuple F) (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic0 (Common.lazard_cyclic_p2_numerator_difference roots) =
      lazard_cyclic1 (Common.lazard_cyclic_p2_numerator_difference roots) /\
  lazard_cyclic1 (Common.lazard_cyclic_p2_numerator_difference roots) =
      lazard_cyclic2 (Common.lazard_cyclic_p2_numerator_difference roots) /\
  lazard_cyclic2 (Common.lazard_cyclic_p2_numerator_difference roots) =
      lazard_cyclic3 (Common.lazard_cyclic_p2_numerator_difference roots) /\
  lazard_cyclic3 (Common.lazard_cyclic_p2_numerator_difference roots) =
      lazard_cyclic4 (Common.lazard_cyclic_p2_numerator_difference roots).
Proof.
repeat split.
- exact: (C01.lazard_cyclic_p2_numerator_difference_coefficient01
    (roots := roots) (hsum := hsum)).
- exact: (C12.lazard_cyclic_p2_numerator_difference_coefficient12
    (roots := roots) (hsum := hsum)).
- exact: (C23.lazard_cyclic_p2_numerator_difference_coefficient23
    (roots := roots) (hsum := hsum)).
- exact: (C34.lazard_cyclic_p2_numerator_difference_coefficient34
    (roots := roots) (hsum := hsum)).
Qed.

End RootFourierNumeratorP2Core.
End PolynomialFormulasLazardQuinticRootFourierNumeratorP2Core.
