From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticRootFourierNumeratorP3Common
  LazardQuinticRootFourierNumeratorP3Coeff01
  LazardQuinticRootFourierNumeratorP3Coeff12
  LazardQuinticRootFourierNumeratorP3Coeff23
  LazardQuinticRootFourierNumeratorP3Coeff34.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP3Core.

Import PolynomialFormulasLazardQuinticRootProjections.
Module Common := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Common.
Module C01 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Coeff01.
Module C12 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Coeff12.
Module C23 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Coeff23.
Module C34 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Coeff34.

Section RootFourierNumeratorP3Core.
Variable F : fieldType.

Theorem lazard_cyclic_p3_numerator_difference_coefficients_equal
    (roots : 5.-tuple F) (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic0 (Common.lazard_cyclic_p3_numerator_difference roots) =
      lazard_cyclic1 (Common.lazard_cyclic_p3_numerator_difference roots) /\
  lazard_cyclic1 (Common.lazard_cyclic_p3_numerator_difference roots) =
      lazard_cyclic2 (Common.lazard_cyclic_p3_numerator_difference roots) /\
  lazard_cyclic2 (Common.lazard_cyclic_p3_numerator_difference roots) =
      lazard_cyclic3 (Common.lazard_cyclic_p3_numerator_difference roots) /\
  lazard_cyclic3 (Common.lazard_cyclic_p3_numerator_difference roots) =
      lazard_cyclic4 (Common.lazard_cyclic_p3_numerator_difference roots).
Proof.
repeat split.
- exact: (C01.lazard_cyclic_p3_numerator_difference_coefficient01
    (roots := roots) (hsum := hsum)).
- exact: (C12.lazard_cyclic_p3_numerator_difference_coefficient12
    (roots := roots) (hsum := hsum)).
- exact: (C23.lazard_cyclic_p3_numerator_difference_coefficient23
    (roots := roots) (hsum := hsum)).
- exact: (C34.lazard_cyclic_p3_numerator_difference_coefficient34
    (roots := roots) (hsum := hsum)).
Qed.

End RootFourierNumeratorP3Core.
End PolynomialFormulasLazardQuinticRootFourierNumeratorP3Core.
