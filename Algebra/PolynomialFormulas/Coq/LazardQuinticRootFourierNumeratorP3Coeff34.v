From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticRootFourierNumeratorP3Common
  LazardQuinticRootFourierNumeratorP3SparseCertificates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP3Coeff34.

Import PolynomialFormulasLazardQuinticRootProjections.
Module P3C := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Common.
Module SC := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseCertificates.

Section RootFourierNumeratorP3Coeff34.
Variable F : fieldType.

Lemma lazard_cyclic_p3_numerator_difference_coefficient34
    (roots : 5.-tuple F) (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic3 (P3C.lazard_cyclic_p3_numerator_difference roots) =
    lazard_cyclic4 (P3C.lazard_cyclic_p3_numerator_difference roots).
Proof.
exact: SC.p3_sparse_coefficient34.
Qed.

End RootFourierNumeratorP3Coeff34.
End PolynomialFormulasLazardQuinticRootFourierNumeratorP3Coeff34.
