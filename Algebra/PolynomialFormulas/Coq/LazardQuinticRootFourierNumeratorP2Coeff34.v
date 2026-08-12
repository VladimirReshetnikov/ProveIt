From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticRootFourierNumeratorP2Common
  LazardQuinticRootFourierNumeratorP2SparseCertificates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP2Coeff34.
Import PolynomialFormulasLazardQuinticRootProjections.
Module P2C := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Common.
Module SC := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCertificates.

Section RootFourierNumeratorP2Coeff34.
Variable F : fieldType.
Lemma lazard_cyclic_p2_numerator_difference_coefficient34
    (roots : 5.-tuple F) (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic3 (P2C.lazard_cyclic_p2_numerator_difference roots) =
    lazard_cyclic4 (P2C.lazard_cyclic_p2_numerator_difference roots).
Proof.
exact: SC.p2_sparse_coefficient34.
Qed.
End RootFourierNumeratorP2Coeff34.
End PolynomialFormulasLazardQuinticRootFourierNumeratorP2Coeff34.
