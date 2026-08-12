From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

From PolynomialFormulas Require Import SexticSparsePolynomials.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseCoefficient0Certificate.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseCoefficient1Certificate.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseCoefficient2Certificate.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseCoefficient3Certificate.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseCoefficient4Certificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCertificates.

Module SP := PolynomialFormulasSexticSparsePolynomials.

Local Open Scope ring_scope.

Module S := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Sparse.

Module P2C := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Common.

Module C0 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCoefficient0Certificate.

Module C1 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCoefficient1Certificate.

Module C2 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCoefficient2Certificate.

Module C3 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCoefficient3Certificate.

Module C4 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCoefficient4Certificate.

Theorem p2_sparse_coefficient01
    {F : fieldType} (roots : 5.-tuple F)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic0 (P2C.lazard_cyclic_p2_numerator_difference roots) =
    lazard_cyclic1 (P2C.lazard_cyclic_p2_numerator_difference roots).
Proof.
have hbridge := S.eval_sparse_p2_numerator_difference (roots := roots) hsum.
have hleft := congrArg lazard_cyclic0 hbridge.
have hright := congrArg lazard_cyclic1 hbridge.
rewrite /S.eval_sparse_cyclic /= in hleft hright.
rewrite -hleft -hright
  C0.p2_sparse_coefficient0_certificate
  C1.p2_sparse_coefficient1_certificate.
reflexivity.
Qed.

Theorem p2_sparse_coefficient12
    {F : fieldType} (roots : 5.-tuple F)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic1 (P2C.lazard_cyclic_p2_numerator_difference roots) =
    lazard_cyclic2 (P2C.lazard_cyclic_p2_numerator_difference roots).
Proof.
have hbridge := S.eval_sparse_p2_numerator_difference (roots := roots) hsum.
have hleft := congrArg lazard_cyclic1 hbridge.
have hright := congrArg lazard_cyclic2 hbridge.
rewrite /S.eval_sparse_cyclic /= in hleft hright.
rewrite -hleft -hright
  C1.p2_sparse_coefficient1_certificate
  C2.p2_sparse_coefficient2_certificate.
reflexivity.
Qed.

Theorem p2_sparse_coefficient23
    {F : fieldType} (roots : 5.-tuple F)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic2 (P2C.lazard_cyclic_p2_numerator_difference roots) =
    lazard_cyclic3 (P2C.lazard_cyclic_p2_numerator_difference roots).
Proof.
have hbridge := S.eval_sparse_p2_numerator_difference (roots := roots) hsum.
have hleft := congrArg lazard_cyclic2 hbridge.
have hright := congrArg lazard_cyclic3 hbridge.
rewrite /S.eval_sparse_cyclic /= in hleft hright.
rewrite -hleft -hright
  C2.p2_sparse_coefficient2_certificate
  C3.p2_sparse_coefficient3_certificate.
reflexivity.
Qed.

Theorem p2_sparse_coefficient34
    {F : fieldType} (roots : 5.-tuple F)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic3 (P2C.lazard_cyclic_p2_numerator_difference roots) =
    lazard_cyclic4 (P2C.lazard_cyclic_p2_numerator_difference roots).
Proof.
have hbridge := S.eval_sparse_p2_numerator_difference (roots := roots) hsum.
have hleft := congrArg lazard_cyclic3 hbridge.
have hright := congrArg lazard_cyclic4 hbridge.
rewrite /S.eval_sparse_cyclic /= in hleft hright.
rewrite -hleft -hright
  C3.p2_sparse_coefficient3_certificate
  C4.p2_sparse_coefficient4_certificate.
reflexivity.
Qed.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCertificates.
