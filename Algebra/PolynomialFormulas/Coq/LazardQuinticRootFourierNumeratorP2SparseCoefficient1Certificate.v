From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

From PolynomialFormulas Require Import SexticSparsePolynomials.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2Sparse.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseData.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCoefficient1Certificate.

Module SP := PolynomialFormulasSexticSparsePolynomials.

Local Open Scope ring_scope.

Module S := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Sparse.

Module D := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseData.

(** Kernel-checked sparse normalization of one cyclic row. *)
Lemma p2_sparse_coefficient1_certificate :
  S.sparse_cyclic1 S.sparse_p2_numerator_difference =
    D.p2_common_normal.
Proof. vm_compute. Qed.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseCoefficient1Certificate.
