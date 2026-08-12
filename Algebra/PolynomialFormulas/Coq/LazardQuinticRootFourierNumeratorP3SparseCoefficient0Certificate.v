From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

From PolynomialFormulas Require Import SexticSparsePolynomials.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3Sparse.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseData.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseCoefficient0Certificate.

Module SP := PolynomialFormulasSexticSparsePolynomials.

Local Open Scope ring_scope.

Module B := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Sparse.

Module S := PolynomialFormulasLazardQuinticRootFourierNumeratorP3Sparse.

Module D := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseData.

(** Intended kernel check of one complete cyclic row.  This whole-row
    [vm_compute] form is retained as an audit target, not as a viable
    production certificate; the manifest records the resource bound. *)
Lemma p3_sparse_coefficient0_certificate :
  B.sparse_cyclic0 S.sparse_p3_numerator_difference =
    D.p3_common_normal.
Proof. vm_compute. Qed.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseCoefficient0Certificate.
