From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

From PolynomialFormulas Require Import SexticSparsePolynomials.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseDataPart0.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseDataPart1.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseDataPart2.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseDataPart3.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseDataPart4.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseDataPart5.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseDataPart6.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseDataPart7.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3SparseDataPart8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseData.

Module SP := PolynomialFormulasSexticSparsePolynomials.

Local Open Scope ring_scope.

Module P0 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart0.

Module P1 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart1.

Module P2 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart2.

Module P3 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart3.

Module P4 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart4.

Module P5 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart5.

Module P6 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart6.

Module P7 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart7.

Module P8 := PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart8.

(** The common cyclic coefficient.  The generator independently
    folds the 20,953-term integer numerator modulo [omega^5 = 1]. *)
Definition p3_common_normal : SP.sparse_polynomial :=
  P0.p3_common_part0 ++
    P1.p3_common_part1 ++
    P2.p3_common_part2 ++
    P3.p3_common_part3 ++
    P4.p3_common_part4 ++
    P5.p3_common_part5 ++
    P6.p3_common_part6 ++
    P7.p3_common_part7 ++
    P8.p3_common_part8.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseData.
