From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

From PolynomialFormulas Require Import SexticSparsePolynomials.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart0.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart1.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart2.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart3.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart4.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart5.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart6.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart7.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart8.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP2SparseDataPart9.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseData.

Module SP := PolynomialFormulasSexticSparsePolynomials.

Local Open Scope ring_scope.

Module P0 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart0.

Module P1 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart1.

Module P2 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart2.

Module P3 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart3.

Module P4 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart4.

Module P5 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart5.

Module P6 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart6.

Module P7 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart7.

Module P8 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart8.

Module P9 := PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseDataPart9.

(** The common cyclic coefficient.  The generator independently
    folds the 30,282-term integer numerator modulo [omega^5 = 1]. *)
Definition p2_common_normal : SP.sparse_polynomial :=
  P0.p2_common_part0 ++
    P1.p2_common_part1 ++
    P2.p2_common_part2 ++
    P3.p2_common_part3 ++
    P4.p2_common_part4 ++
    P5.p2_common_part5 ++
    P6.p2_common_part6 ++
    P7.p2_common_part7 ++
    P8.p2_common_part8 ++
    P9.p2_common_part9.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP2SparseData.
