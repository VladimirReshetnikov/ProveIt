From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

From PolynomialFormulas Require Import SexticSparsePolynomials.
From PolynomialFormulas Require Import LazardQuinticRootFourierNumeratorP3Sparse.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart8.

Module SP := PolynomialFormulasSexticSparsePolynomials.

Local Open Scope ring_scope.

Definition p3_common_part8 : SP.sparse_polynomial := [::
  ((- 2150%:Z), [tuple 13; 2; 2; 1; 0; 0]%N);
  (700%:Z, [tuple 13; 2; 3; 0; 0; 0]%N);
  (3000%:Z, [tuple 13; 3; 0; 2; 0; 0]%N);
  ((- 900%:Z), [tuple 13; 3; 1; 1; 0; 0]%N);
  (1650%:Z, [tuple 13; 3; 2; 0; 0; 0]%N);
  ((- 1300%:Z), [tuple 13; 4; 0; 1; 0; 0]%N);
  ((- 250%:Z), [tuple 13; 4; 1; 0; 0; 0]%N);
  ((- 1500%:Z), [tuple 13; 5; 0; 0; 0; 0]%N);
  ((- 200%:Z), [tuple 14; 0; 0; 4; 0; 0]%N);
  (100%:Z, [tuple 14; 0; 1; 3; 0; 0]%N);
  (100%:Z, [tuple 14; 0; 2; 2; 0; 0]%N);
  ((- 100%:Z), [tuple 14; 1; 1; 2; 0; 0]%N);
  ((- 200%:Z), [tuple 14; 1; 2; 1; 0; 0]%N);
  (400%:Z, [tuple 14; 2; 0; 2; 0; 0]%N);
  ((- 100%:Z), [tuple 14; 2; 1; 1; 0; 0]%N);
  (100%:Z, [tuple 14; 2; 2; 0; 0; 0]%N);
  (100%:Z, [tuple 14; 3; 1; 0; 0; 0]%N);
  ((- 200%:Z), [tuple 14; 4; 0; 0; 0; 0]%N)
].

End PolynomialFormulasLazardQuinticRootFourierNumeratorP3SparseDataPart8.
