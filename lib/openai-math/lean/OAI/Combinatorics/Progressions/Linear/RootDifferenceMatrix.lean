import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

def rootDifferenceMatrix {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) : Matrix (Unit ⊕ I) (Unit ⊕ J) R :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) (Matrix.of (fun (_ : Unit) j => root j)) (0 : Matrix I Unit R) D

theorem rootDifferenceMatrix_mulVec {I J R : Type*} [Fintype J] [CommRing R]
    (root : J → R) (D : Matrix I J R) (x : R) (v : J → R) :
    rootDifferenceMatrix root D *ᵥ Sum.elim (fun _ : Unit => x) v =
      Sum.elim (fun _ : Unit => x + ∑ j, root j * v j) (D *ᵥ v) := by
  funext i
  cases i with
  | inl i =>
    cases i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rootDifferenceMatrix, Matrix.fromBlocks]
  | inr i => simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, rootDifferenceMatrix, Matrix.fromBlocks]

theorem rootDifferenceMatrix_det {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (root : I → R) (A : Matrix I I R) : (rootDifferenceMatrix root A).det = A.det := by
  change (Matrix.fromBlocks (1 : Matrix Unit Unit R) (Matrix.of (fun (_ : Unit) j => root j))
    (0 : Matrix I Unit R) A).det = A.det
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

theorem rootDifferenceMatrix_submatrix {I J R : Type*} [CommRing R]
    (root : J → R) (D : Matrix I J R) (s : I → J) :
    (rootDifferenceMatrix root D).submatrix id (Sum.map id s) =
      rootDifferenceMatrix (fun i => root (s i)) (D.submatrix id s) := by
  ext i j
  cases i <;> cases j <;> rfl

end Erdos3

end

end OAI
