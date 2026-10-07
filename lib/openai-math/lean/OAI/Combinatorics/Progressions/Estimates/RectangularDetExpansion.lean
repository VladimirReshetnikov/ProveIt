import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rectangular_det_expansion {I J R : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [CommRing R] (A : Matrix I J R) (B : Matrix J I R) :
    (A*B).det = ∑ p : I → J, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum,
    Fintype.piFinset_univ, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id_eq]
  ring

end Erdos3

end

end OAI
