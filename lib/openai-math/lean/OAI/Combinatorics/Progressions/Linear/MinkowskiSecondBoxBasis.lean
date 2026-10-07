import OAI.Combinatorics.Progressions.Geometry.MinkowskiSecondBox

namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open Module

theorem projectedTail_det_ne_zero {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    (projectedTail h B).det ≠ 0 := by
  intro hq
  have habs := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h B hB
  rw [hq, abs_zero, mul_zero] at habs
  exact hdet (abs_eq_zero.mp habs)

noncomputable def projectedTailBasis {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (projectedTail h B).col
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (projectedTail_det_ne_zero h B hdet hB))
    (by simp)

@[simp] theorem projectedTailBasis_apply {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) (j : Fin n) :
    projectedTailBasis h B hdet hB j = (projectedTail h B).col j := by
  simp [projectedTailBasis]

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
