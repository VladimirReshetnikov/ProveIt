import Mathlib.Analysis.InnerProductSpace.GramMatrix

namespace OAI

section

namespace Erdos3

open Module

theorem gram_det_basis_change {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Basis ι ℝ E) (v : ι → E) :
    (Matrix.gram ℝ v).det = (b.det v) ^ 2 * (Matrix.gram ℝ b).det := by
  classical
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using finrank_eq_card_basis b))
  have hd (w : ι → E) : (Matrix.gram ℝ w).det = (o.toBasis.toMatrix w).det ^ 2 := by
    rw [Matrix.gram_eq_conjTranspose_mul o w, Matrix.det_mul, Matrix.det_conjTranspose]
    have he : o.toBasis.toMatrix w = Matrix.of (fun i j => o.repr (w j) i) := by
      ext i j
      rfl
    rw [he]
    simp [pow_two]
  rw [hd v, hd b, b.det_apply, ← o.toBasis.toMatrix_mul_toMatrix b v, Matrix.det_mul]
  ring

end Erdos3

end

end OAI
