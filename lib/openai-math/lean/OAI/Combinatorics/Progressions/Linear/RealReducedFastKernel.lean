import OAI.Combinatorics.Progressions.Estimates.ReducedNativeFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
  (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem reducedSquareRealFastRelative_lie_eq_zero (hw : ∀ i, 0 < w i)
    {v z : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hv : v ∈ (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ)
    (hz : z ∈ (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ) :
    ⁅v, z⁆ = 0 := by
  have h := lie_mem_real_baseChange (F.reducedSquareFastRelativeSubmodule w W)
    (F.reducedSquareFastRelativeSubmodule w W) ⊥
    (fun a ha b hb => (Submodule.mem_bot ℚ).mpr
      (F.reducedSquareFastRelative_lie_eq_zero w W hw ha hb)) hv hz
  simpa only [Submodule.baseChange_bot, Submodule.mem_bot] using h

theorem reducedSquareRealFastRelative_action_mem (hw : ∀ i, 0 < w i)
    {u : ℝ ⊗[ℚ] F.quotientTop.PolynomialSymbol w}
    (hu : u ∈ realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w W))
    {v : ℝ ⊗[ℚ] F.squareFiltration.quotientTop.PolynomialSymbol w}
    (hv : v ∈ (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ) :
    ⁅(F.reducedSquareDiagonalSymbolMap w).toLinearMap.baseChange ℝ u, v⁆ ∈
      (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ := by
  let P := (F.reducedSquareFastDiagonalSubalgebra w W).toSubmodule
  let K := F.reducedSquareFastRelativeSubmodule w W
  let d := (F.reducedSquareDiagonalSymbolMap w).toLinearMap
  have hu' : d.baseChange ℝ u ∈ (P.map d).baseChange ℝ := by
    rw [realification_map]
    exact ⟨u, hu, rfl⟩
  have hclosed : ∀ x ∈ P.map d, ∀ y ∈ K, ⁅x, y⁆ ∈ K := by
    rintro x ⟨y, hy, rfl⟩ z hz
    exact F.reducedSquareFastRelative_action_mem w W hw hy hz
  exact lie_mem_real_baseChange (P.map d) K K hclosed hu' hv

end Erdos3.NilpotentLieFiltration

end

end OAI
