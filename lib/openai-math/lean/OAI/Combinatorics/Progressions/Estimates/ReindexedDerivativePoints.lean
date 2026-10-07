import OAI.Combinatorics.Progressions.Linear.SortedBasisTriangular
import OAI.Combinatorics.Progressions.Sampling.DerivativeGridPoints

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem pi_norm_comp_equiv {ι : Type*} [Fintype ι] (x : ι → ℝ) (e : Equiv.Perm ι) :
    ‖x ∘ e‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact norm_le_pi_norm x (e i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h := norm_le_pi_norm (x ∘ e) (e.symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h

theorem derivativeGridPoint_reindex {σ κ : Type*} [Fintype κ]
    (T : σ → ℝ) (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ))
    (A : Matrix κ κ ℝ) (e : Equiv.Perm κ) (h : σ → ℤ) (r : κ → ℝ) :
    derivativeGridPoint T (scale ∘ e) ((LinearMap.funLeft ℝ ℝ e).comp Y)
      (A.submatrix e e) h (r ∘ e) =
        ((derivativeGridPoint T scale Y A h r).1, (derivativeGridPoint T scale Y A h r).2 ∘ e) := by
  have hm : (A.submatrix e e) *ᵥ (r ∘ e) = (A *ᵥ r) ∘ e := by
    simp only [Matrix.submatrix_mulVec_equiv, Function.comp_def, Equiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · funext i
    change scale (e i) * (Y (fun j => (h j : ℝ)) (e i) - ((A.submatrix e e) *ᵥ (r ∘ e)) i) =
      scale (e i) * (Y (fun j => (h j : ℝ)) (e i) - (A *ᵥ r) (e i))
    rw [hm]
    rfl

theorem derivativeGridPoint_reindex_norm {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ))
    (A : Matrix κ κ ℝ) (e : Equiv.Perm κ) (h : σ → ℤ) (r : κ → ℝ) :
    ‖derivativeGridPoint T (scale ∘ e) ((LinearMap.funLeft ℝ ℝ e).comp Y)
      (A.submatrix e e) h (r ∘ e)‖ = ‖derivativeGridPoint T scale Y A h r‖ := by
  rw [derivativeGridPoint_reindex, Prod.norm_def, Prod.norm_def, pi_norm_comp_equiv]

end Erdos3

end

end OAI
