import OAI.Combinatorics.Progressions.Linear.SharedFreeCommonProjection

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

theorem affine_refined_coefficient_mem {L ι : Type*} [AddCommGroup L] [Module ℚ L]
    [Fintype ι] {s : ℕ} (C D : Fin s → Submodule ℚ L)
    (K : Fin s → Submodule ℚ (Fin 4 → L))
    (G : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (α : Fin s → ℝ ⊗[ℚ] L) (β : ι → Fin s → ℝ ⊗[ℚ] L) (x : ι → ℝ)
    (hG : ∀ d : Fin s, coefficients G (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (C d) (D d) (K d)).map (LinearMap.proj 0)).baseChange ℝ)
    (hα : ∀ d, α d ∈ (D d).baseChange ℝ)
    (hβ : ∀ j d, β j d ∈ (D d).baseChange ℝ) (d : Fin s) :
    coefficients (G + positiveUnivariate (fun d => α d + ∑ j, x j • β j d))
        (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (C d) (D d) (K d)).map (LinearMap.proj 0)).baseChange ℝ := by
  rw [map_add, Finsupp.add_apply, positiveUnivariate_coefficient]
  apply Submodule.add_mem _ (hG d)
  apply Submodule.baseChange_mono ℝ (dependent_le_refined_firstProjection (C d) (D d) (K d))
  exact Submodule.add_mem _ (hα d)
    (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hβ j d)))

end Erdos3.VectorPolynomial

end

end OAI
