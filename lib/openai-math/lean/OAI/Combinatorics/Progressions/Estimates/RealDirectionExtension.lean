import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Pi

namespace OAI

section

namespace Erdos3

variable {σ E : Type*} [Fintype σ] [AddCommGroup E] [Module ℚ E] [Module ℝ E]

noncomputable def realDirectionExtension (f : (σ → ℚ) →ₗ[ℚ] E) : (σ → ℝ) →ₗ[ℝ] E := by
  classical
  exact ∑ i, (LinearMap.proj i).smulRight (f (Pi.single i 1))

open scoped Classical in
theorem realDirectionExtension_apply (f : (σ → ℚ) →ₗ[ℚ] E) (h : σ → ℝ) :
    realDirectionExtension f h = ∑ i, h i • f (Pi.single i 1) := by
  classical
  simp only [realDirectionExtension, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]

theorem realDirectionExtension_rat (f : (σ → ℚ) →ₗ[ℚ] E) (h : σ → ℚ) :
    realDirectionExtension f (fun i => (h i : ℝ)) = f h := by
  classical
  rw [realDirectionExtension_apply]
  have he : h = ∑ i, h i • Pi.single i (1 : ℚ) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  exact ratCast_smul_eq ℝ ℚ (h i) _

end Erdos3

end

end OAI
