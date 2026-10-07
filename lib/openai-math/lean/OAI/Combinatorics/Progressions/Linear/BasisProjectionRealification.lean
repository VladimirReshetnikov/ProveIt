import OAI.Combinatorics.Progressions.Estimates.RealifiedMultidegree
import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

theorem basisCoordinateProjection_baseChange (b : Basis ι ℚ V) (S : Set ι) :
    (basisCoordinateProjection b S).baseChange ℝ = basisCoordinateProjection (b.baseChange ℝ) S := by
  classical
  apply (b.baseChange ℝ).ext
  intro i
  rw [basisCoordinateProjection_basis, Basis.baseChange_apply, LinearMap.baseChange_tmul,
    basisCoordinateProjection_basis]
  split_ifs <;> simp only [TensorProduct.tmul_zero]

theorem BasisGradedSubmodule.baseChange (b : Basis ι ℚ V) (w : ι → ℕ) (U : Submodule ℚ V)
    (hU : BasisGradedSubmodule b w U) : BasisGradedSubmodule (b.baseChange ℝ) w (U.baseChange ℝ) := by
  intro j x hx
  have hstable : U.baseChange ℝ ≤ (U.baseChange ℝ).comap (basisGradeProjection (b.baseChange ℝ) w j) := by
    conv_lhs => rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    change basisCoordinateProjection (b.baseChange ℝ) {i | w i = j} ((1 : ℝ) ⊗ₜ[ℚ] u) ∈ U.baseChange ℝ
    rw [← basisCoordinateProjection_baseChange, LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (hU j u hu)
  exact hstable hx

end Erdos3

end

end OAI
