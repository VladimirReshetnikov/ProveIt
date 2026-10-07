import OAI.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {L ν σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ν] {E : Submodule ℚ L}

theorem bracketSystemLift_injective (e : Basis ν ℚ E) : Function.Injective (bracketSystemLift e) := by
  intro x y h
  apply (e.baseChange ℝ).equivFun.symm.injective
  exact realification_subtype_injective E h

theorem exists_subspace_coordinate_polynomial (e : Basis ν ℚ E)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : ∀ α, coefficients P α ∈ E.baseChange ℝ) :
    ∃ Q : VectorPolynomial σ ℚ (ν → ℝ),
      map ((bracketSystemLift e).restrictScalars ℚ) Q = P ∧
        ∀ α, coefficients P α = 0 → coefficients Q α = 0 := by
  classical
  choose v hv using fun α : σ →₀ ℕ => exists_subspace_basis_coordinates e (coefficients P α) (hP α)
  have hzero (α : σ →₀ ℕ) (hα : coefficients P α = 0) : v α = 0 := by
    apply bracketSystemLift_injective e
    rw [hv, hα, map_zero]
  let C : (σ →₀ ℕ) →₀ (ν → ℝ) := {
    support := (coefficients P).support
    toFun := v
    mem_support_toFun := by
      intro α
      rw [Finsupp.mem_support_iff]
      constructor
      · intro h hα
        apply h
        rw [← hv α, hα, map_zero]
      · intro h hα
        exact h (hzero α hα) }
  let Q : VectorPolynomial σ ℚ (ν → ℝ) := coefficients.symm C
  have hcoeff (α : σ →₀ ℕ) : coefficients Q α = v α := by
    change coefficients (coefficients.symm C) α = v α
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hmap : map ((bracketSystemLift e).restrictScalars ℚ) Q = P := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map]
    change bracketSystemLift e (coefficients Q α) = _
    rw [hcoeff]
    exact hv α
  refine ⟨Q, hmap, ?_⟩
  intro α hα
  rw [hcoeff]
  exact hzero α hα

end Erdos3

end

end OAI
