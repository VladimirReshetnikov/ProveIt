import OAI.Combinatorics.Progressions.Estimates.StepOneSymbolLinearPart

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def stepOneGradedFrequency (η : L →ₗ[ℚ] ℚ) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  η.comp (F.stepOneGradedEquiv b ω hlayers).symm.toLinearEquiv.toLinearMap

@[simp] theorem stepOneGradedFrequency_equiv (η : L →ₗ[ℚ] ℚ) (x : L) :
    F.stepOneGradedFrequency b ω hlayers η (F.stepOneGradedEquiv b ω hlayers x) = η x := by
  change η ((F.stepOneGradedEquiv b ω hlayers).symm (F.stepOneGradedEquiv b ω hlayers x)) = _
  rw [LieEquiv.symm_apply_apply]

noncomputable def stepOneGradedKernel (η : L →ₗ[ℚ] ℚ) : LieSubalgebra ℚ F.AssociatedGraded :=
  F.associatedGradedFiltration.stepOneFrequencyKernel (F.stepOneGradedFrequency b ω hlayers η)

theorem mem_stepOneGradedKernel (η : L →ₗ[ℚ] ℚ) (x : F.AssociatedGraded) :
    x ∈ F.stepOneGradedKernel b ω hlayers η ↔ F.stepOneGradedFrequency b ω hlayers η x = 0 := Iff.rfl

theorem stepOneGradedKernel_span {κ : Type*} (η : L →ₗ[ℚ] ℚ) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = (F.stepOneFrequencyKernel η).toSubmodule) :
    Submodule.span ℚ (Set.range (fun i => F.stepOneGradedEquiv b ω hlayers (v i))) =
      (F.stepOneGradedKernel b ω hlayers η).toSubmodule := by
  have hmap : (F.stepOneFrequencyKernel η).toSubmodule.map
      (F.stepOneGradedEquiv b ω hlayers).toLinearEquiv.toLinearMap =
      (F.stepOneGradedKernel b ω hlayers η).toSubmodule := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change F.stepOneGradedFrequency b ω hlayers η (F.stepOneGradedEquiv b ω hlayers x) = 0
      rw [F.stepOneGradedFrequency_equiv]
      exact hx
    · intro hy
      refine ⟨(F.stepOneGradedEquiv b ω hlayers).symm y, hy, ?_⟩
      exact (F.stepOneGradedEquiv b ω hlayers).apply_symm_apply y
  calc
    _ = (Submodule.span ℚ (Set.range v)).map
        (F.stepOneGradedEquiv b ω hlayers).toLinearEquiv.toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = _ := by rw [hv, hmap]

theorem stepOne_gradedPieceProjection_mem_kernel (η : L →ₗ[ℚ] ℚ) (j : ℕ)
    {x : L} (hx : x ∈ F.stepOneFrequencyKernel η) :
    F.gradedPieceProjection b ω hlayers j x ∈ F.stepOneGradedKernel b ω hlayers η := by
  rw [F.stepOne_gradedPieceProjection]
  split_ifs
  · change F.stepOneGradedFrequency b ω hlayers η (F.stepOneGradedEquiv b ω hlayers x) = 0
    rw [F.stepOneGradedFrequency_equiv]
    exact hx
  · exact (F.stepOneGradedKernel b ω hlayers η).zero_mem

theorem stepOne_symbol_values_in_gradedKernel (η : L →ₗ[ℚ] ℚ)
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ t : σ → ℝ, eval₂ t p ∈ realificationLieSubalgebra (F.stepOneFrequencyKernel η)) :
    ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realSymbolOfPolynomial b ω hlayers w p)) ∈
        realificationLieSubalgebra (F.stepOneGradedKernel b ω hlayers η) := by
  have hc := (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (F.stepOneFrequencyKernel η)).toSubmodule p).mp hp
  apply (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (F.stepOneGradedKernel b ω hlayers η)).toSubmodule _).mpr
  intro α
  rw [F.realGradedSymbolPolynomial_coefficient_of_polynomial]
  exact baseChange_mem_of_mapsTo (F.stepOneFrequencyKernel η).toSubmodule
    (F.stepOneGradedKernel b ω hlayers η).toSubmodule
    (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α))
    (fun _ hx => F.stepOne_gradedPieceProjection_mem_kernel b ω hlayers η _ hx) (hc α)

end Erdos3.NilpotentLieFiltration

end

end OAI
