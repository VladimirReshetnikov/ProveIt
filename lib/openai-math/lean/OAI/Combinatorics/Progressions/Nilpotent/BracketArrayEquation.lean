import OAI.Combinatorics.Progressions.Polynomial.PolynomialLiftArrays

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {σ κ ι L : Type*} [Fintype κ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {V : Submodule ℚ L}

theorem liftQuotientArray_neg (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    liftQuotientArray f (fun t => -S t) = -liftQuotientArray f S := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  funext bi
  simp only [coefficients_liftQuotientArray, map_neg, Finsupp.neg_apply, Pi.neg_apply]

theorem liftQuotientArray_norm_bound (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hS : ∀ t, ‖realQuotientCoordinateMap f (coefficients (S t) α)‖ ≤ M) :
    ‖coefficients (liftQuotientArray f S) α‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro bi
  rw [coefficients_liftQuotientArray]
  exact (norm_le_pi_norm (realQuotientCoordinateMap f (coefficients (S bi.1) α)) bi.2).trans (hS bi.1)

theorem liftQuotientArray_grid (f : Basis ι ℚ (L ⧸ V))
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) (l : ℕ)
    (hS : ∀ t, realQuotientCoordinateMap f (coefficients (S t) α) ∈ realDenominatorGrid l) :
    coefficients (liftQuotientArray f S) α ∈ realDenominatorGrid l := by
  classical
  have hex : ∀ t, ∃ z : ι → ℤ,
      (fun i => (z i : ℝ)) = (l : ℝ) • realQuotientCoordinateMap f (coefficients (S t) α) := hS
  choose z hz using hex
  refine ⟨fun bi => z bi.1 bi.2, ?_⟩
  funext bi
  change (z bi.1 bi.2 : ℝ) = (l : ℝ) * coefficients (liftQuotientArray f S) α bi
  rw [coefficients_liftQuotientArray]
  exact congrFun (hz bi.1) bi.2

theorem bracket_array_equation_of_current_relation
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (π : (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] L))
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hcurrent : ∀ t α, ⁅coefficients P α, (1 : ℝ) ⊗ₜ[ℚ] k t⁆ -
      (π (coefficients (S t) α) - π (coefficients (R t) α)) ∈ V.baseChange ℝ) :
    ∀ α, realBracketSystem f k (coefficients P α) =
      coefficients (liftQuotientArray f (fun t => map (π.restrictScalars ℚ)
        (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α +
      coefficients (liftQuotientArray f (fun t => map (π.restrictScalars ℚ)
        (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) α := by
  intro α
  funext bi
  have hi := congrFun ((realQuotientCoordinateMap_eq_zero_iff f _).mpr (hcurrent bi.1 α)) bi.2
  simp only [map_sub, Pi.sub_apply, Pi.zero_apply] at hi
  change realQuotientCoordinateMap f ⁅coefficients P α, (1 : ℝ) ⊗ₜ[ℚ] k bi.1⁆ bi.2 = _
  simp only [Pi.add_apply, coefficients_liftQuotientArray, coefficients_map,
    LinearMap.restrictScalars_apply, map_neg, map_sub, Finsupp.sub_apply,
    Finsupp.neg_apply, Pi.sub_apply, Pi.neg_apply]
  linear_combination hi

end Erdos3

end

end OAI
