import OAI.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial MvPolynomial

variable {σ τ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartHom

theorem realPolynomialGroupMap_weightedAdaptedRealChartHom
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialGroupMap G φ hφ v (F.weightedAdaptedRealChartHom w v β hβ g) =
      G.weightedAdaptedRealChartHom w v β hβ (F.realPolynomialGroupMap G φ hφ w g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [realPolynomialGroupMap_log, weightedAdaptedRealChartHom_coord]
  exact (realChartSubstitute_map β (realificationLieHom φ).toLinearMap _).symm

theorem realPolynomialGroupMap_weightedAdaptedRealChartHom_comp
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (F.realPolynomialGroupMap G φ hφ v).comp (F.weightedAdaptedRealChartHom w v β hβ) =
      (G.weightedAdaptedRealChartHom w v β hβ).comp (F.realPolynomialGroupMap G φ hφ w) := by
  apply MonoidHom.ext
  intro g
  exact F.realPolynomialGroupMap_weightedAdaptedRealChartHom G φ hφ w v β hβ g

end Erdos3.NilpotentLieFiltration

end

end OAI
