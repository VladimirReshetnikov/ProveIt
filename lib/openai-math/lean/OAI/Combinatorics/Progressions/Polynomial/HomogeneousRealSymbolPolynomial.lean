import OAI.Combinatorics.Progressions.Estimates.HomogeneousRealSymbolPullback

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct
attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolHomogeneousPullback realSymbolOfGradedPolynomial realSymbolOfPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)

theorem realSymbolOfPolynomial_homogeneousChart
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    F.realSymbolOfPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolHomogeneousPullback b ω hF w v β
        (F.realSymbolOfPolynomial b ω hF w p) := by
  classical
  apply ((F.polynomialSymbolBasis b ω hF v).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfPolynomial_coordinate, realSymbolHomogeneousPullback,
    F.realSymbolOfGradedPolynomial_coordinate]
  rw [coefficients_realChartSubstitute, coefficients_realChartSubstitute]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr_of_eq_on_inter
  · intro γ hγ hγ'
    have hz : coefficients (F.realGradedSymbolPolynomial b ω hF w
        (F.realSymbolOfPolynomial b ω hF w p)) γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · have he := F.realGradedSymbolPolynomial_coordinate b ω hF w
        (F.realSymbolOfPolynomial b ω hF w p) ⟨(γ, z.val.2), h⟩
      rw [hz, map_zero, Finsupp.zero_apply, F.realSymbolOfPolynomial_coordinate] at he
      rw [← he, mul_zero]
    · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _
        (fun he => h (he.symm.trans z.property)), zero_mul]
  · intro γ hγ hγ'
    have hz : coefficients p γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfPolynomial_coordinate, hz, map_zero, Finsupp.zero_apply, mul_zero]
    · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ γ z.val.2 h, mul_zero]
  · intro γ hγ hγ'
    have hz := z.property
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfPolynomial_coordinate]
    · have ha : Finsupp.weight v z.val.1 ≠ Finsupp.weight w γ :=
        fun he => h (he.symm.trans hz)
      rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _ ha]
      simp only [zero_mul]

theorem realPolynomialSymbolHom_homogeneousChart
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (h : (F.realification.adaptedPolynomialFiltration v).Group)
    (hlog : (h.coord : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) :
    F.realPolynomialSymbolHom b ω hF v h =
      F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
        (F.realPolynomialSymbolHom b ω hF w g) := by
  apply NilpotentLieBCHGroup.ext
  change F.realSymbolOfPolynomial b ω hF v (h.coord : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
    F.realSymbolHomogeneousPullback b ω hF w v β
      (F.realSymbolOfPolynomial b ω hF w (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  rw [hlog]
  exact F.realSymbolOfPolynomial_homogeneousChart b ω hF w v β hβ _

end Erdos3.NilpotentLieFiltration

end

end OAI
