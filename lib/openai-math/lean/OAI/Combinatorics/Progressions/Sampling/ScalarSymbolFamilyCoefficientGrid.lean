import OAI.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι J L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
  (w : σ → ℕ)

theorem scalarSymbolPolynomial_family_rational_coefficients [Fintype ι] [Fintype J]
    (θ : J → F.AssociatedGraded →ₗ[ℚ] ℚ) (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g)
    (j : J) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun j i => θ j (F.associatedGradedBasis b ω hF i)) * m)
      (F.scalarSymbolPolynomial b ω hF w (θ j) g) := by
  classical
  let ℓ : F.AssociatedGraded →ₗ[ℚ] (J → ℚ) := LinearMap.pi θ
  have h : ∀ α : σ →₀ ℕ, ∃ z : J → ℤ,
      (fun j => (z j : ℝ)) =
        ((matrixDenominator (fun j i => θ j (F.associatedGradedBasis b ω hF i)) * m : ℕ) : ℝ) •
          realifyCoordinateMap ℓ
            (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) := by
    intro α
    exact realifyCoordinateMap_grid (F.associatedGradedBasis b ω hF) ℓ m _
      (F.realGradedSymbolPolynomial_rational_coordinates b ω hF w m g hg α)
  choose z hz using h
  refine ⟨fun α => z α j, funext fun α => ?_⟩
  change (z α j : ℝ) =
    ((matrixDenominator (fun j i => θ j (F.associatedGradedBasis b ω hF i)) * m : ℕ) : ℝ) *
      (F.scalarSymbolPolynomial b ω hF w (θ j) g).coeff α
  rw [F.coeff_scalarSymbolPolynomial]
  have hθ : (LinearMap.proj j).comp ℓ = θ j := by ext; rfl
  have hα := congrFun (hz α) j
  change (z α j : ℝ) = _ * realifyFunctional ((LinearMap.proj j).comp ℓ) _ at hα
  rwa [hθ] at hα

theorem scalarSymbolPolynomial_family_exists_coefficient_grid [Fintype ι] [Fintype J]
    (θ : J → F.AssociatedGraded →ₗ[ℚ] ℚ) {H : ℕ}
    (hθ : ∀ j i, RationalHeightLE (θ j (F.associatedGradedBasis b ω hF i)) H)
    (m : ℕ) (hm : 0 < m) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolRationalGrid b ω hF w m g) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ (Fintype.card J * Fintype.card ι) * m ∧
      ∀ j, realPolynomialCoefficientGrid q (F.scalarSymbolPolynomial b ω hF w (θ j) g) := by
  refine ⟨_, Nat.mul_pos (matrixDenominator_pos _) hm,
    Nat.mul_le_mul_right m (matrixDenominator_le _ hθ), ?_⟩
  exact F.scalarSymbolPolynomial_family_rational_coefficients b ω hF w θ m g hg

theorem scalarSymbolPolynomial_family_slow_coefficients_of_height [Fintype ι]
    (θ : J → F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) {H : ℕ}
    (hθ : ∀ j i, RationalHeightLE (θ j (F.associatedGradedBasis b ω hF i)) H)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (j : J) (α : σ →₀ ℕ) :
    |(F.scalarSymbolPolynomial b ω hF w (θ j) g).coeff α| ≤
      (Fintype.card ι : ℝ) * H * M / monomialScale T α :=
  F.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF w (θ j) T hT hM
    (hθ j) g hg α

end Erdos3.NilpotentLieFiltration

end

end OAI
