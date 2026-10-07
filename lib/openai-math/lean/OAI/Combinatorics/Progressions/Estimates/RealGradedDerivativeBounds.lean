/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDerivativeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realGradedSymbolPolynomial_slow_coefficients (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) (i : ι) :
    |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i| ≤
      M / monomialScale T α := by
  by_cases h : Finsupp.weight w α = ω i
  · have hc := F.realGradedSymbolPolynomial_coordinate b ω hF w g.coord ⟨(α, i), h⟩
    exact (congrArg abs hc).le.trans (hg ⟨(α, i), h⟩)
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord α i h, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realGradedSymbolPolynomial_rational_coefficients (l : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w l g) :
    (fun z : (σ →₀ ℕ) × ι => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) z.1) z.2)
        ∈ realDenominatorGrid l := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => if h : Finsupp.weight w z.1 = ω z.2 then a ⟨z, h⟩ else 0, ?_⟩
  funext z
  change ((if h : Finsupp.weight w z.1 = ω z.2 then a ⟨z, h⟩ else 0 : ℤ) : ℝ) =
    (l : ℝ) * ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) z.1) z.2
  by_cases h : Finsupp.weight w z.1 = ω z.2
  · rw [dite_eq_left h]
    have hc := F.realGradedSymbolPolynomial_coordinate b ω hF w g.coord ⟨z, h⟩
    change ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) z.1) z.2 = _ at hc
    rw [hc]
    exact congrFun ha ⟨z, h⟩
  · rw [dite_eq_right h, Int.cast_zero,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord z.1 z.2 h, mul_zero]

theorem realGradedSymbolPolynomial_derivative_bound [Fintype σ] (hw : ∀ i, 0 < w i)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (h : σ → ℚ) (hh : ∀ i, |(h i : ℝ)| ≤ T i) (α : σ →₀ ℕ) (i : ι) :
    |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (directionalDerivative h
        (F.realGradedSymbolPolynomial b ω hF w g.coord)) α) i| ≤
      (Fintype.card σ : ℝ) * s * M / monomialScale T α := by
  let f := (((F.associatedGradedBasis b ω hF).baseChange ℝ).coord i).restrictScalars ℚ
  have hdegree : ∀ (β : σ →₀ ℕ) (j : σ), s < β j →
      f (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) β) = 0 := by
    intro β j hj
    apply F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord β i
    intro heq
    have hβ := Finsupp.le_weight w (Nat.ne_of_gt (hw j)) β
    have hi := F.adaptedBasis_weight_le_step b ω hF i
    omega
  exact directionalDerivative_scaled_coordinate_bound f
    (F.realGradedSymbolPolynomial b ω hF w g.coord) s hdegree T hT M hM
    (fun β => F.realGradedSymbolPolynomial_slow_coefficients b ω hF w T hT hM g hg β i) h hh α

theorem realGradedSymbolPolynomial_derivative_grid [Fintype σ] (l : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w l g)
    (h : σ → ℤ) :
    (fun z : (σ →₀ ℕ) × ι => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (directionalDerivative (fun j => (h j : ℚ))
        (F.realGradedSymbolPolynomial b ω hF w g.coord)) z.1) z.2)
        ∈ realDenominatorGrid l := by
  classical
  have hgrid := F.realGradedSymbolPolynomial_rational_coefficients b ω hF w l g hg
  obtain ⟨a, ha⟩ := hgrid
  have hcoord (z : (σ →₀ ℕ) × ι) : ∃ n : ℤ, (n : ℝ) = (l : ℝ) *
      ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (coefficients (directionalDerivative (fun j => (h j : ℚ))
          (F.realGradedSymbolPolynomial b ω hF w g.coord)) z.1) z.2 := by
    let f := (((F.associatedGradedBasis b ω hF).baseChange ℝ).coord z.2).restrictScalars ℚ
    exact directionalDerivative_integral_coordinate f
      (F.realGradedSymbolPolynomial b ω hF w g.coord) l
      (fun β => ⟨a (β, z.2), congrFun ha (β, z.2)⟩) h z.1
  choose a ha using hcoord
  exact ⟨a, funext ha⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
