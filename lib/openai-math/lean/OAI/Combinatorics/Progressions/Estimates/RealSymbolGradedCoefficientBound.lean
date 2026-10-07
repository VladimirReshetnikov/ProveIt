import OAI.Combinatorics.Progressions.Polynomial.FullChartPolynomialLiftControl

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolHomogeneousPullback

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolSlowBound_iff_gradedCoefficientBound
    (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolSlowBound b ω hF w T M g ↔
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
        (F.realGradedSymbolPolynomialHom b ω hF w g).coord := by
  constructor
  · exact F.realGradedSymbolPolynomial_slow_coefficients b ω hF w T hT hM g
  · exact F.symbolSlowBound_of_gradedPolynomial b ω hF w T M g

theorem realGradedSymbolPolynomialHom_homogeneousPullback
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) :
    F.realGradedSymbolPolynomialHom b ω hF v
      (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g) =
      realPolynomialChartSubstitution F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
        β (F.realGradedSymbolPolynomialHom b ω hF w g) := by
  apply NilpotentLieBCHGroup.ext
  exact F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ g.coord

theorem realGradedSymbolPolynomialHom_homogeneousPullback_coord
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) :
    (F.realGradedSymbolPolynomialHom b ω hF v
      (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g)).coord =
      realChartSubstitute β (F.realGradedSymbolPolynomialHom b ω hF w g).coord := by
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback b ω hF w v β hβ,
    realPolynomialChartSubstitution_coord]

theorem symbolSlowBound_homogeneousPullback_of_coefficientBound
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) (T : τ → ℝ) (M : ℝ)
    (hbound : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
      (realChartSubstitute β (F.realGradedSymbolPolynomialHom b ω hF w g).coord)) :
    F.SymbolSlowBound b ω hF v T M (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g) := by
  apply F.symbolSlowBound_of_gradedPolynomial b ω hF v T M
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback_coord b ω hF w v β hβ]
  exact hbound

theorem realGradedSymbolPolynomialHom_homogeneousPullback_of_chart
    {ν : Type*} (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) (chart : ν → MvPolynomial σ ℝ)
    (E : PolynomialGroup ν F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    (hchart : F.realGradedSymbolPolynomialHom b ω hF w g =
      realPolynomialChartSubstitution F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
        chart E) :
    (F.realGradedSymbolPolynomialHom b ω hF v
      (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g)).coord =
      realChartSubstitute (fun i => MvPolynomial.aeval β (chart i)) E.coord := by
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback_coord b ω hF w v β hβ,
    hchart, realPolynomialChartSubstitution_coord, realChartSubstitute_comp]

theorem FullChartControlledFactors.homogeneousPullback_slow
    {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {m : ℕ} {X : Type} [Fintype X]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (hcontrol : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (fullTaggedVariableWeight (X := X) J i))
    (T : τ → ℝ) (hT : ∀ i, 0 < T i) {B : ℝ} (hB : 1 ≤ B)
    (hmass : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T
      (MvPolynomial.aeval β (normalizedRealPolynomialChart (fun x => (N x : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i))) ≤ B) :
    F.SymbolSlowBound b ω hF v T
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget * B ^ s)
      (F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight (X := X) J)
        v β hβ left) := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_degree_bounded_chart F b ω hF J poly N left right hcontrol
  apply F.symbolSlowBound_of_gradedPolynomial b ω hF v T _
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback_of_chart b ω hF
    (fullTaggedVariableWeight (X := X) J) v β hβ left
    (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly)) E hchart]
  exact CoefficientBound.realChartSubstitute
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) T hT
    (fun i => MvPolynomial.aeval β
      (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly) i))
    hbound (Real.exp_pos budget).le hB hdegree hmass

end Erdos3.NilpotentLieFiltration

end

end OAI
