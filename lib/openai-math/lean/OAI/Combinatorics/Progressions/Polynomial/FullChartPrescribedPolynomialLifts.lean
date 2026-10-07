import OAI.Combinatorics.Progressions.Geometry.InhomogeneousFullChartLift
import OAI.Combinatorics.Progressions.Sampling.RationalHomogeneousSymbolPullbackGrid

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] realPolynomialSymbolLift realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom weightedAdaptedRealChartHom realChartSubstitute

variable {s m : ℕ} {X τ ι L : Type} [Fintype X]
  [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]

local notation "wt" => fullTaggedVariableWeight (X := X) J

theorem FullChartControlledFactors.exists_prescribed_full_lifts
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup wt)
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β δ : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (wt i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v (wt i))
    (htop : ∀ i, weightedHomogeneousComponent v (wt i) (δ i) =
      MvPolynomial.aeval β (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i))
    (D : ℕ) (hD : 0 < D) (hgrid : ∀ i, realPolynomialCoefficientGrid D (β i)) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∃ e r : (F.realification.adaptedPolynomialFiltration v).Group,
        F.realPolynomialSymbolHom b ω hF v e =
          F.realSymbolHomogeneousPullbackHom b ω hF wt v β hβ left ∧
        F.realPolynomialSymbolHom b ω hF v r =
          F.realSymbolHomogeneousPullbackHom b ω hF wt v β hβ right ∧
        F.PolynomialRationalGrid b v (q * D ^ s) r ∧
        0 < q * D ^ s ∧
        ∀ {υ : Type*} (u : υ → ℕ) (γ : τ → MvPolynomial υ ℝ)
          (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
          (T : υ → ℝ), (∀ i, 0 < T i) →
          ∀ B : ℝ, 1 ≤ B →
          (∀ i, realPolynomialMass (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ B) →
          F.PolynomialSlowBound b u T
            (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget * B ^ s)
            (F.weightedAdaptedRealChartHom v u γ hγ e) := by
  obtain ⟨P, e, hbound, _, _, hdegree, he, hsymbol⟩ :=
    FullChartControlledFactors.exists_inhomogeneous_left_lift
      F b ω hF J poly N left right h v β δ hβ hδ htop
  obtain ⟨q, hq, hqB, _, _, _, hright⟩ := h
  let R := F.realSymbolHomogeneousPullbackHom b ω hF wt v β hβ right
  have hR : F.SymbolRationalGrid b ω hF v (q * D ^ s) R :=
    F.symbolRationalGrid_homogeneousPullback_rational_of_coefficientGrid b ω hF wt v
      (fullTaggedVariableWeight_pos J) β hβ q D hgrid right hright
  let r := F.realPolynomialSymbolLift b ω hF v R
  have hr : F.PolynomialRationalGrid b v (q * D ^ s) r := by
    unfold PolynomialRationalGrid
    dsimp only [r]
    rw [F.realPolynomialSymbolLift_log]
    exact F.realSymbolRepresentative_rational_coefficients b ω hF v (q * D ^ s) R hR
  refine ⟨q, hq, hqB, e, r, hsymbol, F.realPolynomialSymbolHom_lift b ω hF v R,
    hr, Nat.mul_pos hq (pow_pos hD s), ?_⟩
  intro υ u γ hγ T hT B hB hmass
  exact F.polynomialSlowBound_inhomogeneous_chart_lift b ω hF v u e δ P he γ hγ
    T hT hbound (Real.exp_pos _).le hB hdegree hmass

end Erdos3.NilpotentLieFiltration

end

end OAI
