import OAI.Combinatorics.Progressions.Geometry.RestrictedChartPrefixControl

namespace OAI

section

namespace Erdos3
open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem realChartSubstitute_mem_gradedPolynomialSubmodule
    {σ τ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
    [IsScalarTower ℚ ℝ V] (b : Basis ι ℝ V) (ω : ι → ℕ)
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : VectorPolynomial σ ℚ V) (hp : p ∈ gradedPolynomialSubmodule b ω w) :
    realChartSubstitute β p ∈ gradedPolynomialSubmodule b ω v := by
  classical
  intro α
  change basisGradeProjection b ω (Finsupp.weight v α)
    (coefficients (realChartSubstitute β p) α) = _
  rw [coefficients_realChartSubstitute, map_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [map_smul]
  by_cases h : Finsupp.weight v α = Finsupp.weight w γ
  · rw [h]
    exact congrArg (fun z =>
      (MvPolynomial.aeval β (MvPolynomial.monomial γ (1 : ℝ))).coeff α • z) (hp γ)
  · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero α h,
      zero_smul, zero_smul]

namespace NilpotentLieFiltration
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)

noncomputable def realSymbolHomogeneousPullback (x : F.RealPolynomialSymbol w) :
    F.RealPolynomialSymbol v :=
  F.realSymbolOfGradedPolynomial b ω hF v
    (realChartSubstitute β (F.realGradedSymbolPolynomial b ω hF w x))

attribute [local irreducible] realSymbolHomogeneousPullback realSymbolOfGradedPolynomial
  realChartSubstitute realGradedSymbolPolynomial gradedPolynomialSubmodule

theorem realGradedSymbolPolynomial_homogeneousPullback
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) (x : F.RealPolynomialSymbol w) :
    F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v β x) =
    realChartSubstitute β (F.realGradedSymbolPolynomial b ω hF w x) := by
  have hp := F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule b ω hF w x
  have hsub := realChartSubstitute_mem_gradedPolynomialSubmodule
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w v β hβ
    (F.realGradedSymbolPolynomial b ω hF w x) hp
  rw [realSymbolHomogeneousPullback]
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF v
    (realChartSubstitute β (F.realGradedSymbolPolynomial b ω hF w x)) hsub

theorem realSymbolGradeEvaluation_homogeneousPullback
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (x : F.RealPolynomialSymbol w) (j : ℕ) (u : τ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF v j u
      (F.realSymbolHomogeneousPullback b ω hF w v β x) =
    F.realSymbolGradeEvaluation b ω hF w j (fun i => MvPolynomial.eval u (β i)) x := by
  rw [F.realSymbolGradeEvaluation_eq_projection,
    F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
    eval₂_realChartSubstitute, F.realSymbolGradeEvaluation_eq_projection]

theorem homogeneousPullback_quotient_mem_of_restricted_grade_values
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (x : F.RealPolynomialSymbol w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t x ∈ realificationLieSubalgebra U) :
    F.realSymbolGradeQuotientHom v k
      ⟨F.realSymbolHomogeneousPullback b ω hF w v β x⟩ ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
        (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) := by
  exact F.realSymbolGradeQuotient_mem_of_restricted_path b ω hF w v U K β hK x
    ⟨F.realSymbolHomogeneousPullback b ω hF w v β x⟩ k hx
    (fun u j _ => F.realSymbolGradeEvaluation_homogeneousPullback b ω hF w v β hβ x j u)

noncomputable def realSymbolHomogeneousPullbackLie
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol v where
  toFun := F.realSymbolHomogeneousPullback b ω hF w v β
  map_add' x y := by
    apply F.realGradedSymbolPolynomial_injective b ω hF v
    simp only [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
      map_add]
  map_smul' r x := by
    apply F.realGradedSymbolPolynomial_injective b ω hF v
    simp only [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
      map_smul, RingHom.id_apply]
  map_lie' {x y} := by
    apply F.realGradedSymbolPolynomial_injective b ω hF v
    simp only [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
      LieHom.map_lie, realChartSubstitute_lie]

noncomputable def realSymbolHomogeneousPullbackHom
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    F.RealPolynomialSymbolGroup w →* F.RealPolynomialSymbolGroup v :=
  NilpotentLieBCHGroup.map (F.realSymbolHomogeneousPullbackLie b ω hF w v β hβ)

@[simp] theorem realSymbolHomogeneousPullbackHom_coord
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (x : F.RealPolynomialSymbolGroup w) :
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ x).coord =
      F.realSymbolHomogeneousPullback b ω hF w v β x.coord := rfl

theorem homogeneousPullback_residual_quotient_mem
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : LieSubalgebra ℚ F.AssociatedGraded) (K : Set (σ → ℝ))
    (hK : ∀ u : τ → ℝ, (fun i => MvPolynomial.eval u (β i)) ∈ K)
    (E Z R : F.RealPolynomialSymbolGroup w) (k : ℕ)
    (hx : ∀ t ∈ K, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈
        realificationLieSubalgebra U) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
    F.realSymbolGradeQuotientHom v k ((pull E)⁻¹ * pull Z * (pull R)⁻¹) ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot v)
        (F.symbolPointwiseSubalgebra b ω hF v U)).map (F.realSymbolGradeQuotientHom v k) := by
  dsimp only
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
  exact F.homogeneousPullback_quotient_mem_of_restricted_grade_values
    b ω hF w v β hβ U K hK (E⁻¹ * Z * R⁻¹).coord k hx

end NilpotentLieFiltration
end Erdos3

end

end OAI
