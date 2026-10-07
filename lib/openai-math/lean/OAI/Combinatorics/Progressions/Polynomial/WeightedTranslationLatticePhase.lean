import OAI.Combinatorics.Progressions.Nilpotent.WeightedTranslationNilmanifold

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem realLattice_translation_integral
    {g : (weightedFiltration w d hwd).realification.Group}
    (hg : g ∈ (weightedTranslationNilmanifold w d hw hwd).realLattice) :
    bchRealTranslationHom w d hwd g ∈ integerPolynomialTranslationSubgroup := by
  change g ∈ (weightedTranslationLattice w d hwd).map NilpotentLieBCHGroup.realificationHom at hg
  obtain ⟨r,hr,rfl⟩ := hg
  have hi : bchTranslationHom w d hw hwd r ∈ PolynomialTranslationGroup.integralGroup :=
    (bchTranslationHom_mem_integralGroup_iff w d hw hwd r).mpr hr
  obtain ⟨z,hz⟩ := hi
  refine ⟨z,?_⟩
  rw [bchRealTranslationHom_rational w d hw hwd, ← hz]
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change (z.base i : ℝ) = ((z.base i : ℚ) : ℝ)
    simp
  · change MvPolynomial.map (Int.castRingHom ℝ) z.polynomial =
      MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) z.polynomial)
    rw [MvPolynomial.map_map]
    congr 1

noncomputable def weightedTranslationPhaseQuotientMap :
    (weightedTranslationNilmanifold w d hw hwd).Space →
      (PolynomialTranslationGroupOver ℝ σ ⧸ integerPolynomialTranslationSubgroup) :=
  Quotient.map (bchRealTranslationHom w d hwd) (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have h := realLattice_translation_integral w d hw hwd (QuotientGroup.leftRel_apply.mp hab)
    simpa only [map_mul,map_inv] using h)

@[simp] theorem weightedTranslationPhaseQuotientMap_mk
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationPhaseQuotientMap w d hw hwd (QuotientGroup.mk g) =
      QuotientGroup.mk (bchRealTranslationHom w d hwd g) := rfl

noncomputable def weightedTranslationQuotientPhase (D₀ : MvPolynomial σ ℝ) :
    (weightedTranslationNilmanifold w d hw hwd).Space → ℂ :=
  translationQuotientPhase D₀ ∘ weightedTranslationPhaseQuotientMap w d hw hwd

@[simp] theorem weightedTranslationQuotientPhase_mk (D₀ : MvPolynomial σ ℝ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationQuotientPhase w d hw hwd D₀ (QuotientGroup.mk g) =
      translationPhaseFunction D₀ (bchRealTranslationHom w d hwd g) := rfl

theorem weightedTranslationQuotientPhase_norm (D₀ : MvPolynomial σ ℝ)
    (g : (weightedTranslationNilmanifold w d hw hwd).Space) :
    ‖weightedTranslationQuotientPhase w d hw hwd D₀ g‖ = 1 :=
  translationQuotientPhase_norm D₀ _

end Erdos3.PolynomialTranslationLie

end

end OAI
