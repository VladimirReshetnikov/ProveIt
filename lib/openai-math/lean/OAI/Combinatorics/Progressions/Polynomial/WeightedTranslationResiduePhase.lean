import OAI.Combinatorics.Progressions.Nilpotent.WeightedTranslationResidueNilmanifold

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem bchRealTranslationHom_rational_residue
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (r : (weightedFiltration w d hwd).Group)
    (hr : bchTranslationHom w d hw hwd r ∈
      (integerTranslationResidueSubgroup M).map PolynomialTranslationGroup.fromInteger) :
    bchRealTranslationHom w d hwd (NilpotentLieBCHGroup.realificationHom r) ∈
      integerPolynomialTranslationResidueCover M := by
  obtain ⟨z, hz, he⟩ := hr
  refine ⟨z, hz, ?_⟩
  rw [bchRealTranslationHom_rational w d hw hwd, ← he]
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change (z.base i : ℝ) = ((z.base i : ℚ) : ℝ)
    simp
  · change MvPolynomial.map (Int.castRingHom ℝ) z.polynomial =
      MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) z.polynomial)
    rw [MvPolynomial.map_map]
    congr 1

theorem realResidueLattice_translation_residue_map
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) {g : (weightedFiltration w d hwd).realification.Group}
    (hg : g ∈ (weightedTranslationResidueLattice w d hw hwd M).map
      NilpotentLieBCHGroup.realificationHom) :
    bchRealTranslationHom w d hwd g ∈ integerPolynomialTranslationResidueCover M := by
  obtain ⟨r, hr, rfl⟩ := hg
  exact bchRealTranslationHom_rational_residue w d hw hwd M r hr

noncomputable def weightedTranslationResidueQuotientMap
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    ((weightedFiltration w d hwd).realification.Group ⧸
      (weightedTranslationResidueLattice w d hw hwd M).map NilpotentLieBCHGroup.realificationHom) →
      (PolynomialTranslationGroupOver ℝ σ ⧸ integerPolynomialTranslationResidueCover M) :=
  Quotient.map (bchRealTranslationHom w d hwd) (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have h := realResidueLattice_translation_residue_map w d hw hwd M
      (QuotientGroup.leftRel_apply.mp hab)
    simpa only [map_mul, map_inv] using h)

@[simp] theorem weightedTranslationResidueQuotientMap_mk
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationResidueQuotientMap w d hw hwd M (QuotientGroup.mk g) =
      QuotientGroup.mk (bchRealTranslationHom w d hwd g) := rfl

section Nilmanifold

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

theorem realResidueLattice_translation_residue
    {g : (weightedFiltration w d hwd).realification.Group}
    (hg : g ∈ (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice) :
    bchRealTranslationHom w d hwd g ∈ integerPolynomialTranslationResidueCover M :=
  realResidueLattice_translation_residue_map w d hw hwd M hg

noncomputable def weightedTranslationResiduePhaseQuotientMap :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space →
      (PolynomialTranslationGroupOver ℝ σ ⧸ integerPolynomialTranslationResidueCover M) :=
  weightedTranslationResidueQuotientMap w d hw hwd M

@[simp] theorem weightedTranslationResiduePhaseQuotientMap_mk
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationResiduePhaseQuotientMap w d hw hwd M hM (QuotientGroup.mk g) =
      QuotientGroup.mk (bchRealTranslationHom w d hwd g) := rfl

end Nilmanifold

end Erdos3.PolynomialTranslationLie

end

end OAI
