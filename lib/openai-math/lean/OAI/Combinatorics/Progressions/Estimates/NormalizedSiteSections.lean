import OAI.Combinatorics.Progressions.Polynomial.FiniteMarginalLowDegree

namespace OAI

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [LinearOrder ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem normalizedObservedDensity_section_low_degree (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) {scale : ℝ} (hscale : 0 < scale)
    (r q k : ℕ) (hq : 2 ≤ q) (heven : Even q)
    (T A : Finset ι) (hAT : A ⊆ T) (hAr : A.card ≤ r) (hk : k ≤ r - A.card)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    {P η : ℝ} (hη : 0 ≤ η) (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + scale⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + scale⁻¹)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (normalizedObservedDensity μ p F w scale) 1 r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (productSectionAverage μ T A z (normalizedObservedDensity μ p F w scale))) ≤
        (16 * (P + 2)) ^ (2 * k) := by
  obtain ⟨f, hf, he⟩ := normalizedObservedDensity_factor μ p F w hw scale hscale
  have hb : ProductBoundedMarginals μ
      (fun x => observedProductDensity μ p F (fun _ => 1) x * f x) 1 r := by
    rw [← he]
    exact hbound
  have h := approxProduct_low_degree_normalized_section μ r q k hq heven T A hAT hAr hk z hz
    (K := 1) le_rfl (inv_nonneg.mpr hscale.le) hη hrP hlog hPq hqP hsmall
    (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (by intro x; norm_num)) hf hclose hb
  rw [← he] at h
  have hn : productNormalizedSection μ T A z (1 : ℝ) (normalizedObservedDensity μ p F w scale) =
      productSectionAverage μ T A z (normalizedObservedDensity μ p F w scale) := by
    funext x
    simp only [productNormalizedSection, one_pow, inv_one, one_mul]
  rw [hn] at h
  have hc : (8 : ℝ) * (1 + 1) * (P + 2) = 16 * (P + 2) := by ring
  rw [hc] at h
  exact h

theorem normalizedObservedDensity_section_norm (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) {scale : ℝ} (hscale : 0 < scale)
    (T A : Finset ι) (hAT : A ⊆ T) (z : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) {η : ℝ} (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card)) :
    Real.sqrt (productANOVAEnergy μ D
      (productSectionAverage μ T A z (normalizedObservedDensity μ p F w scale))) ≤
      scale⁻¹ * Real.sqrt (2 * (1 + η) + 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2) := by
  have he : productSectionAverage μ T A z (normalizedObservedDensity μ p F w scale) =
      (fun x => scale⁻¹ * productSectionAverage μ T A z (observedProductDensity μ p F w) x) :=
    funext (productSectionAverage_smul μ T A z scale⁻¹ (observedProductDensity μ p F w))
  rw [he, sqrt_productANOVAEnergy_smul, abs_of_nonneg (inv_nonneg.mpr hscale.le)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hscale.le)
  simpa only [one_pow, mul_one] using observedProductDensity_section_norm_uniform μ p F T A hAT z hz
    w zero_le_one hw hη D hcard hclose

end Erdos3

end

end OAI
