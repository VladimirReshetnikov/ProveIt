import OAI.Combinatorics.Progressions.Estimates.NormalizedSiteSections

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem observedProductDensity_scaled_section_low_degree {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [LinearOrder ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    {scale cap η P : ℝ} (hscale : 0 < scale) (hcap : 0 ≤ cap) (hinv : scale⁻¹ ≤ cap)
    {r q k : ℕ} (hq : 2 ≤ q) (heven : Even q)
    (T A : Finset ι) (hAT : A ⊆ T) (hAr : A.card ≤ r) (hk : k ≤ r - A.card)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (hη : 0 ≤ η) (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + cap) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + cap)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (normalizedObservedDensity μ p F w scale) 1 r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (fun y => scale⁻¹ * productSectionAverage μ T A z (observedProductDensity μ p F w) y)) ≤
        (16 * (P + 2)) ^ (2 * k) := by
  obtain ⟨f, hf, he⟩ := normalizedObservedDensity_factor μ p F w hw scale hscale
  have hF : ∀ x, 0 ≤ f x ∧ f x ≤ cap := fun x => ⟨(hf x).1, (hf x).2.trans hinv⟩
  have hb : ProductBoundedMarginals μ
      (fun x => observedProductDensity μ p F (fun _ => 1) x * f x) 1 r := by
    rw [← he]
    exact hbound
  have h := approxProduct_low_degree_normalized_section μ r q k hq heven T A hAT hAr hk z hz
    (K := 1) le_rfl hcap hη hrP hlog hPq hqP hsmall
    (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (fun _ => zero_le_one)) hF hclose hb
  rw [← he] at h
  have hn : productNormalizedSection μ T A z (1 : ℝ) (normalizedObservedDensity μ p F w scale) =
      (fun y => scale⁻¹ * productSectionAverage μ T A z (observedProductDensity μ p F w) y) := by
    funext y
    simp only [productNormalizedSection, one_pow, inv_one, one_mul]
    exact productSectionAverage_smul μ T A z scale⁻¹ (observedProductDensity μ p F w) y
  rw [hn] at h
  have hc : (8 : ℝ) * (1 + 1) * (P + 2) = 16 * (P + 2) := by ring
  rw [hc] at h
  exact h

end Erdos3

end

end OAI
