import OAI.Combinatorics.Progressions.Estimates.ObservedTruncationResidual
import OAI.Combinatorics.Progressions.Linear.ProductANOVASectionNormalizedBound
import OAI.Combinatorics.Progressions.Probability.CylinderJointMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productTruncatedGram_bound (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M η : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset I)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ S r x - 1| ≤ η) :
    productANOVAEnergy μ D (fun x => r x * f x) ≤
      2 * M * (FiniteProbabilityWeights.pi μ).mean (fun x => r x * f x) +
        2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  let p := FiniteProbabilityWeights.pi μ
  let h := fun x => r x * f x
  let P := productANOVATruncation μ D h
  let A := productANOVAEnergy μ D h
  let B := M * p.mean h
  let C := (2 : ℝ) ^ b * M * (1 + η)
  let E := η * (D.card : ℝ) ^ 2 * C ^ 2
  have hM : 0 ≤ M := (p.mean_nonneg (fun x => (hf x).1)).trans
    ((p.mean_mono (fun x => (hf x).2)).trans_eq (p.mean_const M))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcap : ∀ S ∈ D, ∀ x, p.weight x ≠ 0 → |productANOVA μ S h x| ≤ C := by
    intro S hS x hx
    have hc := productANOVA_weighted_cap μ r f hr hM hf S
      (fun T hT => hclose T (by
        have := Finset.card_le_card hT
        have := hcard S hS
        omega)) x hx
    have hpw : (2 : ℝ) ^ S.card ≤ (2 : ℝ) ^ b := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) (hcard S hS)
    exact hc.trans (by
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_right hpw (mul_nonneg hM (by linarith : 0 ≤ 1 + η))])
  have herr := productFamily_square_comparison μ r D (fun S => productANOVA μ S h)
    hη hC hcard (fun S _ => productANOVA_depends μ S h) hcap hclose
  change |p.mean (fun x => r x * P x ^ 2) - p.mean (fun x => P x ^ 2)| ≤ E at herr
  have hsquare : p.mean (fun x => P x ^ 2) = A := productANOVAEnergy_square μ D h
  rw [hsquare] at herr
  have hpair : p.mean (fun x => r x * f x * P x) = A :=
    (productANOVAEnergy_pairing μ D h).symm
  have hA : 0 ≤ A := productANOVAEnergy_nonneg μ D h
  have hB : 0 ≤ B := mul_nonneg hM (p.mean_nonneg (fun x => mul_nonneg (hr x) (hf x).1))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hP : 0 ≤ p.mean (fun x => r x * P x ^ 2) :=
    p.mean_nonneg (fun x => mul_nonneg (hr x) (sq_nonneg _))
  have hquad : A ^ 2 ≤ B * (A + E) := by
    have hc := p.density_cauchy_schwarz r f P hr
    rw [hpair] at hc
    apply hc.trans
    apply mul_le_mul (p.density_square_le r f hr hf) _ hP hB
    have hh := (abs_le.mp herr).2
    linarith
  have hbound : A ≤ 2 * B + 2 * E := by
    by_contra hn
    have hpos : 0 < A := by linarith
    have h₁ := mul_nonneg (show 0 ≤ A - 2 * B by linarith) (show 0 ≤ A + E by linarith)
    have h₂ := mul_nonneg hpos.le (show 0 ≤ A - 2 * E by linarith)
    nlinarith [sq_pos_of_pos hpos]
  have htwo : ((2 : ℝ) ^ b) ^ 2 = (4 : ℝ) ^ b := by
    rw [← pow_mul, Nat.mul_comm b 2, pow_mul]
    norm_num
  have hEeq : E = η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
    dsimp [E, C]
    rw [mul_pow, mul_pow, htwo]
    ring
  calc
    _ ≤ 2 * B + 2 * E := hbound
    _ = _ := by rw [hEeq]; dsimp [B, h, p]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSection_truncatedGram_bound (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (rho f : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    {M η : ℝ} (hM : 0 ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ rho η (2 * b + A.card)) :
    productANOVAEnergy μ D (productSectionAverage μ T A z (fun x => rho x * f x)) ≤
      2 * M * (FiniteProbabilityWeights.pi μ).mean
        (productSectionAverage μ T A z (fun x => rho x * f x)) +
      2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  have hc : ProductMarginalsClose μ (productSectionAverage μ T A z rho) η (2 * b) := by
    simpa only [Nat.add_sub_cancel] using
      ProductMarginalsClose.section μ hclose T A hAT (by omega) z hz
  have h := productTruncatedGram_bound μ (productSectionAverage μ T A z rho)
    (productSectionDensityWeight μ T A z rho f)
    (productSectionAverage_nonneg μ T A z rho hrho)
    (fun x => ⟨productSectionDensityWeight_nonneg μ T A z rho f hrho (fun y => (hf y).1) x,
      productSectionDensityWeight_le μ T A z rho f hrho hM hf x⟩) hη D hcard hc
  simpa only [productSectionDensityWeight_mul μ T A z rho f hrho hf] using h

theorem productNormalizedSection_truncatedGram_bound (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (rho f : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    {K M η : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hη : 0 ≤ η) (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ rho η (2 * b + A.card)) :
    productANOVAEnergy μ D (productNormalizedSection μ T A z K (fun x => rho x * f x)) ≤
      2 * M * (FiniteProbabilityWeights.pi μ).mean
        (productNormalizedSection μ T A z K (fun x => rho x * f x)) +
      2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  have hc : ProductMarginalsClose μ (productSectionAverage μ T A z rho) η (2 * b) := by
    simpa only [Nat.add_sub_cancel] using
      ProductMarginalsClose.section μ hclose T A hAT (by omega) z hz
  have h := productTruncatedGram_bound μ (productSectionAverage μ T A z rho)
    (productNormalizedSectionWeight μ T A z K rho f)
    (productSectionAverage_nonneg μ T A z rho hrho)
    (fun x => ⟨productNormalizedSectionWeight_nonneg μ T A z (zero_le_one.trans hK) rho f hrho
      (fun y => (hf y).1) x,
      productNormalizedSectionWeight_le μ T A z hK hM rho f hrho hf x⟩) hη D hcard hc
  simpa only [← productNormalizedSection_weighted_eq μ T A z K rho f hrho hf] using h

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_truncatedGram_bound (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (w : Ω → ℝ) {M η : ℝ} (hM : 0 ≤ M)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b)) :
    productANOVAEnergy μ D (observedProductDensity μ p F w) ≤
      2 * M * p.mean w + 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w M hM hw
  have h := productTruncatedGram_bound μ (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (by intro z; norm_num)) hf hη D hcard hclose
  rw [← he, observedProductDensity_mean μ p F hμ w base] at h
  exact h

theorem observedProductDensity_section_truncatedGram_bound
    (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (w : Ω → ℝ) {M η : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card)) :
    productANOVAEnergy μ D (productSectionAverage μ T A z (observedProductDensity μ p F w)) ≤
      2 * M * (FiniteProbabilityWeights.pi μ).mean
        (productSectionAverage μ T A z (observedProductDensity μ p F w)) +
      2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w M hM hw
  rw [he]
  exact productSection_truncatedGram_bound μ T A hAT z hz
    (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (by intro x; norm_num)) hM hf hη D hcard hclose

theorem observedProductDensity_small_mass_energy (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (w : Ω → ℝ) {η τ : ℝ}
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hη : 0 ≤ η) (hmass : p.mean w ≤ τ)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ) :
    productANOVAEnergy μ D (observedProductDensity μ p F w) ≤ 3 * τ := by
  have h := observedProductDensity_truncatedGram_bound μ p F hμ base w zero_le_one hw hη D hcard hclose
  norm_num only [one_pow, mul_one] at h
  linarith

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSection_truncatedGram_uniform (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (rho f : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    {M η : ℝ} (hM : 0 ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ rho η (2 * b + A.card)) :
    productANOVAEnergy μ D (productSectionAverage μ T A z (fun x => rho x * f x)) ≤
      2 * M ^ 2 * (1 + η) +
        2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  have hc := ProductMarginalsClose.section μ hclose T A hAT (by omega) z hz
  have hmean := hc ∅ (by simp) z hz
  rw [productConditionalMean_empty] at hmean
  have hmass : (FiniteProbabilityWeights.pi μ).mean
      (productSectionAverage μ T A z (fun x => rho x * f x)) ≤ M * (1 + η) := by
    calc
      _ ≤ (FiniteProbabilityWeights.pi μ).mean (fun x => M * productSectionAverage μ T A z rho x) :=
        (FiniteProbabilityWeights.pi μ).mean_mono
          (fun x => (productSectionAverage_weighted_cap μ T A z rho f hrho hf x).2)
      _ = M * (FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ T A z rho) :=
        (FiniteProbabilityWeights.pi μ).mean_const_mul M _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hmean).2]) hM
  have h := productSection_truncatedGram_bound μ T A hAT z hz rho f hrho hM hf hη D hcard hclose
  nlinarith [mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)]

theorem observedProductDensity_section_norm_uniform {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (w : Ω → ℝ) {M η : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card)) :
    Real.sqrt (productANOVAEnergy μ D (productSectionAverage μ T A z (observedProductDensity μ p F w))) ≤
      Real.sqrt (2 * M ^ 2 * (1 + η) +
        2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2) := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w M hM hw
  rw [he]
  apply Real.sqrt_le_sqrt
  exact productSection_truncatedGram_uniform μ T A hAT z hz
    (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (by intro x; norm_num)) hM hf hη D hcard hclose

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_truncation_sqrt_le (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
      Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  calc
    _ = Real.sqrt (productCouplingPairing c (productANOVATruncation μ D w)
        (productANOVATruncation ν D f) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (productANOVAEnergy μ D w * productANOVAEnergy ν D f) :=
      Real.sqrt_le_sqrt (productCouplingPairing_truncation_sq_le c D w f)
    _ = _ := Real.sqrt_mul (productANOVAEnergy_nonneg μ D w) _

theorem productCouplingPairing_truncation_small_energy (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) {τ N : ℝ}
    (hw : productANOVAEnergy μ D w ≤ 3 * τ)
    (hf : Real.sqrt (productANOVAEnergy ν D f) ≤ N) :
    |productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
      Real.sqrt (3 * τ) * N := by
  apply (productCouplingPairing_truncation_sqrt_le c D w f).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hw) hf (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem observedProductDensity_small_mass_pairing {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (hμ : ∀ i x, 0 < (μ i).weight x) (base : ∀ i, X i) (w : Ω → ℝ)
    {η τ N : ℝ} (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hη : 0 ≤ η) (hmass : p.mean w ≤ τ)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (f : (∀ i, Y i) → ℝ) (hf : Real.sqrt (productANOVAEnergy ν D f) ≤ N) :
    |productCouplingPairing c (productANOVATruncation μ D (observedProductDensity μ p F w))
      (productANOVATruncation ν D f)| ≤ Real.sqrt (3 * τ) * N :=
  productCouplingPairing_truncation_small_energy c D _ f
    (observedProductDensity_small_mass_energy μ p F hμ base w hw hη hmass D hcard hclose herr) hf

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_section_norm_le_three (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (T A : Finset ι) (hAT : A ⊆ T) (z : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy μ D
      (productSectionAverage μ T A z (observedProductDensity μ p F w))) ≤ 3 := by
  have h := observedProductDensity_section_norm_uniform μ p F T A hAT z hz w
    zero_le_one hw hη0 D hcard hclose
  simp only [one_pow, mul_one] at h
  apply h.trans
  calc
    _ ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by linarith)
    _ = 3 := by norm_num

theorem observedProductDensity_scaled_section_norm (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) {scale cap : ℝ}
    (hscale : 0 < scale) (hcap : scale⁻¹ ≤ cap)
    (T A : Finset ι) (hAT : A ⊆ T) (z : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy μ D
      (fun y => scale⁻¹ * productSectionAverage μ T A z (observedProductDensity μ p F w) y)) ≤ 3 * cap := by
  rw [sqrt_productANOVAEnergy_smul, abs_of_nonneg (inv_nonneg.mpr hscale.le)]
  have h := observedProductDensity_section_norm_le_three μ p F w hw T A hAT z hz
    hη0 hη1 D hcard hclose herr
  calc
    _ ≤ scale⁻¹ * 3 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hscale.le)
    _ ≤ 3 * cap := by nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem observed_unit_truncation_control {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (hμ : ∀ i x, 0 < (μ i).weight x) (base : ∀ i, X i)
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (D : Finset (Finset ι))
    {b : ℕ} {eta : ℝ} (heta : 0 ≤ eta) (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) eta (2 * b)) :
    let P := productANOVATruncation μ D (observedProductDensity μ p F w)
    let cap := (D.card : ℝ) * (2 : ℝ) ^ b * (1 + eta)
    p.mean (fun z => P (F z) ^ 2) ≤ 2 + 3 * eta * cap ^ 2 ∧
    p.mean (fun z => (w z - P (F z)) ^ 2) ≤ 1 + eta * cap ^ 2 ∧
    ∀ (I : Finset ι), I.card ≤ b → (∀ S ⊆ I, S ∈ D) →
      ∀ a : (∀ i, X i) → ℝ, ProductDependsOn I a →
        |p.mean (fun z => (w z - P (F z)) * a (F z))| ≤
          eta * cap * (FiniteProbabilityWeights.pi μ).mean (fun x => |a x|) := by
  intro P cap
  let C := (2 : ℝ) ^ b * (1 + eta)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcap (S) (hS : S ∈ D) (x) (_hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
      |productANOVA μ S (observedProductDensity μ p F w) x| ≤ C := by
    have h := observedProductDensity_component_cap μ p F hμ w zero_le_one heta hw
      (ProductMarginalsClose.mono μ hclose (by omega : b ≤ 2 * b)) S (hcard S hS) x
    simpa only [mul_one] using h
  have hsquare := observed_truncation_square_error μ p F hμ w D heta hC hcard hcap hclose
  have hres := observed_truncation_residual_square μ p F hμ w D heta hC hcard hcap hclose
  have hgram := observedProductDensity_truncatedGram_bound μ p F hμ base w zero_le_one hw heta D hcard hclose
  norm_num only [one_pow, mul_one, mul_one] at hgram
  have hpow : ((2 : ℝ) ^ b) ^ 2 = (4 : ℝ) ^ b := by
    rw [← pow_mul, Nat.mul_comm b 2, pow_mul]
    norm_num
  have heq : eta * (D.card : ℝ) ^ 2 * C ^ 2 = eta * cap ^ 2 := by
    dsimp only [C, cap]
    ring
  have heqGram : 2 * eta * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + eta) ^ 2 = 2 * eta * cap ^ 2 := by
    dsimp only [cap]
    simp only [mul_pow, hpow]
    ring
  rw [heq] at hsquare hres
  rw [heqGram] at hgram
  have hwmean : p.mean w ≤ 1 := (p.mean_mono (fun z => (hw z).2)).trans_eq (p.mean_const 1)
  have hwsq : p.mean (fun z => w z ^ 2) ≤ 1 := by
    apply (p.mean_mono (g := fun _ => 1) ?_).trans_eq (p.mean_const 1)
    intro z
    have h := hw z
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have he := (abs_le.mp hsquare).2
    change p.mean (fun z => P (F z) ^ 2) ≤ _
    change p.mean (fun z => P (F z) ^ 2) - _ ≤ _ at he
    linarith
  · linarith
  · intro I hI hDI a ha
    have ht := observed_truncation_local_test_error μ p F hμ w D heta hcard hcap hclose I hI hDI a ha
    apply ht.trans_eq
    dsimp only [cap, C]
    ring

end Erdos3

end

end OAI
