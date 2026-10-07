import OAI.Combinatorics.Progressions.Estimates.ObservedUnitTruncation
import OAI.Combinatorics.Progressions.Geometry.ProductMarginalSupport
import OAI.Combinatorics.Progressions.Probability.ProductDensityRepresentative

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteWeightDensity_mean_le {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) :
    p.mean (finiteWeightDensity p w) ≤ ∑ x, w x := by
  unfold FiniteProbabilityWeights.mean
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p.weight x = 0
  · simpa only [hx, zero_mul] using hw x
  · apply le_of_eq
    unfold finiteWeightDensity
    field_simp

theorem zeroLevelGram_bound {s M η : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hcap : s ≤ M * (1 + η)) :
    s ^ 2 ≤ 2 * M * s + 2 * η * M ^ 2 * (1 + η) ^ 2 := by
  by_cases he : η ≤ 1
  · have h2 : s ≤ 2 * M := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right h2 hs
    have herr : 0 ≤ 2 * η * M ^ 2 * (1 + η) ^ 2 := by positivity
    nlinarith
  · have hsq := pow_le_pow_left₀ hs hcap 2
    have hfactor : 1 ≤ 2 * η := by linarith
    have hscaled := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (M * (1 + η)))
    nlinarith [mul_nonneg hM hs]

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem finiteLaw_zero_projection (w f : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    {M η : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (hclose : ∀ x,
      |productFiberMass w ∅ x - productFiberMass (FiniteProbabilityWeights.pi μ).weight ∅ x| ≤
        η * productFiberMass (FiniteProbabilityWeights.pi μ).weight ∅ x) :
    productANOVAEnergy μ (lowDegreeCoordinateSets I 0)
      (finiteWeightDensity (FiniteProbabilityWeights.pi μ) (fun x => w x * f x)) ≤
        2 * M * (∑ x, w x * f x) + 2 * η * M ^ 2 * (1 + η) ^ 2 := by
  let p := FiniteProbabilityWeights.pi μ
  let s := ∑ x, w x * f x
  have hs : 0 ≤ s := Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (hf x).1)
  have hM : 0 ≤ M := (p.mean_nonneg (fun x => (hf x).1)).trans
    ((p.mean_mono (fun x => (hf x).2)).trans_eq (p.mean_const M))
  obtain ⟨x₀, _hx₀⟩ : ∃ x, 0 < p.weight x := by
    by_contra hn
    push Not at hn
    have hsum : (∑ x, p.weight x) ≤ 0 := Finset.sum_nonpos (fun x _ => hn x)
    rw [p.total] at hsum
    norm_num at hsum
  have hmass := hclose x₀
  simp only [productFiberMass_empty, (FiniteProbabilityWeights.pi μ).total, mul_one] at hmass
  have hW : (∑ x, w x) ≤ 1 + η := by
    have hh := (abs_le.mp hmass).2
    linarith
  have hcap : s ≤ M * (1 + η) := by
    calc
      _ ≤ ∑ x, w x * M := Finset.sum_le_sum
        (fun x _ => mul_le_mul_of_nonneg_left (hf x).2 (hw x))
      _ = (∑ x, w x) * M := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + η) * M := mul_le_mul_of_nonneg_right hW hM
      _ = _ := mul_comm _ _
  have hnonneg : 0 ≤ p.mean (finiteWeightDensity p (fun x => w x * f x)) :=
    p.mean_nonneg (finiteWeightDensity_nonneg p _ (fun x => mul_nonneg (hw x) (hf x).1))
  have hmean := finiteWeightDensity_mean_le p (fun x => w x * f x)
    (fun x => mul_nonneg (hw x) (hf x).1)
  rw [productANOVAEnergy_zero]
  exact (pow_le_pow_left₀ hnonneg hmean 2).trans (zeroLevelGram_bound hs hM hη hcap)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem approxProduct_projection_bound (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M η : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (b : ℕ)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ S r x - 1| ≤ η) :
    productANOVAEnergy μ (lowDegreeCoordinateSets I b) (fun x => r x * f x) ≤
      2 * M * (FiniteProbabilityWeights.pi μ).mean (fun x => r x * f x) +
        2 * η * ((∑ j ∈ Finset.range (b + 1), (Fintype.card I).choose j : ℕ) : ℝ) ^ 2 *
          (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  have h := productTruncatedGram_bound μ r f hr hf hη (lowDegreeCoordinateSets I b)
    (fun S hS => (mem_lowDegreeCoordinateSets I b S).mp hS) hclose
  rwa [lowDegreeCoordinateSets_card] at h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem finiteLaw_projection_positive (w f : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    {M η : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η) (b : ℕ) (hb : 0 < b)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      |productFiberMass w S x - productFiberMass (FiniteProbabilityWeights.pi μ).weight S x| ≤
        η * productFiberMass (FiniteProbabilityWeights.pi μ).weight S x) :
    productANOVAEnergy μ (lowDegreeCoordinateSets I b)
      (finiteWeightDensity (FiniteProbabilityWeights.pi μ) (fun x => w x * f x)) ≤
        2 * M * (∑ x, w x * f x) +
          2 * η * ((∑ j ∈ Finset.range (b + 1), (Fintype.card I).choose j : ℕ) : ℝ) ^ 2 *
            (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  let p := FiniteProbabilityWeights.pi μ
  let r := finiteWeightDensity p w
  have hs : ∀ x, p.weight x = 0 → w x = 0 :=
    productLaw_supported_of_singleton_marginals μ w hw
      (fun i => hclose {i} (by simp only [Finset.card_singleton]; omega))
  have hr : ∀ x, p.weight x * r x = w x := finiteWeightDensity_mul p w hs
  have hsf : ∀ x, p.weight x = 0 → w x * f x = 0 := by
    intro x hx
    rw [hs x hx, zero_mul]
  have he : ∀ x, p.weight x * finiteWeightDensity p (fun y => w y * f y) x =
      p.weight x * (r x * f x) := by
    intro x
    rw [finiteWeightDensity_mul p _ hsf, ← mul_assoc, hr]
  rw [productANOVAEnergy_of_weighted_eq μ _ _ he]
  have h := approxProduct_projection_bound μ r f (finiteWeightDensity_nonneg p w hw) hf hη b
    (fun S hS => productConditionalMean_close_of_marginal μ S r w hr (hclose S hS))
  have hmean : (FiniteProbabilityWeights.pi μ).mean (fun x => r x * f x) = ∑ x, w x * f x :=
    mean_finiteWeightDensity p w f hs
  rw [hmean] at h
  exact h

theorem finiteLaw_projection_bound (w f : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    {M η : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η) (b : ℕ)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      |productFiberMass w S x - productFiberMass (FiniteProbabilityWeights.pi μ).weight S x| ≤
        η * productFiberMass (FiniteProbabilityWeights.pi μ).weight S x) :
    productANOVAEnergy μ (lowDegreeCoordinateSets I b)
      (finiteWeightDensity (FiniteProbabilityWeights.pi μ) (fun x => w x * f x)) ≤
        2 * M * (∑ x, w x * f x) +
          2 * η * ((∑ j ∈ Finset.range (b + 1), (Fintype.card I).choose j : ℕ) : ℝ) ^ 2 *
            (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst b
    simpa using finiteLaw_zero_projection μ w f hw hf hη (hclose ∅ (by simp))
  · exact finiteLaw_projection_positive μ w f hw hf hη b hb hclose

theorem finiteLaw_projection_of_density (w f h : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    {M η : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η) (b : ℕ)
    (hdensity : ∀ x, (FiniteProbabilityWeights.pi μ).weight x * h x = w x * f x)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      |productFiberMass w S x - productFiberMass (FiniteProbabilityWeights.pi μ).weight S x| ≤
        η * productFiberMass (FiniteProbabilityWeights.pi μ).weight S x) :
    productANOVAEnergy μ (lowDegreeCoordinateSets I b) h ≤
      2 * M * (∑ x, w x * f x) +
        2 * η * ((∑ j ∈ Finset.range (b + 1), (Fintype.card I).choose j : ℕ) : ℝ) ^ 2 *
          (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  let p := FiniteProbabilityWeights.pi μ
  have hs : ∀ x, p.weight x = 0 → w x * f x = 0 := by
    intro x hx
    have h := hdensity x
    rw [hx, zero_mul] at h
    exact h.symm
  have he : ∀ x, p.weight x * h x = p.weight x * finiteWeightDensity p (fun y => w y * f y) x := by
    intro x
    calc
      _ = w x * f x := hdensity x
      _ = _ := (finiteWeightDensity_mul p _ hs x).symm
  rw [productANOVAEnergy_of_weighted_eq μ _ _ he]
  exact finiteLaw_projection_bound μ w f hw hf hη b hclose

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem marginal_mass_error_of_density {a b η : ℝ} (hb : 0 ≤ b)
    (hzero : b = 0 → a = 0) (hclose : 0 < b → |a / b - 1| ≤ η) :
    |a - b| ≤ η * b := by
  by_cases hz : b = 0
  · rw [hz, hzero hz]
    simp
  · have hp : 0 < b := lt_of_le_of_ne hb (Ne.symm hz)
    have h := hclose hp
    have he : a / b - 1 = (a - b) / b := by field_simp
    rw [he, abs_div, abs_of_pos hp] at h
    exact (div_le_iff₀ hp).mp h

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem finiteProbability_truncated_projection
    (ν : FiniteProbabilityWeights (∀ i, X i)) (f h : (∀ i, X i) → ℝ)
    {M η : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η) (b : ℕ)
    (hdensity : ∀ x, (FiniteProbabilityWeights.pi μ).weight x * h x = ν.weight x * f x)
    (hzero : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      productFiberMass (FiniteProbabilityWeights.pi μ).weight S x = 0 →
        productFiberMass ν.weight S x = 0)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      0 < productFiberMass (FiniteProbabilityWeights.pi μ).weight S x →
        |productFiberMass ν.weight S x /
          productFiberMass (FiniteProbabilityWeights.pi μ).weight S x - 1| ≤ η) :
    productANOVAEnergy μ (lowDegreeCoordinateSets I b) h ≤
      2 * M * ν.mean f +
        2 * η * ((∑ j ∈ Finset.range (b + 1), (Fintype.card I).choose j : ℕ) : ℝ) ^ 2 *
          (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  have h := finiteLaw_projection_of_density μ ν.weight f h ν.nonneg hf hη b hdensity
    (fun S hS x => marginal_mass_error_of_density
      (productFiberMass_nonneg _ (FiniteProbabilityWeights.pi μ).nonneg S x)
      (hzero S hS x) (hclose S hS x))
  simpa only [FiniteProbabilityWeights.mean] using h

end Erdos3

end

end OAI
