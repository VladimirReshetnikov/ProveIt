import OAI.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
import OAI.Combinatorics.Progressions.FixedDensity.Energy

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingFeature (b t : ℝ) (sigma : Bool) (u : ℝ) : ℝ :=
  1 + (b + if sigma then t else -t) * (u - 1)

noncomputable def countingKernel (b u v : ℝ) : ℝ :=
  1 + b * (u + v - 2) + (2 * b ^ 2 - b) * (u - 1) * (v - 1)

noncomputable def positiveCountingKernel (b u v : ℝ) : ℝ := 1 - b + b * u * v

theorem countingFeature_pair (b t r u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b t sigma u * countingFeature b r sigma v) =
      1 + b * (u + v - 2) + (b ^ 2 + t * r) * (u - 1) * (v - 1) := by
  rw [Fintype.expect_eq_sum_div_card]
  norm_num [countingFeature]
  ring

theorem countingFeature_opposite {b t : ℝ} (ht : t ^ 2 = b * (1 - b)) (u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b t sigma u * countingFeature b (-t) sigma v) =
      countingKernel b u v := by
  have hc : b ^ 2 + t * (-t) = 2 * b ^ 2 - b := by nlinarith
  rw [countingFeature_pair, hc]
  rfl

theorem countingFeature_same {b t : ℝ} (ht : t ^ 2 = b * (1 - b)) (u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b t sigma u * countingFeature b t sigma v) =
      positiveCountingKernel b u v := by
  have hc : b ^ 2 + t * t = b := by nlinarith
  rw [countingFeature_pair, hc]
  unfold positiveCountingKernel
  ring

theorem countingFeature_sqrt_opposite {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b (Real.sqrt (b * (1 - b))) sigma u *
      countingFeature b (-Real.sqrt (b * (1 - b))) sigma v) = countingKernel b u v :=
  countingFeature_opposite (Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hb1))) u v

theorem countingFeature_sqrt_same {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b (Real.sqrt (b * (1 - b))) sigma u *
      countingFeature b (Real.sqrt (b * (1 - b))) sigma v) = positiveCountingKernel b u v :=
  countingFeature_same (Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hb1))) u v

theorem countingKernel_one (u v : ℝ) : countingKernel 1 u v = u * v := by
  unfold countingKernel
  ring

theorem countingKernel_quarter (u v : ℝ) :
    countingKernel (1 / 4) u v = 3 / 8 + (3 / 8) * u + (3 / 8) * v - (1 / 8) * u * v := by
  unfold countingKernel
  ring

theorem positiveCountingKernel_nonneg {b u v : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ positiveCountingKernel b u v :=
  add_nonneg (sub_nonneg.mpr hb1) (mul_nonneg (mul_nonneg hb hu) hv)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingFeatureProduct {I X : Type*} [Fintype I] [DecidableEq I]
    (b t : ℝ) (f : I → X → ℝ) (sigma : I → Bool) (x : X) : ℝ :=
  ∏ i, countingFeature b t (sigma i) (f i x)

noncomputable def countingKernelProductAverage {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] (b : ℝ) (f : I → X → ℝ) (g : I → Y → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, ∏ i, countingKernel b (f i x) (g i y)

noncomputable def positiveKernelGram {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (b : ℝ) (f : I → X → ℝ) : ℝ := 𝔼 x, 𝔼 y, ∏ i, positiveCountingKernel b (f i x) (f i y)

theorem countingFeatureProduct_pair {I X Y : Type*} [Fintype I] [DecidableEq I]
    (b t r : ℝ) (f : I → X → ℝ) (g : I → Y → ℝ) (x : X) (y : Y) :
    (𝔼 sigma : I → Bool, countingFeatureProduct b t f sigma x * countingFeatureProduct b r g sigma y) =
      ∏ i, (𝔼 sigma : Bool, countingFeature b t sigma (f i x) * countingFeature b r sigma (g i y)) := by
  classical
  simp only [countingFeatureProduct, ← Finset.prod_mul_distrib]
  exact (FixedDensity.prod_mean (fun i sigma => countingFeature b t sigma (f i x) *
    countingFeature b r sigma (g i y))).symm

theorem countingFeatureProduct_mean_pair {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] (b t r : ℝ)
    (f : I → X → ℝ) (g : I → Y → ℝ) :
    (𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) *
      (𝔼 y, countingFeatureProduct b r g sigma y)) =
      𝔼 x, 𝔼 y, ∏ i, (𝔼 sigma : Bool,
        countingFeature b t sigma (f i x) * countingFeature b r sigma (g i y)) := by
  simp_rw [Finset.expect_mul_expect]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro y _
  exact countingFeatureProduct_pair b t r f g x y

theorem countingKernelProductAverage_factorization {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] {b t : ℝ} (ht : t ^ 2 = b * (1 - b))
    (f : I → X → ℝ) (g : I → Y → ℝ) :
    countingKernelProductAverage b f g =
      𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) *
        (𝔼 y, countingFeatureProduct b (-t) g sigma y) := by
  simpa only [countingFeature_opposite ht, countingKernelProductAverage] using
    (countingFeatureProduct_mean_pair b t (-t) f g).symm

theorem countingFeatureProduct_square {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {b t : ℝ} (ht : t ^ 2 = b * (1 - b)) (f : I → X → ℝ) :
    (𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) ^ 2) = positiveKernelGram b f := by
  simpa only [pow_two, countingFeature_same ht, positiveKernelGram] using
    countingFeatureProduct_mean_pair b t t f f

theorem positiveKernelGram_nonneg {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (f : I → X → ℝ) : 0 ≤ positiveKernelGram b f := by
  rw [← countingFeatureProduct_square (Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hb1))) f]
  exact Finset.expect_nonneg (fun _ _ => sq_nonneg _)

theorem countingKernelProductAverage_sq_le {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (f : I → X → ℝ) (g : I → Y → ℝ) :
    countingKernelProductAverage b f g ^ 2 ≤ positiveKernelGram b f * positiveKernelGram b g := by
  let t := Real.sqrt (b * (1 - b))
  have ht : t ^ 2 = b * (1 - b) := Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hb1))
  have hnt : (-t) ^ 2 = b * (1 - b) := by simpa only [neg_sq] using ht
  rw [countingKernelProductAverage_factorization ht f g]
  calc
    _ ≤ (𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) ^ 2) *
        (𝔼 sigma : I → Bool, (𝔼 y, countingFeatureProduct b (-t) g sigma y) ^ 2) :=
      Finset.expect_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := by rw [countingFeatureProduct_square ht, countingFeatureProduct_square hnt]

theorem countingKernelProductAverage_abs_le {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] {b A : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (hA : 0 ≤ A)
    (f : I → X → ℝ) (g : I → Y → ℝ)
    (hf : positiveKernelGram b f ≤ A) (hg : positiveKernelGram b g ≤ A) :
    |countingKernelProductAverage b f g| ≤ A := by
  have hsq := (countingKernelProductAverage_sq_le hb hb1 f g).trans
    (mul_le_mul hf hg (positiveKernelGram_nonneg hb hb1 g) hA)
  nlinarith [sq_abs (countingKernelProductAverage b f g), abs_nonneg (countingKernelProductAverage b f g)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingBernoulli {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    FiniteProbabilityWeights Bool where
  weight sigma := if sigma then b else 1 - b
  nonneg sigma := by cases sigma <;> simp <;> linarith
  total := by simp

theorem countingBernoulli_mean {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (u : ℝ) :
    (countingBernoulli hb hb1).mean (fun sigma => if sigma then u else 1) = 1 - b + b * u := by
  simpa [FiniteProbabilityWeights.mean, countingBernoulli] using add_comm (b * u) (1 - b)

theorem countingBernoulli_product {I : Type*} [Fintype I] [DecidableEq I]
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (u : I → ℝ) :
    (FiniteProbabilityWeights.pi (fun _ : I => countingBernoulli hb hb1)).mean
      (fun choice => ∏ i, if choice i then u i else 1) = ∏ i, (1 - b + b * u i) := by
  rw [FiniteProbabilityWeights.mean_pi_product (fun _ : I => countingBernoulli hb hb1)
    (fun i sigma => if sigma then u i else 1)]
  simp only [countingBernoulli_mean]

theorem positiveKernelGram_le_of_boolean_products {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {b A : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (f : I → X → ℝ)
    (h : ∀ choice : I → Bool, (𝔼 x, 𝔼 y, ∏ i, if choice i then f i x * f i y else 1) ≤ A) :
    positiveKernelGram b f ≤ A := by
  classical
  let p := FiniteProbabilityWeights.pi (fun _ : I => countingBernoulli hb hb1)
  have hpoint (x y : X) : (∏ i, positiveCountingKernel b (f i x) (f i y)) =
      p.mean (fun choice => ∏ i, if choice i then f i x * f i y else 1) := by
    simpa only [positiveCountingKernel, mul_assoc] using
      (countingBernoulli_product hb hb1 (fun i => f i x * f i y)).symm
  calc
    positiveKernelGram b f =
        p.mean (fun choice => 𝔼 x, 𝔼 y, ∏ i, if choice i then f i x * f i y else 1) := by
      simp only [positiveKernelGram, hpoint, FiniteProbabilityWeights.mean_finset_expect]
    _ ≤ p.mean (fun _ => A) := p.mean_mono h
    _ = A := p.mean_const A

theorem countingKernelProductAverage_abs_le_of_boolean_products {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] {b A : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hA : 0 ≤ A) (f : I → X → ℝ) (g : I → Y → ℝ)
    (hf : ∀ choice : I → Bool, (𝔼 x, 𝔼 y, ∏ i, if choice i then f i x * f i y else 1) ≤ A)
    (hg : ∀ choice : I → Bool, (𝔼 x, 𝔼 y, ∏ i, if choice i then g i x * g i y else 1) ≤ A) :
    |countingKernelProductAverage b f g| ≤ A :=
  countingKernelProductAverage_abs_le hb hb1 hA f g
    (positiveKernelGram_le_of_boolean_products hb hb1 f hf)
    (positiveKernelGram_le_of_boolean_products hb hb1 g hg)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem countingKernelProductAverage_outer_sq_le {I X Y Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (f : Z → I → X → ℝ) (g : Z → I → Y → ℝ) :
    (𝔼 z, countingKernelProductAverage b (f z) (g z)) ^ 2 ≤
      (𝔼 z, positiveKernelGram b (f z)) * (𝔼 z, positiveKernelGram b (g z)) := by
  let t := Real.sqrt (b * (1 - b))
  have ht : t ^ 2 = b * (1 - b) := Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hb1))
  have hnt : (-t) ^ 2 = b * (1 - b) := by simpa only [neg_sq] using ht
  let U : Z × (I → Bool) → ℝ := fun q => 𝔼 x, countingFeatureProduct b t (f q.1) q.2 x
  let V : Z × (I → Bool) → ℝ := fun q => 𝔼 y, countingFeatureProduct b (-t) (g q.1) q.2 y
  have hleft : (𝔼 q, U q * V q) = 𝔼 z, countingKernelProductAverage b (f z) (g z) := by
    rw [expect_prod_split]
    simp only [U, V, ← countingKernelProductAverage_factorization ht]
  have hrightU : (𝔼 q, U q ^ 2) = 𝔼 z, positiveKernelGram b (f z) := by
    rw [expect_prod_split]
    simp only [U, countingFeatureProduct_square ht]
  have hrightV : (𝔼 q, V q ^ 2) = 𝔼 z, positiveKernelGram b (g z) := by
    rw [expect_prod_split]
    simp only [V, countingFeatureProduct_square hnt]
  simpa only [hleft, hrightU, hrightV] using
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ U V

theorem mean_positiveKernelGram_le_of_boolean_products {I X Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Z]
    {b A : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (f : Z → I → X → ℝ)
    (h : ∀ choice : I → Bool,
      (𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then f z i x * f z i y else 1) ≤ A) :
    (𝔼 z, positiveKernelGram b (f z)) ≤ A := by
  classical
  let p := FiniteProbabilityWeights.pi (fun _ : I => countingBernoulli hb hb1)
  have hpoint (z : Z) (x y : X) : (∏ i, positiveCountingKernel b (f z i x) (f z i y)) =
      p.mean (fun choice => ∏ i, if choice i then f z i x * f z i y else 1) := by
    simpa only [positiveCountingKernel, mul_assoc] using
      (countingBernoulli_product hb hb1 (fun i => f z i x * f z i y)).symm
  calc
    (𝔼 z, positiveKernelGram b (f z)) =
        p.mean (fun choice => 𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then f z i x * f z i y else 1) := by
      simp only [positiveKernelGram, hpoint, FiniteProbabilityWeights.mean_finset_expect]
    _ ≤ p.mean (fun _ => A) := p.mean_mono h
    _ = A := p.mean_const A

theorem countingKernelProductAverage_outer_abs_le {I X Y Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    {b A : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (hA : 0 ≤ A)
    (f : Z → I → X → ℝ) (g : Z → I → Y → ℝ)
    (hf : ∀ choice : I → Bool,
      (𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then f z i x * f z i y else 1) ≤ A)
    (hg : ∀ choice : I → Bool,
      (𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then g z i x * g z i y else 1) ≤ A) :
    |𝔼 z, countingKernelProductAverage b (f z) (g z)| ≤ A := by
  have hsq := (countingKernelProductAverage_outer_sq_le hb hb1 f g).trans
    (mul_le_mul (mean_positiveKernelGram_le_of_boolean_products hb hb1 f hf)
      (mean_positiveKernelGram_le_of_boolean_products hb hb1 g hg)
      (Finset.expect_nonneg (fun z _ => positiveKernelGram_nonneg hb hb1 (g z))) hA)
  nlinarith [sq_abs (𝔼 z, countingKernelProductAverage b (f z) (g z)),
    abs_nonneg (𝔼 z, countingKernelProductAverage b (f z) (g z))]

end Erdos3

end

end OAI
