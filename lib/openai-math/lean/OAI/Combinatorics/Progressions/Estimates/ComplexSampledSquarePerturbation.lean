import OAI.Combinatorics.Progressions.Probability.DensityComparisonComposition

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem complex_model_l1_le_of_bounded_tests {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) {ε : ℝ}
    (he : ∀ φ : X → ℂ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      ‖(∫ x, f x * φ x ∂μ) - ∫ x, g x * φ x ∂μ‖ ≤ ε) :
    (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  let φ := fun x => (starRingEnd ℂ) (f x - g x) / (‖f x - g x‖ : ℂ)
  have hφ : Measurable φ := (Complex.continuous_conj.measurable.comp (hf.sub hg)).div (hf.sub hg).norm.complex_ofReal
  have hbound (x) : ‖φ x‖ ≤ 1 := by
    dsimp only [φ]
    rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  have hidentity (x) : (f x - g x) * φ x = (‖f x - g x‖ : ℂ) := by
    dsimp only [φ]
    rw [← mul_div_assoc, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_div]
    by_cases h : ‖f x - g x‖ = 0
    · simp [h]
    · rw [pow_two, mul_div_cancel_right₀ _ h]
  have hif := hfi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hig := hgi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have h := he φ hφ hbound
  rw [← integral_sub hif hig] at h
  simp_rw [← sub_mul, hidentity] at h
  rw [integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))] at h
  exact h

namespace FiniteProbabilityWeights

theorem complexMean_integral {Y X : Type*} [Fintype Y] [MeasurableSpace X]
    (law : FiniteProbabilityWeights Y) (μ : Measure X) (f : Y → X → ℂ)
    (hf : ∀ y, Integrable (f y) μ) :
    law.complexMean (fun y => ∫ x, f y x ∂μ) =
      ∫ x, law.complexMean (fun y => f y x) ∂μ := by
  simp only [complexMean]
  rw [integral_finsetSum _ (fun y _ => (hf y).const_mul _)]
  simp only [integral_const_mul]

theorem mean_density_test_integral {Y X : Type*} [Fintype Y] [MeasurableSpace X]
    (law : FiniteProbabilityWeights Y) (μ : Measure X) (g : Y → X → ℝ)
    (hgi : ∀ y, Integrable (g y) μ)
    (φ : X → ℂ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1) :
    law.complexMean (fun y => ∫ x, (g y x : ℂ) * φ x ∂μ) =
      ∫ x, (law.mean (fun y => g y x) : ℂ) * φ x ∂μ := by
  refine (law.complexMean_integral μ _ (fun y =>
    (hgi y).ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb))).trans ?_
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x =>
    law.complexMean_ofReal_mul (fun y => g y x) (φ x)))

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

theorem complex_model_l2_le_of_l1 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f g : X → ℂ)
    (hf : Measurable f) (hg : Measurable g) (Cf Cg : ℝ≥0)
    (hfb : ∀ x, ‖f x‖ ≤ Cf) (hgb : ∀ x, ‖g x‖ ≤ Cg) {E : ℝ}
    (hE : (∫ x, ‖f x - g x‖ ∂μ) ≤ E) :
    (∫ x, ‖f x - g x‖ ^ 2 ∂μ) ≤ (Cf + Cg : ℝ≥0) * E := by
  have hb (x) : ‖f x - g x‖ ≤ (Cf + Cg : ℝ≥0) :=
    (norm_sub_le _ _).trans (add_le_add (hfb x) (hgb x))
  have hi : Integrable (fun x => ‖f x - g x‖) μ :=
    Integrable.of_bound (hf.sub hg).norm.aestronglyMeasurable (Cf + Cg)
      (Filter.Eventually.of_forall (fun x => by simpa only [norm_norm, NNReal.coe_add] using hb x))
  have hs : Integrable (fun x => ‖f x - g x‖ ^ 2) μ :=
    Integrable.of_bound ((hf.sub hg).norm.pow_const 2).aestronglyMeasurable
      (((Cf + Cg : ℝ≥0) : ℝ) ^ 2)
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2))
  calc
    _ ≤ ∫ x, ((Cf + Cg : ℝ≥0) : ℝ) * ‖f x - g x‖ ∂μ :=
      integral_mono hs (hi.const_mul _) (fun x => by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))
    _ = ((Cf + Cg : ℝ≥0) : ℝ) * ∫ x, ‖f x - g x‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (NNReal.coe_nonneg _)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem complex_norm_sub_sq_le {a b c : ℂ} :
    ‖a - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b - c‖ ^ 2 := by
  have ht : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a - b) (b - c)
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith [sq_nonneg (‖a - b‖ - ‖b - c‖)]

theorem complex_square_integral_uniform_perturbation
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f f' g : X → ℂ) (hf' : Measurable f') (hg : Measurable g)
    {δ E : ℝ} (happrox : ∀ x, ‖f' x - f x‖ ≤ δ)
    (hi : Integrable (fun x => ‖f x - g x‖ ^ 2) μ)
    (he : (∫ x, ‖f x - g x‖ ^ 2 ∂μ) ≤ E) :
    (∫ x, ‖f' x - g x‖ ^ 2 ∂μ) ≤ 2 * δ ^ 2 + 2 * E := by
  have hb (x) : ‖f' x - g x‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * ‖f x - g x‖ ^ 2 := by
    have ht := complex_norm_sub_sq_le (a := f' x) (b := f x) (c := g x)
    have hs := pow_le_pow_left₀ (norm_nonneg _) (happrox x) 2
    linarith
  have hdom : Integrable (fun x => 2 * δ ^ 2 + 2 * ‖f x - g x‖ ^ 2) μ :=
    (integrable_const _).add (hi.const_mul _)
  have hi' : Integrable (fun x => ‖f' x - g x‖ ^ 2) μ :=
    hdom.mono' ((hf'.sub hg).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hb x))
  calc
    _ ≤ ∫ x, 2 * δ ^ 2 + 2 * ‖f x - g x‖ ^ 2 ∂μ := integral_mono hi' hdom hb
    _ = 2 * δ ^ 2 + 2 * ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by
      rw [integral_add (integrable_const _) (hi.const_mul _)]
      simp [integral_const_mul]
    _ ≤ _ := by linarith

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

theorem finiteComplex_norm_sq_expansion {A : Type*} [Fintype A]
    (c f : A → ℂ) :
    (‖∑ a, c a * f a‖ ^ 2 : ℂ) =
      ∑ a, ∑ b, (c a * star (c b)) * (f a * star (f b)) := by
  rw [← Complex.mul_conj']
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change c a * f a * (star (c b) * star (f b)) = _
  ring

theorem finiteComplex_quadratic_error_le {A : Type*} [Fintype A]
    (c : A → ℂ) (M N : A → A → ℂ) {ε : ℝ}
    (h : ∀ a b, ‖M a b - N a b‖ ≤ ε) :
    ‖(∑ a, ∑ b, (c a * star (c b)) * M a b) -
      ∑ a, ∑ b, (c a * star (c b)) * N a b‖ ≤ (∑ a, ‖c a‖) ^ 2 * ε := by
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ a, ∑ b, ‖(c a * star (c b)) * (M a b - N a b)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ a, ∑ b, (‖c a‖ * ‖c b‖) * ε := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (h a b) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp only [← Finset.sum_mul, ← Finset.mul_sum, pow_two]

theorem finiteComplex_norm_sq_integral {A X : Type*} [Fintype A] [MeasurableSpace X]
    (μ : Measure X) (c : A → ℂ) (f : A → X → ℂ)
    (hi : ∀ a b, Integrable (fun x => f a x * star (f b x)) μ) :
    Complex.ofReal (∫ x, ‖∑ a, c a * f a x‖ ^ 2 ∂μ) =
      ∑ a, ∑ b, (c a * star (c b)) * ∫ x, f a x * star (f b x) ∂μ := by
  rw [← integral_complex_ofReal]
  simp_rw [Complex.ofReal_pow, finiteComplex_norm_sq_expansion]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hi a b).const_mul _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => (hi a b).const_mul _)]
  simp only [integral_const_mul]

theorem finiteComplex_l2_integral_comparison
    {A X Y : Type*} [Fintype A] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (c : A → ℂ) (f : A → X → ℂ) (g : A → Y → ℂ)
    (hfi : ∀ a b, Integrable (fun x => f a x * star (f b x)) μ)
    (hgi : ∀ a b, Integrable (fun y => g a y * star (g b y)) ν) {ε : ℝ}
    (hpair : ∀ a b, ‖(∫ x, f a x * star (f b x) ∂μ) -
      ∫ y, g a y * star (g b y) ∂ν‖ ≤ ε) :
    |(∫ x, ‖∑ a, c a * f a x‖ ^ 2 ∂μ) -
      ∫ y, ‖∑ a, c a * g a y‖ ^ 2 ∂ν| ≤ (∑ a, ‖c a‖) ^ 2 * ε := by
  have h := finiteComplex_quadratic_error_le c _ _ hpair
  rw [← finiteComplex_norm_sq_integral μ c f hfi,
    ← finiteComplex_norm_sq_integral ν c g hgi,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal

theorem complex_square_sub_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f g : X → ℂ)
    (hf : Measurable f) (hg : Measurable g) (Cf Cg : ℝ≥0)
    (hfb : ∀ x, ‖f x‖ ≤ Cf) (hgb : ∀ x, ‖g x‖ ≤ Cg) :
    Integrable (fun x => ‖f x - g x‖ ^ 2) μ := by
  apply Integrable.of_bound ((hf.sub hg).norm.pow_const 2).aestronglyMeasurable
    (((Cf + Cg : ℝ≥0) : ℝ) ^ 2)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sub_le _ _).trans (add_le_add (hfb x) (hgb x))) 2

theorem complex_sampled_square_perturbation
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (f fa g : X → ℂ) (F Fa G : Y → ℂ)
    (hf : Measurable f) (hfa : Measurable fa) (hg : Measurable g)
    (hF : Measurable F) (hFa : Measurable Fa) (hG : Measurable G)
    (Cf Cg Ca : ℝ≥0)
    (hfb : ∀ x, ‖fa x‖ ≤ Ca) (hgb : ∀ x, ‖g x‖ ≤ Cg)
    (hFb : ∀ y, ‖F y‖ ≤ Cf) (hGb : ∀ y, ‖G y‖ ≤ Cg)
    {δ E ε : ℝ} (ha : ∀ x, ‖f x - fa x‖ ≤ δ)
    (hA : ∀ y, ‖F y - Fa y‖ ≤ δ)
    (hL1 : (∫ y, ‖F y - G y‖ ∂ν) ≤ E)
    (hsample : |(∫ x, ‖fa x - g x‖ ^ 2 ∂μ) - (∫ y, ‖Fa y - G y‖ ^ 2 ∂ν)| ≤ ε) :
    (∫ x, ‖f x - g x‖ ^ 2 ∂μ) ≤ 6 * δ ^ 2 + 4 * (Cf + Cg : ℝ≥0) * E + 2 * ε := by
  have hi := complex_square_sub_integrable ν F G hF hG Cf Cg hFb hGb
  have hsq := complex_model_l2_le_of_l1 ν F G hF hG Cf Cg hFb hGb hL1
  have happrox := complex_square_integral_uniform_perturbation ν F Fa G hFa hG
    (fun y => by simpa only [norm_sub_rev] using hA y) hi hsq
  have he : (∫ x, ‖fa x - g x‖ ^ 2 ∂μ) ≤
      2 * δ ^ 2 + 2 * ((Cf + Cg : ℝ≥0) * E) + ε := by
    have ht := (le_abs_self ((∫ x, ‖fa x - g x‖ ^ 2 ∂μ) -
      (∫ y, ‖Fa y - G y‖ ^ 2 ∂ν))).trans hsample
    linarith
  have hs := complex_square_integral_uniform_perturbation μ fa f g hf hg ha
    (complex_square_sub_integrable μ fa g hfa hg Ca Cg hfb hgb) he
  linarith

end Erdos3

end

end OAI
