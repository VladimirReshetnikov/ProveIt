import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import OAI.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_toReal_hasSum {X : Type*} (p : PMF X) :
    HasSum (fun x => (p x).toReal) 1 := by
  have hs : Summable (fun x => (p x).toReal) :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  have ht : (∑' x, (p x).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe, ENNReal.toReal_one]
  simpa only [ht] using hs.hasSum

theorem pmf_complex_average_summable {X : Type*} (p : PMF X)
    (f : X → ℂ) {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    Summable (fun x => ((p x).toReal : ℂ) * f x) := by
  apply ((pmf_toReal_hasSum p).summable.mul_right B).of_norm_bounded
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf x) ENNReal.toReal_nonneg

theorem pmf_complex_average_error {X : Type*} (p : PMF X)
    (f g : X → ℂ) {Bf Bg ε : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ Bf) (hg : ∀ x, ‖g x‖ ≤ Bg)
    (he : ∀ x, ‖f x - g x‖ ≤ ε) :
    ‖(∑' x, ((p x).toReal : ℂ) * f x) -
      ∑' x, ((p x).toReal : ℂ) * g x‖ ≤ ε := by
  rw [← (pmf_complex_average_summable p f hf).tsum_sub
    (pmf_complex_average_summable p g hg)]
  have hw : HasSum (fun x => (p x).toReal * ε) ε := by
    simpa only [one_mul] using (pmf_toReal_hasSum p).mul_right ε
  apply tsum_of_norm_bounded hw
  intro x
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (he x) ENNReal.toReal_nonneg

theorem pmf_bind_toReal {X Y : Type*} (p : PMF X) (q : X → PMF Y) (y : Y) :
    ((p.bind q) y).toReal = ∑' x, (p x).toReal * (q x y).toReal := by
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun x => ENNReal.mul_ne_top (p.apply_ne_top x) ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul]

theorem pmf_bind_scaled_complex_average {X Y : Type*}
    (p : PMF X) (q : X → PMF Y) (C : ℝ) (y : Y) :
    (∑' x, ((p x).toReal : ℂ) * ((C * (q x y).toReal : ℝ) : ℂ)) =
      ((C * ((p.bind q) y).toReal : ℝ) : ℂ) := by
  simp only [pmf_bind_toReal, Complex.ofReal_mul, Complex.ofReal_tsum]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  ring

theorem pmf_bind_point_error {X Y : Type*} (p : PMF X) (q : X → PMF Y)
    (a : X → ℂ) {C ε : ℝ} (hC : 0 ≤ C) (y : Y)
    (he : ∀ x, ‖((C * (q x y).toReal : ℝ) : ℂ) - a x‖ ≤ ε) :
    ‖((C * ((p.bind q) y).toReal : ℝ) : ℂ) -
      ∑' x, ((p x).toReal : ℂ) * a x‖ ≤ ε := by
  let f (x : X) : ℂ := ((C * (q x y).toReal : ℝ) : ℂ)
  have hf (x : X) : ‖f x‖ ≤ C := by
    have hp : (q x y).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top ((q x).coe_le_one y)
    change ‖((C * (q x y).toReal : ℝ) : ℂ)‖ ≤ C
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC ENNReal.toReal_nonneg)]
    exact (mul_le_mul_of_nonneg_left hp hC).trans_eq (mul_one C)
  have ha (x : X) : ‖a x‖ ≤ C + ε := by
    calc
      ‖a x‖ = ‖(a x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖a x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ ε + C := add_le_add (by simpa only [norm_sub_rev] using he x) (hf x)
      _ = C + ε := add_comm _ _
  have h := pmf_complex_average_error p f a hf ha he
  change ‖(∑' x, ((p x).toReal : ℂ) * ((C * (q x y).toReal : ℝ) : ℂ)) -
    ∑' x, ((p x).toReal : ℂ) * a x‖ ≤ ε at h
  rw [pmf_bind_scaled_complex_average] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_bind_measure_eq_sum {X Y : Type*} [MeasurableSpace Y]
    (p : PMF X) (q : X → PMF Y) :
    (p.bind q).toMeasure = Measure.sum (fun x => (p x) • (q x).toMeasure) := by
  ext s hs
  rw [PMF.toMeasure_bind_apply _ _ _ hs, Measure.sum_apply _ hs]
  apply tsum_congr
  intro x
  rw [Measure.smul_apply, smul_eq_mul]

theorem pmf_bind_integral_tsum {X Y E : Type*} [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : PMF X) (q : X → PMF Y) (f : Y → E)
    (hf : Integrable f (p.bind q).toMeasure) :
    (∫ y, f y ∂(p.bind q).toMeasure) = ∑' x, (p x).toReal • ∫ y, f y ∂(q x).toMeasure := by
  rw [pmf_bind_measure_eq_sum] at hf ⊢
  rw [integral_sum_measure hf]
  simp only [integral_smul_measure]

theorem pmf_integral_bind {X Y E : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : PMF X) (q : X → PMF Y) (f : Y → E)
    (hf : Integrable f (p.bind q).toMeasure)
    (hi : Integrable (fun x => ∫ y, f y ∂(q x).toMeasure) p.toMeasure) :
    (∫ y, f y ∂(p.bind q).toMeasure) =
      ∫ x, ∫ y, f y ∂(q x).toMeasure ∂p.toMeasure :=
  (pmf_bind_integral_tsum p q f hf).trans (p.integral_eq_tsum _ hi).symm

theorem FiniteProbabilityWeights.integral_bind_real {X Y : Type*}
    [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (q : X → PMF Y) (f : Y → ℝ)
    (hf : Integrable f (p.toPMF.bind q).toMeasure) :
    (∫ y, f y ∂(p.toPMF.bind q).toMeasure) =
      p.mean (fun x => ∫ y, f y ∂(q x).toMeasure) := by
  rw [pmf_bind_integral_tsum p.toPMF q f hf, tsum_fintype]
  simp only [FiniteProbabilityWeights.toPMF_toReal, smul_eq_mul, FiniteProbabilityWeights.mean]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X Y : Type*} [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]

theorem pmf_bind_toReal_integral (p : PMF X) (q : X → PMF Y) (z : Y) :
    ((p.bind q) z).toReal = ∫ x, (q x z).toReal ∂p.toMeasure := by
  have hb (x : X) : (q x z).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top ((q x).coe_le_one z)
  have hi : Integrable (fun x => (q x z).toReal) p.toMeasure := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_of_nonneg ENNReal.toReal_nonneg] using hb x)
  rw [pmf_bind_toReal, p.integral_eq_tsum _ hi]
  simp only [smul_eq_mul]

theorem pmf_bind_point_approximation_error (p : PMF X) (q : X → PMF Y)
    (z : Y) (approx : X → ℂ) {K ε : ℝ} (hK : 0 ≤ K)
    (herr : ∀ x, ‖((K * (q x z).toReal : ℝ) : ℂ) - approx x‖ ≤ ε) :
    ‖((K * ((p.bind q) z).toReal : ℝ) : ℂ) - ∫ x, approx x ∂p.toMeasure‖ ≤ ε := by
  let f (x : X) : ℂ := (K * (q x z).toReal : ℝ)
  have hf (x : X) : ‖f x‖ ≤ K := by
    have hb : (q x z).toReal ≤ 1 := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top ((q x).coe_le_one z)
    change ‖((K * (q x z).toReal : ℝ) : ℂ)‖ ≤ K
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hK ENNReal.toReal_nonneg)]
    exact mul_le_of_le_one_right hK hb
  have ha (x : X) : ‖approx x‖ ≤ ε + K := by
    calc
      _ = ‖(approx x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖approx x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ ε + K := add_le_add (by simpa only [norm_sub_rev] using herr x) (hf x)
  have hai : Integrable approx p.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (ε + K) (ae_of_all _ ha)
  rw [p.integral_eq_tsum approx hai]
  simpa only [Complex.real_smul] using pmf_bind_point_error p q approx hK z herr

end Erdos3

end

end OAI
