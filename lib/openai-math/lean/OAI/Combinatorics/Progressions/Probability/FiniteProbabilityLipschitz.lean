import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
import OAI.Combinatorics.Progressions.Geometry.CompactBoxIntegral

namespace OAI

section

namespace Erdos3

open scoped BigOperators

structure FiniteProbabilityWeights (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace FiniteProbabilityWeights

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

noncomputable def mean (f : Ω → ℝ) : ℝ := ∑ x, p.weight x * f x

noncomputable def correlation (v w : Ω → ℂ) : ℂ :=
  ∑ x, (p.weight x : ℂ) * (v x * star (w x))

theorem mean_nonneg {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ p.mean f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))

theorem mean_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : p.mean f ≤ p.mean g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x))

theorem mean_const (c : ℝ) : p.mean (fun _ => c) = c := by
  rw [mean, ← Finset.sum_mul, p.total, one_mul]

theorem mean_mul_sq_le (f g : Ω → ℝ) :
    (p.mean (fun x => f x * g x)) ^ 2 ≤
      p.mean (fun x => f x ^ 2) * p.mean (fun x => g x ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg (f x)))
    (fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg (g x)))
  intro x _
  exact le_of_eq (by ring)

theorem mean_square_le (f : Ω → ℝ) : (p.mean f) ^ 2 ≤ p.mean (fun x => f x ^ 2) := by
  have h := p.mean_mul_sq_le f (fun _ => 1)
  simpa only [mul_one, one_pow, p.mean_const] using h

theorem norm_correlation_sq_le (v w : Ω → ℂ) :
    ‖p.correlation v w‖ ^ 2 ≤
      p.mean (fun x => ‖v x‖ ^ 2) * p.mean (fun x => ‖w x‖ ^ 2) := by
  have hnorm : ‖p.correlation v w‖ ≤ p.mean (fun x => ‖v x‖ * ‖w x‖) := by
    unfold correlation mean
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro x _
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (p.nonneg x)]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (p.mean_mul_sq_le (fun x => ‖v x‖) (fun x => ‖w x‖))

theorem correlation_self (v : Ω → ℂ) :
    p.correlation v v = (p.mean (fun x => ‖v x‖ ^ 2) : ℂ) := by
  unfold correlation mean
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  change v x * (starRingEnd ℂ) (v x) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem norm_correlation_symm (v w : Ω → ℂ) :
    ‖p.correlation v w‖ = ‖p.correlation w v‖ := by
  have h : star (p.correlation v w) = p.correlation w v := by
    unfold correlation
    simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [← h, norm_star]

theorem mean_single_norm [DecidableEq Ω] (x : Ω) :
    p.mean (fun y => ‖(Pi.single x (1 : ℂ) : Ω → ℂ) y‖) = p.weight x := by
  unfold mean
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (law : C → FiniteProbabilityWeights Ω)

noncomputable def centeredFiniteWeightDensity (z : C × Ω) : ℝ :=
  (law z.1).weight z.2

theorem centeredFiniteWeightDensity_measurable
    (hweight : ∀ x, Measurable (fun c => (law c).weight x)) :
    Measurable (centeredFiniteWeightDensity law) :=
  measurable_from_prod_countable_left hweight

omit [MeasurableSpace C] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFiniteWeightDensity_nonneg (z : C × Ω) :
    0 ≤ centeredFiniteWeightDensity law z := (law z.1).nonneg z.2

omit [MeasurableSpace C] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFiniteWeightDensity_le_one (z : C × Ω) :
    centeredFiniteWeightDensity law z ≤ 1 := by
  change (law z.1).weight z.2 ≤ 1
  rw [← (law z.1).total]
  exact Finset.single_le_sum (fun x _ => (law z.1).nonneg x) (Finset.mem_univ z.2)

theorem centeredFiniteWeightDensity_integrable
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (μ : Measure C) [IsProbabilityMeasure μ] :
    Integrable (centeredFiniteWeightDensity law) (μ.prod Measure.count) := by
  apply (integrable_const (1 : ℝ)).mono'
    (centeredFiniteWeightDensity_measurable law hweight).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_of_nonneg (centeredFiniteWeightDensity_nonneg law z)]
    exact centeredFiniteWeightDensity_le_one law z)

theorem centeredFiniteWeightDensity_integral
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    (μ : Measure C) [IsProbabilityMeasure μ] :
    (∫ z, centeredFiniteWeightDensity law z ∂μ.prod Measure.count) = 1 := by
  rw [integral_prod _ (centeredFiniteWeightDensity_integrable law hweight μ)]
  simp only [centeredFiniteWeightDensity, integral_count, (law _).total]
  simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteProbability_tensor_comparison
    {E Z T O : Type*} [MeasurableSpace E] [Fintype Z]
    [MeasurableSpace T] [MeasurableSpace O]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (p : FiniteProbabilityWeights Z) (ν : Measure T) [IsProbabilityMeasure ν]
    (f : Z → O) (g : T → O) (hg : Measurable g)
    (φ : E × O → ℝ) (hφ : Measurable φ) (hφone : ∀ x, ‖φ x‖ ≤ 1)
    {ε : ℝ}
    (hcomparison : ∀ x,
      |p.mean (fun z => φ (x, f z)) - ∫ t, φ (x, g t) ∂ν| ≤ ε) :
    |(∫ x, p.mean (fun z => φ (x, f z)) ∂μ) -
      ∫ x, ∫ t, φ (x, g t) ∂ν ∂μ| ≤ ε := by
  have hmean : Measurable (fun x => p.mean (fun z => φ (x, f z))) := by
    unfold FiniteProbabilityWeights.mean
    apply Finset.measurable_sum
    intro z _
    exact measurable_const.mul (hφ.comp (measurable_id.prodMk measurable_const))
  have hmean_bound (x : E) : ‖p.mean (fun z => φ (x, f z))‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · calc
        -1 = p.mean (fun _ => -1) := (p.mean_const (-1)).symm
        _ ≤ p.mean (fun z => φ (x, f z)) :=
          p.mean_mono (fun z => (abs_le.mp (hφone (x, f z))).1)
    · calc
        p.mean (fun z => φ (x, f z)) ≤ p.mean (fun _ => 1) :=
          p.mean_mono (fun z => (abs_le.mp (hφone (x, f z))).2)
        _ = 1 := p.mean_const 1
  have hmean_int : Integrable (fun x => p.mean (fun z => φ (x, f z))) μ :=
    Integrable.mono' (integrable_const (1 : ℝ)) hmean.aestronglyMeasurable
      (Filter.Eventually.of_forall hmean_bound)
  have htest : Measurable (fun x : E × T => φ (x.1, g x.2)) :=
    hφ.comp (measurable_fst.prodMk (hg.comp measurable_snd))
  have hinner := htest.stronglyMeasurable.integral_prod_right' (ν := ν)
  have hinner_bound (x : E) : ‖∫ t, φ (x, g t) ∂ν‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := ν)
        (Filter.Eventually.of_forall (fun t => hφone (x, g t)))
  have hinner_int : Integrable (fun x => ∫ t, φ (x, g t) ∂ν) μ :=
    Integrable.mono' (integrable_const (1 : ℝ)) hinner.aestronglyMeasurable
      (Filter.Eventually.of_forall hinner_bound)
  have herr : ∀ᵐ x ∂μ,
      ‖p.mean (fun z => φ (x, f z)) - ∫ t, φ (x, g t) ∂ν‖ ≤ ε :=
    Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hcomparison x)
  rw [← integral_sub hmean_int hinner_int, ← Real.norm_eq_abs]
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const herr

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem finiteSource_density_error_measurable {Ω X I : Type*} [Fintype Ω]
    [MeasurableSpace X] [Fintype I] (p : FiniteProbabilityWeights Ω) (F : Ω → X)
    (μ : Measure X) [SFinite μ] (D : X → (I → ℝ) → ℝ)
    (hD : Measurable (Function.uncurry D)) :
    Measurable (fun v => p.mean (fun x => D (F x) v) - ∫ x, D x v ∂μ) := by
  have hleft : Measurable (fun v => p.mean (fun x => D (F x) v)) := by
    unfold FiniteProbabilityWeights.mean
    apply Finset.measurable_sum
    intro x _
    exact measurable_const.mul (hD.comp (measurable_const.prodMk measurable_id))
  exact hleft.sub hD.stronglyMeasurable.integral_prod_left'.measurable

theorem finiteSource_density_l1_of_uniform_bound {Ω X I : Type*} [Fintype Ω]
    [MeasurableSpace X] [Fintype I] (p : FiniteProbabilityWeights Ω) (F : Ω → X)
    (μ : Measure X) (S : Set X) (hF : ∀ x, F x ∈ S) (hμ : ∀ᵐ x ∂μ, x ∈ S)
    (D : X → (I → ℝ) → ℝ) {R ε : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x ∈ S, ∀ v, R < ‖v‖ → D x v = 0)
    (hm : Measurable (fun v => p.mean (fun x => D (F x) v) - ∫ x, D x v ∂μ))
    (he : ∀ v, |p.mean (fun x => D (F x) v) - ∫ x, D x v ∂μ| ≤ ε) :
    Integrable (fun v => p.mean (fun x => D (F x) v) - ∫ x, D x v ∂μ) ∧
      (∫ v, |p.mean (fun x => D (F x) v) - ∫ x, D x v ∂μ|) ≤ ε*(2*R)^Fintype.card I := by
  let Δ := fun v => p.mean (fun x => D (F x) v) - ∫ x, D x v ∂μ
  have hz (v : I → ℝ) (hv : R < ‖v‖) : Δ v = 0 := by
    have hmean : p.mean (fun x => D (F x) v) = 0 := by
      have hfun : (fun x => D (F x) v) = fun _ => 0 := funext (fun x => hs _ (hF x) v hv)
      rw [hfun, p.mean_const]
    have hint : (∫ x, D x v ∂μ) = 0 :=
      integral_eq_zero_of_ae (hμ.mono (fun x hx => hs x hx v hv))
    exact sub_eq_zero.mpr (hmean.trans hint.symm)
  have hbound (v : I → ℝ) : ‖Δ v‖ ≤ (Metric.closedBall (0 : I → ℝ) R).indicator (fun _ => ε) v := by
    by_cases hv : v ∈ Metric.closedBall (0 : I → ℝ) R
    · rw [Set.indicator_of_mem hv]
      exact he v
    · have hv' : R < ‖v‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hv
      rw [Set.indicator_of_notMem hv, hz v hv', norm_zero]
  have hi : Integrable ((Metric.closedBall (0 : I → ℝ) R).indicator (fun _ => ε)) :=
    (integrableOn_const (isCompact_closedBall (0 : I → ℝ) R).measure_lt_top.ne).integrable_indicator measurableSet_closedBall
  refine ⟨hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hbound), ?_⟩
  exact integral_norm_le_box Δ hR hz (fun v _ => he v)

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped Classical BigOperators NNReal

theorem mean_lipschitz_uniform {A X : Type*} [Fintype A] [PseudoMetricSpace X]
    (p : FiniteProbabilityWeights A) (f : A → X → ℝ) {L : ℝ≥0}
    (hf : ∀ a, LipschitzWith L (f a)) :
    LipschitzWith L (fun x => p.mean (fun a => f a x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ ∑ a, dist (p.weight a * f a x) (p.weight a * f a y) := dist_sum_sum_le _ _ _
    _ = ∑ a, p.weight a * dist (f a x) (f a y) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (p.nonneg _)]
    _ ≤ ∑ a, p.weight a * ((L : ℝ) * dist x y) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left ((hf a).dist_le_mul _ _) (p.nonneg a))
    _ = _ := by rw [← Finset.sum_mul, p.total, one_mul]

theorem mean_lipschitz_uniform_emetric {A X : Type*} [Fintype A] [PseudoEMetricSpace X]
    (p : FiniteProbabilityWeights A) (f : A → X → ℝ) {L : ℝ≥0}
    (hf : ∀ a, LipschitzWith L (f a)) :
    LipschitzWith L (fun x => p.mean (fun a => f a x)) := by
  let w : A → ℝ≥0 := fun a => ⟨p.weight a, p.nonneg a⟩
  have hmul (a : A) : LipschitzWith (w a) (fun x : ℝ => p.weight a * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (p.nonneg a)]
    exact le_rfl
  have hsum (s : Finset A) :
      LipschitzWith (∑ a ∈ s, w a * L) (fun x => ∑ a ∈ s, p.weight a * f a x) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simpa only [Finset.sum_insert ha, Function.comp_def] using ((hmul a).comp (hf a)).add ih
  have hw : (∑ a, w a) = 1 := by
    apply NNReal.coe_injective
    change (↑(∑ a, w a) : ℝ) = 1
    rw [NNReal.coe_sum]
    exact p.total
  simpa only [← Finset.sum_mul, hw, one_mul, mean] using hsum Finset.univ

end Erdos3.FiniteProbabilityWeights

end

end OAI
