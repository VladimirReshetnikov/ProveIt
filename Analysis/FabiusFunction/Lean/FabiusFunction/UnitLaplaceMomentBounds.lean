import FabiusFunction.ProbabilityLaplaceMoments
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Generic bounds for unit-interval Laplace moments

For `M_k(s) = unitLaplaceMoment μ s k`, this module first proves the exact
comparison between any two real tilts

`exp (min (t - s) 0) * M_k(t) ≤ M_k(s) ≤
  exp (max (t - s) 0) * M_k(t)`.

It follows that strict positivity is independent of the tilt.  The
weighted-sum probability representation then gives the same bounds for
`fabiusLaplaceMoment`; its positive zero-tilt half moments show that every
degree is strictly positive at every real tilt.

The module also proves midpoint log-convexity and factorial absorption for
`unitLaplaceMoment` of any measure finite on compact sets.  These estimates use
arbitrary real tilts and arbitrary positive amounts subtracted from a tilt; the
three-quarter formulas used by the Fabius asymptotic layer are retained as
thin specializations.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ENNReal

namespace Fabius

/-- Quantitative comparison of the `k`th unit-interval Laplace moment at any
two real tilts.  For a measure finite on compact sets and `s t : ℝ`,

`exp (min (t - s) 0) * M_k(t) ≤ M_k(s) ≤
  exp (max (t - s) 0) * M_k(t)`.

Indeed, changing the tilt from `t` to `s` multiplies the integrand by
`exp ((t - s) * x)`, whose exponent lies between `min (t - s) 0` and
`max (t - s) 0` on `[0,1]`. -/
theorem unitLaplaceMoment_tilt_bounds
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (s t : ℝ) :
    Real.exp (min (t - s) 0) * unitLaplaceMoment μ t k ≤
        unitLaplaceMoment μ s k ∧
      unitLaplaceMoment μ s k ≤
        Real.exp (max (t - s) 0) * unitLaplaceMoment μ t k := by
  have hIntegrable (u : ℝ) : IntegrableOn
      (fun x : ℝ => Real.exp (-u * x) * x ^ k) (Icc (0 : ℝ) 1) μ := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    fun_prop
  have hLower : IntegrableOn
      (fun x : ℝ => Real.exp (min (t - s) 0) *
        (Real.exp (-t * x) * x ^ k)) (Icc (0 : ℝ) 1) μ :=
    (hIntegrable t).const_mul (Real.exp (min (t - s) 0))
  have hUpper : IntegrableOn
      (fun x : ℝ => Real.exp (max (t - s) 0) *
        (Real.exp (-t * x) * x ^ k)) (Icc (0 : ℝ) 1) μ :=
    (hIntegrable t).const_mul (Real.exp (max (t - s) 0))
  have hmul_bounds (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      min (t - s) 0 ≤ (t - s) * x ∧
        (t - s) * x ≤ max (t - s) 0 := by
    by_cases hδ : 0 ≤ t - s
    · rw [min_eq_right hδ, max_eq_left hδ]
      constructor
      · exact mul_nonneg hδ hx.1
      · calc
          (t - s) * x ≤ (t - s) * 1 :=
            mul_le_mul_of_nonneg_left hx.2 hδ
          _ = t - s := mul_one _
    · have hδ' : t - s ≤ 0 := le_of_not_ge hδ
      rw [min_eq_left hδ', max_eq_right hδ']
      constructor
      · calc
          t - s = (t - s) * 1 := (mul_one _).symm
          _ ≤ (t - s) * x := mul_le_mul_of_nonpos_left hx.2 hδ'
      · exact mul_nonpos_of_nonpos_of_nonneg hδ' hx.1
  have hpointwise (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Real.exp (min (t - s) 0) * (Real.exp (-t * x) * x ^ k) ≤
          Real.exp (-s * x) * x ^ k ∧
        Real.exp (-s * x) * x ^ k ≤
          Real.exp (max (t - s) 0) * (Real.exp (-t * x) * x ^ k) := by
    have hrewrite : Real.exp (-s * x) * x ^ k =
        Real.exp ((t - s) * x) * (Real.exp (-t * x) * x ^ k) := by
      rw [show -s * x = (t - s) * x + -t * x by ring, Real.exp_add]
      ring
    rw [hrewrite]
    have hnonneg : 0 ≤ Real.exp (-t * x) * x ^ k :=
      mul_nonneg (Real.exp_nonneg _) (pow_nonneg hx.1 k)
    exact ⟨
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (hmul_bounds x hx).1) hnonneg,
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (hmul_bounds x hx).2) hnonneg⟩
  unfold unitLaplaceMoment
  constructor
  · rw [← MeasureTheory.integral_const_mul]
    apply integral_mono_ae hLower (hIntegrable s)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (hpointwise x hx).1
  · rw [← MeasureTheory.integral_const_mul]
    apply integral_mono_ae (hIntegrable s) hUpper
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (hpointwise x hx).2

/-- Strict positivity of a unit-interval Laplace moment does not depend on the
real tilt.  For every natural degree `k` and real tilts `s,t`,

`0 < M_k(s) ↔ 0 < M_k(t)`.

The measure need only be finite on compact sets; in particular, the statement
also covers a zero measure or a measure whose positive-degree moments vanish. -/
theorem unitLaplaceMoment_pos_iff
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (s t : ℝ) :
    0 < unitLaplaceMoment μ s k ↔ 0 < unitLaplaceMoment μ t k := by
  constructor
  · intro hs
    exact lt_of_lt_of_le
      (mul_pos (Real.exp_pos _) hs)
      (unitLaplaceMoment_tilt_bounds μ k t s).1
  · intro ht
    exact lt_of_lt_of_le
      (mul_pos (Real.exp_pos _) ht)
      (unitLaplaceMoment_tilt_bounds μ k s t).1

/-- Cauchy--Schwarz midpoint log-convexity for the tilted mass of any measure
on `[0,1]`, at arbitrary real tilts. -/
theorem unitLaplaceMoment_midpoint_le_sqrt
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (a b : ℝ) :
    unitLaplaceMoment μ ((a + b) / 2) 0 ≤
      (unitLaplaceMoment μ a 0) ^ (1 / 2 : ℝ) *
        (unitLaplaceMoment μ b 0) ^ (1 / 2 : ℝ) := by
  let ν : Measure ℝ := μ.restrict (Icc (0 : ℝ) 1)
  letI : IsFiniteMeasure ν := by
    dsimp [ν]
    exact isFiniteMeasure_restrict.2 isCompact_Icc.measure_ne_top
  let f : ℝ → ℝ := fun x => Real.exp (-(a / 2) * x)
  let g : ℝ → ℝ := fun x => Real.exp (-(b / 2) * x)
  have hf_meas : AEStronglyMeasurable f ν := by
    exact (by fun_prop : Continuous f).aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable g ν := by
    exact (by fun_prop : Continuous g).aestronglyMeasurable
  have hf : MemLp f (ENNReal.ofReal 2) ν := by
    simpa using (memLp_two_iff_integrable_sq hf_meas).2 (show
      IntegrableOn (fun x : ℝ => f x ^ 2) (Icc (0 : ℝ) 1) μ by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        fun_prop)
  have hg : MemLp g (ENNReal.ofReal 2) ν := by
    simpa using (memLp_two_iff_integrable_sq hg_meas).2 (show
      IntegrableOn (fun x : ℝ => g x ^ 2) (Icc (0 : ℝ) 1) μ by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        fun_prop)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le) hf hg
  simp only [unitLaplaceMoment, pow_zero, mul_one]
  change (∫ x, Real.exp (-((a + b) / 2) * x) ∂ν) ≤ _
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with x
    rw [← Real.exp_add]
    congr 1
    ring
  · congr 1
    · apply congrArg (fun y : ℝ => y ^ (1 / 2 : ℝ))
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_two, ← Real.exp_nat_mul]
      congr 1
      ring
    · apply congrArg (fun y : ℝ => y ^ (1 / 2 : ℝ))
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.rpow_two, ← Real.exp_nat_mul]
      congr 1
      ring

/-- The three-quarter specialization of midpoint log-convexity, valid at
every real tilt. -/
theorem unitLaplaceMoment_three_quarters_le_sqrt
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (s : ℝ) :
    unitLaplaceMoment μ (3 * s / 4) 0 ≤
      (unitLaplaceMoment μ (s / 2) 0) ^ (1 / 2 : ℝ) *
        (unitLaplaceMoment μ s 0) ^ (1 / 2 : ℝ) := by
  simpa only [show ((s / 2 + s) / 2 : ℝ) = 3 * s / 4 by ring] using
    unitLaplaceMoment_midpoint_le_sqrt μ (s / 2) s

/-- Squared Cauchy--Schwarz midpoint log-convexity for the tilted mass of any
measure on `[0,1]`, at arbitrary real tilts. -/
theorem unitLaplaceMoment_midpoint_sq_le_all
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (a b : ℝ) :
    unitLaplaceMoment μ ((a + b) / 2) 0 ^ 2 ≤
      unitLaplaceMoment μ a 0 * unitLaplaceMoment μ b 0 := by
  let A := unitLaplaceMoment μ a 0
  let B := unitLaplaceMoment μ b 0
  let C := unitLaplaceMoment μ ((a + b) / 2) 0
  have hA : 0 ≤ A := unitLaplaceMoment_nonneg _ _ _
  have hB : 0 ≤ B := unitLaplaceMoment_nonneg _ _ _
  have hC : 0 ≤ C := unitLaplaceMoment_nonneg _ _ _
  have h := unitLaplaceMoment_midpoint_le_sqrt μ a b
  change C ≤ A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) at h
  change C ^ 2 ≤ A * B
  calc
    C ^ 2 ≤ (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) ^ 2 := by
      exact (sq_le_sq₀ hC (by positivity)).2 h
    _ = A * B := by
      rw [mul_pow]
      rw [show (A ^ (1 / 2 : ℝ)) ^ 2 = A by
        simpa [one_div] using
          (Real.rpow_inv_natCast_pow hA (by norm_num : (2 : ℕ) ≠ 0))]
      rw [show (B ^ (1 / 2 : ℝ)) ^ 2 = B by
        simpa [one_div] using
          (Real.rpow_inv_natCast_pow hB (by norm_num : (2 : ℕ) ≠ 0))]

set_option linter.unusedVariables false in
/-- Compatibility form of midpoint log-convexity for finite measures and
nonnegative tilts.  The sign hypotheses are unnecessary in the all-real
theorem `unitLaplaceMoment_midpoint_sq_le_all`. -/
theorem unitLaplaceMoment_midpoint_sq_le
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    unitLaplaceMoment μ ((a + b) / 2) 0 ^ 2 ≤
      unitLaplaceMoment μ a 0 * unitLaplaceMoment μ b 0 :=
  unitLaplaceMoment_midpoint_sq_le_all μ a b

/-- The squared three-quarter specialization of midpoint log-convexity,
valid at every real tilt. -/
theorem unitLaplaceMoment_three_quarters_sq_le_all
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (s : ℝ) :
    unitLaplaceMoment μ (3 * s / 4) 0 ^ 2 ≤
      unitLaplaceMoment μ (s / 2) 0 * unitLaplaceMoment μ s 0 := by
  simpa only [show ((s / 2 + s) / 2 : ℝ) = 3 * s / 4 by ring] using
    unitLaplaceMoment_midpoint_sq_le_all μ (s / 2) s

set_option linter.unusedVariables false in
/-- Compatibility form of the squared three-quarter estimate for a finite
measure and a nonnegative tilt.  The generic estimate is valid for every real
tilt. -/
theorem unitLaplaceMoment_three_quarters_sq_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) (hs : 0 ≤ s) :
    unitLaplaceMoment μ (3 * s / 4) 0 ^ 2 ≤
      unitLaplaceMoment μ (s / 2) 0 * unitLaplaceMoment μ s 0 :=
  unitLaplaceMoment_three_quarters_sq_le_all μ s

/-- A power can be absorbed into any positive exponential tilt. -/
theorem pow_mul_exp_neg_mul_le_factorial
    (k : ℕ) {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(a * x)) ≤
      (1 / a) ^ k * (k.factorial : ℝ) := by
  let y : ℝ := a * x
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hseries := Real.pow_div_factorial_le_exp y hy k
  have hmul := mul_le_mul_of_nonneg_right hseries (Real.exp_nonneg (-y))
  have hybound : y ^ k * Real.exp (-y) ≤ (k.factorial : ℝ) := by
    rw [div_mul_eq_mul_div] at hmul
    rw [← Real.exp_add] at hmul
    norm_num at hmul
    rwa [div_le_one hfac] at hmul
  have hscale : x = (1 / a) * y := by
    dsimp [y]
    field_simp
  rw [hscale, mul_pow]
  have hexp : -(a * ((1 / a) * y)) = -y := by
    field_simp
  rw [hexp, mul_assoc]
  exact mul_le_mul_of_nonneg_left hybound (pow_nonneg (by positivity) k)

/-- The standard unit-tilt estimate `x^k exp(-x) ≤ k!` for `x ≥ 0`. -/
theorem pow_mul_exp_neg_le_factorial
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-x) ≤ (k.factorial : ℝ) := by
  simpa using pow_mul_exp_neg_mul_le_factorial
    k (a := 1) (by norm_num) hx

/-- A power can be absorbed into one quarter of a positive exponential tilt. -/
theorem pow_mul_exp_neg_quarter_le
    (k : ℕ) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(s * x / 4)) ≤
      (4 / s) ^ k * (k.factorial : ℝ) := by
  have h := pow_mul_exp_neg_mul_le_factorial
    k (show 0 < s / 4 by positivity) hx
  have hscale : (1 / (s / 4) : ℝ) = 4 / s := by field_simp
  have hexp : (s / 4) * x = s * x / 4 := by ring
  simpa only [hscale, hexp] using h

/-- Trading powers of the variable for any positive amount `a` subtracted
from the tilt,
for the unit-interval Laplace moments of any compactly finite measure. -/
theorem unitLaplaceMoment_le_of_tilt_sub
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (s : ℝ) {a : ℝ} (ha : 0 < a) :
    unitLaplaceMoment μ s k ≤
      ((1 / a) ^ k * (k.factorial : ℝ)) *
        unitLaplaceMoment μ (s - a) 0 := by
  let C : ℝ := (1 / a) ^ k * (k.factorial : ℝ)
  have hleft : IntegrableOn
      (fun x : ℝ => Real.exp (-s * x) * x ^ k) (Icc (0 : ℝ) 1) μ := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    fun_prop
  have hright : IntegrableOn
      (fun x : ℝ => C * (Real.exp (-(s - a) * x) * x ^ 0))
      (Icc (0 : ℝ) 1) μ := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    fun_prop
  unfold unitLaplaceMoment
  rw [← MeasureTheory.integral_const_mul]
  apply integral_mono_ae hleft hright
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [pow_zero, mul_one]
  have hsplit : Real.exp (-s * x) =
      Real.exp (-(s - a) * x) * Real.exp (-(a * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  rw [mul_assoc, mul_comm (Real.exp (-(a * x))) (x ^ k)]
  calc
    Real.exp (-(s - a) * x) * (x ^ k * Real.exp (-(a * x))) ≤
        Real.exp (-(s - a) * x) * C := by
      exact mul_le_mul_of_nonneg_left
        (pow_mul_exp_neg_mul_le_factorial k ha hx.1)
        (Real.exp_nonneg _)
    _ = C * Real.exp (-(s - a) * x) := by ring

/-- Compatibility name for trading powers for a positive amount of tilt in a
finite measure. -/
theorem unitLaplaceMoment_le_shift
    (μ : Measure ℝ) [IsFiniteMeasure μ] (k : ℕ)
    {s a : ℝ} (ha : 0 < a) :
    unitLaplaceMoment μ s k ≤
      ((1 / a) ^ k * (k.factorial : ℝ)) *
        unitLaplaceMoment μ (s - a) 0 :=
  unitLaplaceMoment_le_of_tilt_sub μ k s ha

/-- Trading powers of the variable for one quarter of the tilt, for the
unit-interval Laplace moments of any finite measure. -/
theorem unitLaplaceMoment_le_three_quarters
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (k : ℕ) {s : ℝ} (hs : 0 < s) :
    unitLaplaceMoment μ s k ≤
      ((4 / s) ^ k * (k.factorial : ℝ)) *
        unitLaplaceMoment μ (3 * s / 4) 0 := by
  have h := unitLaplaceMoment_le_of_tilt_sub
    μ k s (show 0 < s / 4 by positivity)
  have hscale : (1 / (s / 4) : ℝ) = 4 / s := by field_simp
  have htilt : s - s / 4 = 3 * s / 4 := by ring
  simpa only [hscale, htilt] using h

/-- The exact two-tilt comparison for every Fabius Laplace moment.  For any
bounded Fabius candidate satisfying `IsFabius`, any degree `k`, and real tilts
`s,t`,

`exp (min (t - s) 0) * M_k(t) ≤ M_k(s) ≤
  exp (max (t - s) 0) * M_k(t)`.

This is the measure-generic unit-interval estimate transported through the
weighted-sum probability representation. -/
theorem fabiusLaplaceMoment_tilt_bounds
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (s t : ℝ) :
    Real.exp (min (t - s) 0) * fabiusLaplaceMoment F k t ≤
        fabiusLaplaceMoment F k s ∧
      fabiusLaplaceMoment F k s ≤
        Real.exp (max (t - s) 0) * fabiusLaplaceMoment F k t := by
  simpa only [
    ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
      F hF] using
    unitLaplaceMoment_tilt_bounds
      ProbabilityRepresentation.weightedSumDistribution k s t

/-- Every Fabius Laplace moment is strictly positive: for every natural degree
`k` and every real tilt `s`,

`0 < fabiusLaplaceMoment F k s`.

At zero tilt this is the positivity of the exact half moment `halfMoment k`;
`fabiusLaplaceMoment_tilt_bounds` transports it to arbitrary real tilts. -/
theorem fabiusLaplaceMoment_pos_all
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (s : ℝ) :
    0 < fabiusLaplaceMoment F k s := by
  have hzero : 0 < fabiusLaplaceMoment F k 0 := by
    rw [fabiusLaplaceMoment_zero_eq_halfMoment F hF]
    exact_mod_cast halfMoment_pos k
  exact lt_of_lt_of_le
    (mul_pos (Real.exp_pos _) hzero)
    (fabiusLaplaceMoment_tilt_bounds F hF k s 0).1

/-- Midpoint log-convexity for the zeroth tilted moments of any bounded Fabius
candidate, at arbitrary real tilts. -/
theorem fabiusLaplaceMoment_midpoint_sq_le_all
    (F : BoundedFabius) (hF : IsFabius F) (a b : ℝ) :
    fabiusLaplaceMoment F 0 ((a + b) / 2) ^ 2 ≤
      fabiusLaplaceMoment F 0 a * fabiusLaplaceMoment F 0 b := by
  simpa only [
    ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
      F hF] using
    unitLaplaceMoment_midpoint_sq_le_all
      ProbabilityRepresentation.weightedSumDistribution a b

set_option linter.unusedVariables false in
/-- Compatibility form of Fabius midpoint log-convexity on the nonnegative
tilt ray.  The sign hypotheses are unnecessary in the all-real theorem
`fabiusLaplaceMoment_midpoint_sq_le_all`. -/
theorem fabiusLaplaceMoment_midpoint_sq_le
    (F : BoundedFabius) (hF : IsFabius F)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    fabiusLaplaceMoment F 0 ((a + b) / 2) ^ 2 ≤
      fabiusLaplaceMoment F 0 a * fabiusLaplaceMoment F 0 b :=
  fabiusLaplaceMoment_midpoint_sq_le_all F hF a b

/-- Trading powers of the variable for any positive amount subtracted from
the tilt, for the moments of any bounded Fabius candidate. -/
theorem fabiusLaplaceMoment_le_of_tilt_sub
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (s : ℝ) {a : ℝ} (ha : 0 < a) :
    fabiusLaplaceMoment F k s ≤
      ((1 / a) ^ k * (k.factorial : ℝ)) *
        fabiusLaplaceMoment F 0 (s - a) := by
  simpa only [
    ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
      F hF] using
    unitLaplaceMoment_le_of_tilt_sub
      ProbabilityRepresentation.weightedSumDistribution k s ha

/-- Compatibility name for trading powers for a positive amount of tilt in a
Fabius Laplace moment. -/
theorem fabiusLaplaceMoment_le_shift
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ)
    {s a : ℝ} (ha : 0 < a) :
    fabiusLaplaceMoment F k s ≤
      ((1 / a) ^ k * (k.factorial : ℝ)) *
        fabiusLaplaceMoment F 0 (s - a) :=
  fabiusLaplaceMoment_le_of_tilt_sub F hF k s ha

end Fabius
