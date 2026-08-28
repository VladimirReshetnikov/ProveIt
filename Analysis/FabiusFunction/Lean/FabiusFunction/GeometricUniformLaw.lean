import FabiusFunction.WeightedUniformDistribution
import FabiusFunction.WeightedUniformSupport

/-!
# Geometrically weighted uniform-coordinate laws

For a real parameter `q`, this file specializes the general weighted
uniform-coordinate construction to

`w q n = (1 - q) * q ^ n`.

The definitions are total in `q`.  Absolute convergence, affine
self-similarity, reflection, and support as the exact series range use the
natural hypothesis `|q| < 1`; nonnegativity, concentration, and exact
interval support `[0,1]` use `0 ≤ q < 1`.  In particular, the foundational
law includes the endpoint `q = 0`.  Strict positivity is needed only by later
density and CDF-change-of-variables arguments.
-/

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval

namespace Fabius
namespace ProbabilityRepresentation

set_option autoImplicit false
noncomputable section

/-! ## Geometric weights -/

/-- The normalized geometric weight sequence with ratio `q`. -/
def geometricUniformWeight (q : ℝ) (n : ℕ) : ℝ :=
  (1 - q) * q ^ n

/-- The first normalized geometric weight. -/
@[simp] theorem geometricUniformWeight_zero (q : ℝ) :
    geometricUniformWeight q 0 = 1 - q := by
  simp only [geometricUniformWeight, pow_zero, mul_one]

/-- Shifting the geometric weight sequence scales it by `q`. -/
@[simp] theorem geometricUniformWeight_succ (q : ℝ) (n : ℕ) :
    geometricUniformWeight q (Nat.succ n) =
      q * geometricUniformWeight q n := by
  simp only [geometricUniformWeight, pow_succ]
  ring

/-- For `|q| < 1`, the normalized geometric weights sum to one. -/
theorem hasSum_geometricUniformWeight
    {q : ℝ} (hq : |q| < 1) :
    HasSum (geometricUniformWeight q) 1 := by
  change HasSum (fun n : ℕ => (1 - q) * q ^ n) 1
  have hq1 : q < 1 := (abs_lt.mp hq).2
  have hne : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq1)
  have h := (hasSum_geometric_of_abs_lt_one hq).mul_left (1 - q)
  rw [mul_inv_cancel₀ hne] at h
  exact h

/-- The norms of the normalized geometric weights are summable whenever
`|q| < 1`. -/
theorem summable_norm_geometricUniformWeight
    {q : ℝ} (hq : |q| < 1) :
    Summable fun n => ‖geometricUniformWeight q n‖ := by
  have h := (summable_geometric_of_lt_one (abs_nonneg q) hq).mul_left |1 - q|
  simpa only [geometricUniformWeight, Real.norm_eq_abs, abs_mul, abs_pow] using h

/-- The geometric weights are nonnegative on the probability range
`0 ≤ q < 1`. -/
theorem geometricUniformWeight_nonneg
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    0 ≤ geometricUniformWeight q n := by
  exact mul_nonneg (sub_nonneg.mpr hq1.le) (pow_nonneg hq0 n)

/-! ## The random series -/

/-- The normalized geometrically weighted uniform-coordinate series. -/
noncomputable def geometricUniformSeries (q : ℝ) : SampleSpace → ℝ :=
  weightedUniformSeries (geometricUniformWeight q)

/-- The geometric uniform series is continuous for `|q| < 1`. -/
theorem continuous_geometricUniformSeries
    {q : ℝ} (hq : |q| < 1) :
    Continuous (geometricUniformSeries q) :=
  continuous_weightedUniformSeries (summable_norm_geometricUniformWeight hq)

/-- The geometric uniform series is measurable for `|q| < 1`. -/
theorem measurable_geometricUniformSeries
    {q : ℝ} (hq : |q| < 1) :
    Measurable (geometricUniformSeries q) :=
  measurable_weightedUniformSeries (summable_norm_geometricUniformWeight hq)

/-- Splitting off the first coordinate gives the affine recurrence
`X q = (1 - q) U₀ + q X q'`. -/
theorem geometricUniformSeries_split
    {q : ℝ} (hq : |q| < 1) (ω : SampleSpace) :
    geometricUniformSeries q ω =
      (1 - q) * (ω 0 : ℝ) + q * geometricUniformSeries q (tail ω) := by
  change weightedUniformSeries (geometricUniformWeight q) ω =
    (1 - q) * (ω 0 : ℝ) +
      q * weightedUniformSeries (geometricUniformWeight q) (tail ω)
  rw [weightedUniformSeries_split (summable_norm_geometricUniformWeight hq)]
  have htail :
      (fun n => geometricUniformWeight q (Nat.succ n)) =
        fun n => q • geometricUniformWeight q n := by
    funext n
    simp only [geometricUniformWeight_succ, smul_eq_mul]
  rw [htail, weightedUniformSeries_smul_weights]
  simp only [geometricUniformWeight, pow_zero, mul_one, smul_eq_mul]
  ring

/-- Reflecting all coordinates sends the geometric series to `1 - X`. -/
theorem geometricUniformSeries_reflect
    {q : ℝ} (hq : |q| < 1) (ω : SampleSpace) :
    geometricUniformSeries q (reflectCoordinates ω) =
      1 - geometricUniformSeries q ω := by
  change weightedUniformSeries (geometricUniformWeight q)
      (reflectCoordinates ω) =
    1 - weightedUniformSeries (geometricUniformWeight q) ω
  rw [weightedUniformSeries_reflect
    (summable_norm_geometricUniformWeight hq) ω,
    (hasSum_geometricUniformWeight hq).tsum_eq]

/-- For `0 ≤ q < 1`, the geometric series lies pointwise in the unit
interval. -/
theorem geometricUniformSeries_mem_Icc
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (ω : SampleSpace) :
    geometricUniformSeries q ω ∈ Icc (0 : ℝ) 1 := by
  have hq : |q| < 1 := by simpa only [abs_of_nonneg hq0] using hq1
  exact weightedUniformSeries_mem_unitInterval
    (summable_norm_geometricUniformWeight hq)
    (geometricUniformWeight_nonneg hq0 hq1)
    (hasSum_geometricUniformWeight hq).tsum_eq ω

/-! ## The probability law -/

/-- The pushforward law of the geometric uniform series. -/
noncomputable def geometricUniformDistribution (q : ℝ) : Measure ℝ :=
  weightedUniformDistribution (geometricUniformWeight q)

/-- For `|q| < 1`, the geometric pushforward is a probability measure. -/
theorem geometricUniformDistribution_isProbabilityMeasure
    {q : ℝ} (hq : |q| < 1) :
    IsProbabilityMeasure (geometricUniformDistribution q) := by
  exact weightedUniformDistribution_isProbabilityMeasure
    (summable_norm_geometricUniformWeight hq)

/-- The first coordinate and an independent copy of the full geometric
series have their product law. -/
theorem uniformProduct_map_head_tail_geometricUniformSeries
    {q : ℝ} (hq : |q| < 1) :
    uniformProduct.map
        (fun ω : SampleSpace => (ω 0, geometricUniformSeries q (tail ω))) =
      (volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (geometricUniformDistribution q) := by
  simpa only [geometricUniformDistribution, weightedUniformDistribution,
    geometricUniformSeries] using
    uniformProduct_map_head_tail_function
      (geometricUniformSeries q) (measurable_geometricUniformSeries hq)

/-- The geometric law is the affine image of one uniform coordinate and
an independent copy of itself. -/
theorem geometricUniformDistribution_selfSimilar
    {q : ℝ} (hq : |q| < 1) :
    geometricUniformDistribution q =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (geometricUniformDistribution q)).map
          (fun p => (1 - q) * (p.1 : ℝ) + q * p.2) := by
  change uniformProduct.map (geometricUniformSeries q) =
    ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
      (uniformProduct.map (geometricUniformSeries q))).map
        (fun p => (1 - q) * (p.1 : ℝ) + q * p.2)
  have hjoint :
      uniformProduct.map
          (fun ω : SampleSpace => (ω 0, geometricUniformSeries q (tail ω))) =
        (volume : Measure (Set.Icc (0 : ℝ) 1)).prod
          (uniformProduct.map (geometricUniformSeries q)) := by
    simpa only [geometricUniformDistribution, weightedUniformDistribution,
      geometricUniformSeries] using
      uniformProduct_map_head_tail_geometricUniformSeries hq
  rw [← hjoint]
  rw [Measure.map_map (μ := uniformProduct)
    (f := fun ω : SampleSpace => (ω 0, geometricUniformSeries q (tail ω)))
    (g := fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
      (1 - q) * (p.1 : ℝ) + q * p.2)
    (by fun_prop)
    ((measurable_pi_apply 0).prodMk
      ((measurable_geometricUniformSeries hq).comp measurable_tail))]
  apply Measure.map_congr
  filter_upwards with ω
  exact geometricUniformSeries_split hq ω

/-- The geometric law is invariant under reflection about `1 / 2`. -/
theorem geometricUniformDistribution_reflection
    {q : ℝ} (hq : |q| < 1) :
    (geometricUniformDistribution q).map (fun x : ℝ => 1 - x) =
      geometricUniformDistribution q := by
  simpa only [geometricUniformDistribution,
    (hasSum_geometricUniformWeight hq).tsum_eq] using
    (weightedUniformDistribution_reflection
      (summable_norm_geometricUniformWeight hq))

/-- For `0 ≤ q < 1`, the geometric law is concentrated on `[0,1]`. -/
theorem geometricUniformDistribution_Icc
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    geometricUniformDistribution q (Icc (0 : ℝ) 1) = 1 := by
  have hq : |q| < 1 := by simpa only [abs_of_nonneg hq0] using hq1
  exact weightedUniformDistribution_unitInterval
    (summable_norm_geometricUniformWeight hq)
    (geometricUniformWeight_nonneg hq0 hq1)
    (hasSum_geometricUniformWeight hq).tsum_eq

/-- For `0 ≤ q < 1`, the geometric law gives no mass to the complement
of `[0,1]`. -/
theorem geometricUniformDistribution_compl_Icc
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    geometricUniformDistribution q ((Icc (0 : ℝ) 1)ᶜ) = 0 := by
  have hq : |q| < 1 := by simpa only [abs_of_nonneg hq0] using hq1
  exact weightedUniformDistribution_compl_unitInterval
    (summable_norm_geometricUniformWeight hq)
    (geometricUniformWeight_nonneg hq0 hq1)
    (hasSum_geometricUniformWeight hq).tsum_eq

/-- For every `|q| < 1`, the topological support of the geometric law is
exactly the range of its geometric coordinate series.  This structural form
also covers negative geometric ratios, whose range need not be an interval
with endpoints `0` and `1`. -/
theorem geometricUniformDistribution_support_eq_range
    {q : ℝ} (hq : |q| < 1) :
    (geometricUniformDistribution q).support =
      Set.range (geometricUniformSeries q) := by
  simpa only [geometricUniformDistribution, geometricUniformSeries] using
    (weightedUniformDistribution_support_eq_range
      (w := geometricUniformWeight q) (summable_norm_geometricUniformWeight hq))

/-- For `0 ≤ q < 1`, the topological support of the geometric law is exactly
the full unit interval. -/
theorem geometricUniformDistribution_support_eq_Icc
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (geometricUniformDistribution q).support = Icc (0 : ℝ) 1 := by
  have hq : |q| < 1 := by simpa only [abs_of_nonneg hq0] using hq1
  simpa only [geometricUniformDistribution] using
    (weightedUniformDistribution_support_eq_unitInterval
      (summable_norm_geometricUniformWeight hq)
      (geometricUniformWeight_nonneg hq0 hq1)
      (hasSum_geometricUniformWeight hq).tsum_eq)

end

end ProbabilityRepresentation
end Fabius
