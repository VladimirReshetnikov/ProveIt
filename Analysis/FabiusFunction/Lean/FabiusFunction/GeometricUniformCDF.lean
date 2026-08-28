import FabiusFunction.ContinuousCDF
import FabiusFunction.GeometricUniformLaw
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# CDF and density of the geometric uniform law

For `|q| < 1`, let `F_q` be the CDF of the random series with weights
`(1 - q) q^n`.  This module proves continuity and reflection of `F_q`.
On the probability range `0 ≤ q < 1` it proves the exact exterior values.
For `0 < q < 1` it then derives the conditioning integral, its ordinary
interval-integral form, and the resulting continuous nonnegative density.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff unitInterval

namespace Fabius
namespace ProbabilityRepresentation

set_option autoImplicit false
noncomputable section

/-- The cumulative distribution function of the geometric uniform law.

The definition is total in `q`.  Its interpretation as the ordinary CDF
of a probability law is established below under `|q| < 1`. -/
def geometricUniformCDF (q x : ℝ) : ℝ :=
  cdf (geometricUniformDistribution q) x

/-- Every geometric-uniform CDF is monotone. -/
theorem monotone_geometricUniformCDF (q : ℝ) :
    Monotone (geometricUniformCDF q) :=
  ProbabilityTheory.monotone_cdf (geometricUniformDistribution q)

/-- Every geometric-uniform CDF is nonnegative. -/
theorem geometricUniformCDF_nonneg (q x : ℝ) :
    0 ≤ geometricUniformCDF q x :=
  ProbabilityTheory.cdf_nonneg (geometricUniformDistribution q) x

/-- Every geometric-uniform CDF is at most one. -/
theorem geometricUniformCDF_le_one (q x : ℝ) :
    geometricUniformCDF q x ≤ 1 :=
  ProbabilityTheory.cdf_le_one (geometricUniformDistribution q) x

/-- The geometric-uniform CDF is measurable for every real parameter. -/
theorem measurable_geometricUniformCDF (q : ℝ) :
    Measurable (geometricUniformCDF q) := by
  exact (ProbabilityTheory.monotone_cdf
    (geometricUniformDistribution q)).measurable

/-- The geometric-uniform CDF is continuous whenever `|q| < 1`. -/
theorem continuous_geometricUniformCDF
    {q : ℝ} (hq : |q| < 1) :
    Continuous (geometricUniformCDF q) := by
  letI : IsProbabilityMeasure (geometricUniformDistribution q) :=
    geometricUniformDistribution_isProbabilityMeasure hq
  letI : NullSingletonClass (geometricUniformDistribution q) :=
    geometricUniformDistribution_nullSingletonClass hq
  exact continuous_cdf_of_nullSingleton (geometricUniformDistribution q)

/-- Reflection of the geometric law gives
`F_q (1 - x) = 1 - F_q x`. -/
theorem geometricUniformCDF_reflection
    {q : ℝ} (hq : |q| < 1) (x : ℝ) :
    geometricUniformCDF q (1 - x) = 1 - geometricUniformCDF q x := by
  letI : IsProbabilityMeasure (geometricUniformDistribution q) :=
    geometricUniformDistribution_isProbabilityMeasure hq
  letI : NullSingletonClass (geometricUniformDistribution q) :=
    geometricUniformDistribution_nullSingletonClass hq
  exact cdf_reflection_sub (geometricUniformDistribution q)
    (geometricUniformDistribution_reflection hq) x

/-- Reflection fixes the value of every atomless geometric-uniform CDF at
the midpoint. -/
@[simp] theorem geometricUniformCDF_one_half
    {q : ℝ} (hq : |q| < 1) :
    geometricUniformCDF q (1 / 2) = 1 / 2 := by
  have h := geometricUniformCDF_reflection hq (1 / 2)
  norm_num at h ⊢
  linarith

/-- On the nonnegative probability range, `F_q` vanishes on the
nonpositive half-line. -/
theorem geometricUniformCDF_zero_of_nonpos
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {x : ℝ} (hx : x ≤ 0) :
    geometricUniformCDF q x = 0 := by
  have hq : |q| < 1 := by simpa only [abs_of_nonneg hq0] using hq1
  letI : IsProbabilityMeasure (geometricUniformDistribution q) :=
    geometricUniformDistribution_isProbabilityMeasure hq
  letI : NullSingletonClass (geometricUniformDistribution q) :=
    geometricUniformDistribution_nullSingletonClass hq
  rw [geometricUniformCDF, ProbabilityTheory.cdf_eq_real,
    ← measureReal_congr Iio_ae_eq_Iic]
  have hsubset : Iio x ⊆ (Icc (0 : ℝ) 1)ᶜ := by
    intro y hy
    simp only [mem_compl_iff, mem_Icc]
    intro hyIcc
    exact (not_lt_of_ge hyIcc.1) (hy.trans_le hx)
  apply measureReal_mono_null hsubset
  rw [measureReal_def, geometricUniformDistribution_compl_Icc hq0 hq1]
  simp only [ENNReal.toReal_zero]

/-- On the nonnegative probability range, `F_q` is one on the half-line
starting at one. -/
theorem geometricUniformCDF_one_of_one_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {x : ℝ} (hx : 1 ≤ x) :
    geometricUniformCDF q x = 1 := by
  have hq : |q| < 1 := by simpa only [abs_of_nonneg hq0] using hq1
  letI : IsProbabilityMeasure (geometricUniformDistribution q) :=
    geometricUniformDistribution_isProbabilityMeasure hq
  apply le_antisymm
  · exact ProbabilityTheory.cdf_le_one (geometricUniformDistribution q) x
  · rw [geometricUniformCDF, ProbabilityTheory.cdf_eq_real]
    calc
      1 = (geometricUniformDistribution q).real (Icc (0 : ℝ) 1) := by
        rw [measureReal_def, geometricUniformDistribution_Icc hq0 hq1]
        simp only [ENNReal.toReal_one]
      _ ≤ (geometricUniformDistribution q).real (Iic x) := by
        exact measureReal_mono (fun _y hy => hy.2.trans hx)
          (measure_ne_top _ _)

/-- Conditioning on the first uniform coordinate gives the all-real
refinement equation
`F_q x = ∫₀¹ F_q ((x - (1 - q) u) / q) du`.

Strict positivity of `q` is used only to solve the affine event inequality
for the independent tail variable.
-/
theorem geometricUniformCDF_eq_integral
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
    geometricUniformCDF q x =
      ∫ u : Icc (0 : ℝ) 1,
        geometricUniformCDF q ((x - (1 - q) * (u : ℝ)) / q) := by
  have hq : |q| < 1 := by simpa only [abs_of_pos hq0] using hq1
  letI : IsProbabilityMeasure (geometricUniformDistribution q) :=
    geometricUniformDistribution_isProbabilityMeasure hq
  let A : Set (Icc (0 : ℝ) 1 × ℝ) :=
    {p | (1 - q) * (p.1 : ℝ) + q * p.2 ≤ x}
  have hA : MeasurableSet A := by
    apply measurableSet_le
    · fun_prop
    · fun_prop
  have hcombine : Measurable
      (fun p : Icc (0 : ℝ) 1 × ℝ =>
        (1 - q) * (p.1 : ℝ) + q * p.2) := by
    fun_prop
  rw [geometricUniformCDF, ProbabilityTheory.cdf_eq_real,
    geometricUniformDistribution_selfSimilar hq,
    map_measureReal_apply hcombine measurableSet_Iic]
  change ((volume : Measure (Icc (0 : ℝ) 1)).prod
    (geometricUniformDistribution q)).real A = _
  calc
    ((volume : Measure (Icc (0 : ℝ) 1)).prod
        (geometricUniformDistribution q)).real A =
        ∫ p, A.indicator (fun _ => (1 : ℝ)) p
          ∂((volume : Measure (Icc (0 : ℝ) 1)).prod
            (geometricUniformDistribution q)) := by
      symm
      exact integral_indicator_one hA
    _ = ∫ u : Icc (0 : ℝ) 1,
        ∫ v : ℝ, A.indicator (fun _ => (1 : ℝ)) (u, v)
          ∂(geometricUniformDistribution q) := by
      apply integral_prod
      exact (integrable_const (1 : ℝ)).indicator hA
    _ = ∫ u : Icc (0 : ℝ) 1,
        geometricUniformCDF q ((x - (1 - q) * (u : ℝ)) / q) := by
      apply integral_congr_ae
      filter_upwards with u
      let Au : Set ℝ :=
        {v | (1 - q) * (u : ℝ) + q * v ≤ x}
      have hAu : MeasurableSet Au := by
        apply measurableSet_le <;> fun_prop
      calc
        (∫ v : ℝ, A.indicator (fun _ => (1 : ℝ)) (u, v)
            ∂(geometricUniformDistribution q)) =
            ∫ v : ℝ, Au.indicator (fun _ => (1 : ℝ)) v
              ∂(geometricUniformDistribution q) := by
          apply integral_congr_ae
          filter_upwards with v
          rfl
        _ = (geometricUniformDistribution q).real Au :=
          integral_indicator_one hAu
        _ = geometricUniformCDF q
            ((x - (1 - q) * (u : ℝ)) / q) := by
          rw [geometricUniformCDF, ProbabilityTheory.cdf_eq_real]
          have hset :
              Au = Iic ((x - (1 - q) * (u : ℝ)) / q) := by
            ext v
            simp only [Au, mem_setOf_eq, mem_Iic]
            rw [le_div_iff₀ hq0]
            constructor <;> intro hv <;> nlinarith
          rw [hset]

/-- The conditioning equation as an ordinary interval integral:
`F_q x = q / (1 - q) ∫_((x-(1-q))/q)^(x/q) F_q`. -/
theorem geometricUniformCDF_eq_intervalIntegral
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
    geometricUniformCDF q x =
      q / (1 - q) *
        ∫ t in ((x - (1 - q)) / q)..(x / q), geometricUniformCDF q t := by
  rw [geometricUniformCDF_eq_integral hq0 hq1]
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hone : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq1)
  have hc : q / (1 - q) ≠ 0 := div_ne_zero hqne hone
  have harg (u : ℝ) :
      (x - (1 - q) * u) / q = x / q - u / (q / (1 - q)) := by
    field_simp [hqne, hone]
  have hlower :
      x / q - 1 / (q / (1 - q)) = (x - (1 - q)) / q := by
    field_simp [hqne, hone]
  calc
    (∫ u : Icc (0 : ℝ) 1,
        geometricUniformCDF q ((x - (1 - q) * (u : ℝ)) / q)) =
        ∫ u in Icc (0 : ℝ) 1,
          geometricUniformCDF q ((x - (1 - q) * u) / q) := by
      simpa using (integral_subtype (G := ℝ) measurableSet_Icc
        (fun u : ℝ => geometricUniformCDF q
          ((x - (1 - q) * u) / q)))
    _ = ∫ u in (0 : ℝ)..1,
        geometricUniformCDF q ((x - (1 - q) * u) / q) := by
      rw [integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by norm_num)]
    _ = ∫ u in (0 : ℝ)..1,
        geometricUniformCDF q (x / q - u / (q / (1 - q))) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      change geometricUniformCDF q ((x - (1 - q) * u) / q) =
        geometricUniformCDF q (x / q - u / (q / (1 - q)))
      exact congrArg (geometricUniformCDF q) (harg u)
    _ = q / (1 - q) *
        ∫ t in ((x - (1 - q)) / q)..(x / q),
          geometricUniformCDF q t := by
      have hchange := intervalIntegral.integral_comp_sub_div
        (a := (0 : ℝ)) (b := 1) (f := geometricUniformCDF q)
        hc (x / q)
      rw [hlower] at hchange
      simpa only [zero_div, sub_zero, smul_eq_mul] using hchange

/-- The canonical density obtained by differentiating the positive-ratio
geometric-uniform refinement equation.  The definition is total in `q`, but
its density interpretation below requires `0 < q < 1`. -/
def geometricUniformDensity (q x : ℝ) : ℝ :=
  (geometricUniformCDF q (x / q) -
    geometricUniformCDF q ((x - (1 - q)) / q)) / (1 - q)

/-- For `0 < q < 1`, the geometric-uniform CDF has derivative
`geometricUniformDensity q` at every real point. -/
theorem geometricUniformCDF_hasDerivAt
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
    HasDerivAt (geometricUniformCDF q) (geometricUniformDensity q x) x := by
  have hq : |q| < 1 := by simpa only [abs_of_pos hq0] using hq1
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hone : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq1)
  have hcont : Continuous (geometricUniformCDF q) :=
    continuous_geometricUniformCDF hq
  let P : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, geometricUniformCDF q t
  have hP (z : ℝ) : HasDerivAt P (geometricUniformCDF q z) z := by
    dsimp only [P]
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 z)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcont.continuousAt
  have hrepr : geometricUniformCDF q = fun y : ℝ =>
      q / (1 - q) *
        (P (y / q) - P ((y - (1 - q)) / q)) := by
    funext y
    rw [geometricUniformCDF_eq_intervalIntegral hq0 hq1]
    change q / (1 - q) *
        (∫ t in ((y - (1 - q)) / q)..(y / q),
          geometricUniformCDF q t) =
      q / (1 - q) *
        ((∫ t in (0 : ℝ)..(y / q), geometricUniformCDF q t) -
          ∫ t in (0 : ℝ)..((y - (1 - q)) / q),
            geometricUniformCDF q t)
    rw [intervalIntegral.integral_interval_sub_left
      (hcont.intervalIntegrable 0 (y / q))
      (hcont.intervalIntegrable 0 ((y - (1 - q)) / q))]
  rw [hrepr]
  have hu := (hP (x / q)).comp x ((hasDerivAt_id x).div_const q)
  have hl := (hP ((x - (1 - q)) / q)).comp x
    (((hasDerivAt_id x).sub_const (1 - q)).div_const q)
  have hder := (hu.sub hl).const_mul (q / (1 - q))
  have hcoef :
      q / (1 - q) *
          (geometricUniformCDF q (x / q) * (1 / q) -
            geometricUniformCDF q ((x - (1 - q)) / q) * (1 / q)) =
        geometricUniformDensity q x := by
    rw [geometricUniformDensity]
    field_simp [hqne, hone]
  simpa only [Function.comp_apply, id_eq, Pi.sub_apply, hcoef] using hder

/-- The pointwise derivative formula for the geometric-uniform CDF. -/
theorem deriv_geometricUniformCDF
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
    deriv (geometricUniformCDF q) x = geometricUniformDensity q x :=
  (geometricUniformCDF_hasDerivAt hq0 hq1 x).deriv

/-- The geometric-uniform density is continuous for `0 < q < 1`. -/
theorem continuous_geometricUniformDensity
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Continuous (geometricUniformDensity q) := by
  have hq : |q| < 1 := by simpa only [abs_of_pos hq0] using hq1
  change Continuous (fun x : ℝ =>
    (geometricUniformCDF q (x / q) -
      geometricUniformCDF q ((x - (1 - q)) / q)) / (1 - q))
  exact (((continuous_geometricUniformCDF hq).comp (by fun_prop)).sub
    ((continuous_geometricUniformCDF hq).comp (by fun_prop))).div_const (1 - q)

/-- The geometric-uniform density is nonnegative for `0 < q < 1`. -/
theorem geometricUniformDensity_nonneg
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
    0 ≤ geometricUniformDensity q x := by
  rw [geometricUniformDensity]
  apply div_nonneg
  · apply sub_nonneg.mpr
    apply monotone_geometricUniformCDF q
    apply (div_le_div_iff_of_pos_right hq0).2
    linarith
  · exact sub_nonneg.mpr hq1.le

/-- The positive-ratio geometric-uniform density vanishes on the
nonpositive half-line. -/
@[simp] theorem geometricUniformDensity_zero_of_nonpos
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {x : ℝ} (hx : x ≤ 0) :
    geometricUniformDensity q x = 0 := by
  have hupper : x / q ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hx hq0.le
  have hlower : (x - (1 - q)) / q ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hq0.le
  rw [geometricUniformDensity,
    geometricUniformCDF_zero_of_nonpos hq0.le hq1 hupper,
    geometricUniformCDF_zero_of_nonpos hq0.le hq1 hlower]
  simp

/-- The positive-ratio geometric-uniform density vanishes on the half-line
starting at one. -/
@[simp] theorem geometricUniformDensity_zero_of_one_le
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {x : ℝ} (hx : 1 ≤ x) :
    geometricUniformDensity q x = 0 := by
  have hupper : 1 ≤ x / q := by
    apply (le_div_iff₀ hq0).2
    linarith
  have hlower : 1 ≤ (x - (1 - q)) / q := by
    apply (le_div_iff₀ hq0).2
    linarith
  rw [geometricUniformDensity,
    geometricUniformCDF_one_of_one_le hq0.le hq1 hupper,
    geometricUniformCDF_one_of_one_le hq0.le hq1 hlower,
    sub_self, zero_div]

/-- The ordinary support of the positive-ratio density is contained in the
open unit interval. -/
theorem support_geometricUniformDensity_subset_Ioo
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Function.support (geometricUniformDensity q) ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  constructor
  · by_contra hnonneg
    exact hx (geometricUniformDensity_zero_of_nonpos hq0 hq1
      (le_of_not_gt hnonneg))
  · by_contra hlt
    exact hx (geometricUniformDensity_zero_of_one_le hq0 hq1
      (le_of_not_gt hlt))

/-- The ordinary support of the positive-ratio density is contained in the
closed unit interval. -/
theorem support_geometricUniformDensity_subset_Icc
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Function.support (geometricUniformDensity q) ⊆ Icc (0 : ℝ) 1 :=
  (support_geometricUniformDensity_subset_Ioo hq0 hq1).trans
    Ioo_subset_Icc_self

/-- The topological support of the positive-ratio density is contained in
the closed unit interval. -/
theorem tsupport_geometricUniformDensity_subset_Icc
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    tsupport (geometricUniformDensity q) ⊆ Icc (0 : ℝ) 1 := by
  change closure (Function.support (geometricUniformDensity q)) ⊆
    Icc (0 : ℝ) 1
  exact closure_minimal
    (support_geometricUniformDensity_subset_Icc hq0 hq1) isClosed_Icc

/-- The positive-ratio geometric-uniform density has compact support. -/
theorem geometricUniformDensity_hasCompactSupport
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasCompactSupport (geometricUniformDensity q) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_geometricUniformDensity_subset_Icc hq0 hq1)

/-- Reflection about `1 / 2` makes the positive-ratio density symmetric. -/
theorem geometricUniformDensity_reflection
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
    geometricUniformDensity q (1 - x) = geometricUniformDensity q x := by
  have hq : |q| < 1 := by simpa only [abs_of_pos hq0] using hq1
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hupper :
      (1 - x) / q = 1 - (x - (1 - q)) / q := by
    field_simp [hqne]
    ring
  have hlower :
      ((1 - x) - (1 - q)) / q = 1 - x / q := by
    field_simp [hqne]
    ring
  rw [geometricUniformDensity, hupper, hlower,
    geometricUniformCDF_reflection hq,
    geometricUniformCDF_reflection hq,
    geometricUniformDensity]
  ring

/-- For `0 < q < 1`, the geometric-uniform law is Lebesgue measure with
the explicit continuous density `geometricUniformDensity q`. -/
theorem geometricUniformDistribution_eq_withDensity
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    geometricUniformDistribution q =
      (volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (geometricUniformDensity q x)) := by
  have hq : |q| < 1 := by simpa only [abs_of_pos hq0] using hq1
  letI : IsProbabilityMeasure (geometricUniformDistribution q) :=
    geometricUniformDistribution_isProbabilityMeasure hq
  apply measure_eq_withDensity_of_cdf_hasDerivAt
    (geometricUniformDistribution q) (geometricUniformDensity q)
  intro x
  change HasDerivAt (geometricUniformCDF q)
    (geometricUniformDensity q x) x
  exact geometricUniformCDF_hasDerivAt hq0 hq1 x

/-- For `0 < q < 1`, the geometric-uniform CDF is smooth of every finite
order.  The proof bootstraps the explicit affine derivative refinement and
does not use Fourier inversion. -/
theorem contDiff_geometricUniformCDF
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ContDiff ℝ ∞ (geometricUniformCDF q) := by
  have hdifferentiable : Differentiable ℝ (geometricUniformCDF q) :=
    fun x => (geometricUniformCDF_hasDerivAt hq0 hq1 x).differentiableAt
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hdifferentiable.continuous
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiff_succ_iff_deriv]
      refine ⟨hdifferentiable, by simp, ?_⟩
      have hderiv : deriv (geometricUniformCDF q) =
          geometricUniformDensity q := by
        funext x
        exact deriv_geometricUniformCDF hq0 hq1 x
      rw [hderiv]
      change ContDiff ℝ n (fun x : ℝ =>
        (geometricUniformCDF q (x / q) -
          geometricUniformCDF q ((x - (1 - q)) / q)) / (1 - q))
      exact ((ih.comp (contDiff_id.div_const q)).sub
        (ih.comp ((contDiff_id.sub contDiff_const).div_const q))).div_const (1 - q)

/-- For `0 < q < 1`, the explicit geometric-uniform density is smooth. -/
theorem contDiff_geometricUniformDensity
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ContDiff ℝ ∞ (geometricUniformDensity q) := by
  have hF := contDiff_geometricUniformCDF hq0 hq1
  change ContDiff ℝ ∞ (fun x : ℝ =>
    (geometricUniformCDF q (x / q) -
      geometricUniformCDF q ((x - (1 - q)) / q)) / (1 - q))
  exact ((hF.comp (contDiff_id.div_const q)).sub
    (hF.comp ((contDiff_id.sub contDiff_const).div_const q))).div_const (1 - q)

end
end ProbabilityRepresentation
end Fabius
