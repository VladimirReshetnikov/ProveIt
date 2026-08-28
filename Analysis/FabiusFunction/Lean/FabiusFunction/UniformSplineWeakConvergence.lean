import FabiusFunction.FabiusUniformSpline
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Weak convergence of the finite spline laws

The umbrella gap register's *Uniform CDF control and weak convergence*
candidate compares the uniform estimate `|C_p - F| ≤ 2^{-p}` (public as
`abs_uniformCenteredPartialCDF_sub_fabiusReal_le` in
`FabiusComputability`) with the qualitative statement it strengthens:
the translated finite laws converge weakly to the random-series law.
This module supplies that qualitative statement, discharging the
register's obligation.

`uniformCenteredPartialLaw p` bundles the candidate's measure `μ_p` —
the law of the first `p` weighted uniform coordinates translated right
by `2^{-p-1}` — as a probability measure, and its CDF is identified
with the midpoint-corrected finite CDF `C_p`.  Weak convergence is
proved by Lévy's continuity theorem: the characteristic functions
converge pointwise by dominated convergence, because the partial sums
of the random series converge pointwise on the sample space and the
integrands all lie on the unit circle.  No rate enters the qualitative
statement; the `2^{-p}` rate lives in the CDF bound above, which is
strictly finer information than the limit alone.

* `tendsto_uniformPartialSum` — pointwise convergence of the partial
  sums to the random series on the sample space.
* `tendsto_charFun_uniformPartialDistribution` — characteristic
  functions of the finite laws converge to that of the limit law.
* `uniformCenteredPartialLaw` — the translated finite law, with its
  probability instance and CDF identification
  `cdf_uniformCenteredPartialLaw`.
* `uniformCenteredPartialLaw_tendsto` — weak convergence of the
  translated finite laws to the random-series law.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Complex Set Filter Topology

namespace Fabius
namespace ProbabilityRepresentation

/-! ## Pointwise convergence of the partial sums -/

/-- The summand family of the random series is summable at every sample
point: the coordinates lie in `[0,1]`, so the geometric envelope
`(1/2)·(1/2)^n` dominates. -/
lemma summable_uniformCoordinate (ω : SampleSpace) :
    Summable (fun n : ℕ => (ω n : ℝ) / 2 / 2 ^ n) := by
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (div_nonneg (ω n).2.1 (by norm_num)) (by positivity))
    (fun n => ?_) (summable_geometric_two.mul_left (1 / 2))
  have h1 : (ω n : ℝ) ≤ 1 := (ω n).2.2
  have hEq : (1 : ℝ) / 2 * (1 / 2) ^ n = 1 / (2 * 2 ^ n) := by
    rw [div_pow, one_pow, div_mul_div_comm, one_mul]
  rw [div_div, hEq]
  gcongr

/-- **The finite partial sums converge to the random series** at every
sample point. -/
theorem tendsto_uniformPartialSum (ω : SampleSpace) :
    Tendsto (fun p => uniformPartialSum p ω) atTop
      (𝓝 (weightedCoordinateSum ω)) := by
  have h := (summable_uniformCoordinate ω).hasSum.tendsto_sum_nat
  simpa [uniformPartialSum, weightedCoordinateSum] using h

/-! ## Convergence of the characteristic functions -/

/-- The characteristic function of a pushforward from the sample space,
written as a sample-space integral of a unit-circle integrand. -/
private lemma charFun_map_sampleSpace (S : SampleSpace → ℝ)
    (hS : Measurable S) (t : ℝ) :
    charFun (uniformProduct.map S) t =
      ∫ ω, cexp ((t : ℂ) * (S ω : ℝ) * I) ∂uniformProduct := by
  rw [charFun_apply_real,
    integral_map hS.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => cexp ((t : ℂ) * (x : ℝ) * I))
          (uniformProduct.map S) from
        (Complex.measurable_exp.comp
          ((Complex.measurable_ofReal.const_mul (t : ℂ)).mul_const
            I)).aestronglyMeasurable)]

/-- **The characteristic functions of the finite laws converge
pointwise** to that of the random-series law, by dominated convergence:
the integrands lie on the unit circle and converge pointwise with the
partial sums. -/
theorem tendsto_charFun_uniformPartialDistribution (t : ℝ) :
    Tendsto (fun p => charFun (uniformPartialDistribution p) t) atTop
      (𝓝 (charFun weightedSumDistribution t)) := by
  have hrw : ∀ p, charFun (uniformPartialDistribution p) t =
      ∫ ω, cexp ((t : ℂ) * (uniformPartialSum p ω : ℝ) * I)
        ∂uniformProduct :=
    fun p => charFun_map_sampleSpace _ (measurable_uniformPartialSum p) t
  have hrw' : charFun weightedSumDistribution t =
      ∫ ω, cexp ((t : ℂ) * (weightedCoordinateSum ω : ℝ) * I)
        ∂uniformProduct :=
    charFun_map_sampleSpace _ measurable_weightedCoordinateSum t
  simp only [hrw, hrw']
  have hcont : Continuous fun s : ℝ => cexp ((t : ℂ) * (s : ℝ) * I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.const_mul (t : ℂ)).mul_const I)
  refine tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun p => (Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp
        (measurable_uniformPartialSum p)).const_mul (t : ℂ)).mul_const
          I)).aestronglyMeasurable)
    (integrable_const 1) (fun p => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => ?_)
  · exact le_of_eq (by rw [mul_comm ((t : ℂ)) _, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal_mul_I])
  · exact ((hcont.tendsto _).comp (tendsto_uniformPartialSum ω)).congr
      fun p => rfl

/-! ## The translated finite laws -/

/-- The candidate's measure `μ_p`: the law of the first `p` weighted
uniform coordinates, translated right by the midpoint correction
`2^{-p-1}`. -/
noncomputable def uniformCenteredPartialLaw (p : ℕ) : Measure ℝ :=
  (uniformPartialDistribution p).map (· + 1 / 2 ^ (p + 1))

instance (p : ℕ) : IsProbabilityMeasure (uniformCenteredPartialLaw p) :=
  Measure.isProbabilityMeasure_map (measurable_id.add_const _).aemeasurable

/-- **The CDF of the translated finite law is the midpoint-corrected
finite CDF** `C_p`: translation shifts the CDF's threshold. -/
theorem cdf_uniformCenteredPartialLaw (p : ℕ) (x : ℝ) :
    ProbabilityTheory.cdf (uniformCenteredPartialLaw p) x =
      uniformCenteredPartialCDF p x := by
  have hpre : (fun a : ℝ => a + 1 / 2 ^ (p + 1)) ⁻¹' Iic x =
      Iic (x - 1 / 2 ^ (p + 1)) := by
    ext a
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro h <;> linarith
  have hL : ProbabilityTheory.cdf (uniformCenteredPartialLaw p) x =
      (uniformPartialDistribution p).real (Iic (x - 1 / 2 ^ (p + 1))) := by
    rw [ProbabilityTheory.cdf_eq_real, uniformCenteredPartialLaw,
      map_measureReal_apply
        (show Measurable fun a : ℝ => a + 1 / 2 ^ (p + 1) from
          measurable_id.add_const _)
        measurableSet_Iic,
      hpre]
  have hR : uniformCenteredPartialCDF p x =
      (uniformPartialDistribution p).real (Iic (x - 1 / 2 ^ (p + 1))) := by
    show ProbabilityTheory.cdf (uniformPartialDistribution p)
        (x - 1 / 2 ^ (p + 1)) = _
    rw [ProbabilityTheory.cdf_eq_real]
  rw [hL, hR]

/-- The characteristic functions of the translated laws also converge:
the translation contributes a unit-circle factor `e^{iδ_p t}` with
`δ_p = 2^{-p-1} → 0`. -/
theorem tendsto_charFun_uniformCenteredPartialLaw (t : ℝ) :
    Tendsto (fun p => charFun (uniformCenteredPartialLaw p) t) atTop
      (𝓝 (charFun weightedSumDistribution t)) := by
  have hδ : Tendsto (fun p : ℕ => (1 : ℝ) / 2 ^ (p + 1)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    have hshift := h.comp (tendsto_add_atTop_nat 1)
    refine hshift.congr fun p => ?_
    show ((1 : ℝ) / 2) ^ (p + 1) = 1 / 2 ^ (p + 1)
    rw [div_pow, one_pow]
  have hcont : Continuous fun s : ℝ => cexp (((s * t : ℝ) : ℂ) * I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_id.mul continuous_const)).mul_const I)
  have hexp : Tendsto
      (fun p : ℕ => cexp (((1 / 2 ^ (p + 1) * t : ℝ) : ℂ) * I)) atTop
      (𝓝 1) := by
    have h := (hcont.tendsto 0).comp hδ
    simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero] at h
    exact h.congr fun p => rfl
  have hfactor : ∀ p, charFun (uniformCenteredPartialLaw p) t =
      charFun (uniformPartialDistribution p) t *
        cexp (((1 / 2 ^ (p + 1) * t : ℝ) : ℂ) * I) := by
    intro p
    rw [uniformCenteredPartialLaw, charFun_map_add_const]
    simp only [Real.inner_apply]
  simp only [hfactor]
  simpa using (tendsto_charFun_uniformPartialDistribution t).mul hexp

/-! ## Weak convergence -/

/-- The translated finite law, bundled as a point of the space of
probability measures on `ℝ` with its weak topology. -/
noncomputable def uniformCenteredPartialProbability (p : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨uniformCenteredPartialLaw p, inferInstance⟩

/-- The random-series law, bundled as a point of the space of
probability measures on `ℝ` with its weak topology. -/
noncomputable def weightedSumProbability : ProbabilityMeasure ℝ :=
  ⟨weightedSumDistribution, inferInstance⟩

/-- **Weak convergence of the finite spline laws** (the gap register's
candidate, qualitative half): the translated finite laws `μ_p` converge
to the random-series law in the topology of weak convergence of
probability measures.  By Lévy's continuity theorem it suffices that
the characteristic functions converge pointwise, which is
`tendsto_charFun_uniformCenteredPartialLaw`.  The quantitative half —
the all-real uniform CDF bound `|C_p - F| ≤ 2^{-p}` — is
`abs_uniformCenteredPartialCDF_sub_fabiusReal_le` in
`FabiusComputability`, and is strictly finer information than the
unquantified limit. -/
theorem uniformCenteredPartialLaw_tendsto :
    Tendsto uniformCenteredPartialProbability atTop
      (𝓝 weightedSumProbability) := by
  exact MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun
    fun t => tendsto_charFun_uniformCenteredPartialLaw t

end ProbabilityRepresentation
end Fabius
