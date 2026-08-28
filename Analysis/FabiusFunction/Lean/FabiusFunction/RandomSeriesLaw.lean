import FabiusFunction.MeasureRefinement
import FabiusFunction.ProbabilityRepresentation

/-!
# The up-measure is the law of the dyadic random series

Two probabilistic descriptions of the Fabius–Rvachev system coexist in
this library.  `ProbabilityRepresentation` constructs the random series
`X = ∑ U_k 2^{-k-1}` of independent uniform digits on a genuine product
sample space and identifies its cumulative distribution function with
the Fabius function; `MeasureRefinement` works with the density measure
`μ_up = up · Leb` and proves its refinement equation by characteristic
functions.  This module supplies the missing bridge: **`μ_up` is the
pushforward of the law of `X` under the affine map `x ↦ 2x - 1`**.

The proof is the fundamental theorem of calculus in disguise.  The
folded global derivative `F'(x) = 2·up(2x-1)` says exactly that
`y ↦ F((y+1)/2)` is an antiderivative of `up`, so both measures give
the interval `(-∞, y]` the mass `F((y+1)/2)`, and finite measures
agreeing on all such intervals are equal.

With the bridge in hand, the refinement equation transfers to the
random series itself, producing its **equality-in-law splitting**
`X ≗ (U + X')/2` — the drafts' random-variable identity `eq:random-tail`
in measure form, with the uniform digit made explicit — and the closed
form of the characteristic function of `X`.

* `hasDerivAt_fabiusReal_half_shift` — `y ↦ F((y+1)/2)` has derivative
  `up y` everywhere.
* `setIntegral_rvachevUp_Iic` / `rvachevMeasure_Iic` — the CDF of the
  up-measure is `F((y+1)/2)`.
* `weightedSumDistribution_Iic` — the CDF of the random series in
  `ℝ≥0∞` form.
* `rvachevMeasure_eq_map_weightedSum` — the bridge
  `μ_up = law(X) ∘ (2·-1)⁻¹`, with inverse form
  `weightedSum_eq_map_rvachevMeasure`.
* `charFun_weightedSum_eq_rvachev`, `charFun_weightedSumDistribution` —
  `E[e^{itX}] = e^{it/2}·Φ̂(t/2)`, and its closed form through the
  Rvachev Fourier transform.
* `weightedSumDistribution_self_similar` — the splitting law
  `law(X) = ((Uniform[0,1] ∗ law(X)) ∘ (·/2)⁻¹`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Complex Real Set Filter

namespace Fabius

open ProbabilityRepresentation

/-! ## The antiderivative of the up-function -/

/-- **`y ↦ F((y+1)/2)` is a global antiderivative of the up-function.**
This is the folded derivative identity `F'(x) = 2·up(2x-1)` of
`fabius_hasDerivAt` composed with the affine substitution: the factor
`2` is eaten by the inner derivative `1/2`, and the argument
`2·((y+1)/2) - 1` collapses to `y`. -/
theorem hasDerivAt_fabiusReal_half_shift (F : BoundedFabius)
    (hF : IsFabius F) (y : ℝ) :
    HasDerivAt (fun z : ℝ => fabiusReal F ((z + 1) / 2)) (rvachevUp F y) y := by
  have hinner : HasDerivAt (fun z : ℝ => (z + 1) / 2) (2⁻¹) y := by
    simpa using ((hasDerivAt_id y).add_const (1 : ℝ)).div_const 2
  have h := (fabius_hasDerivAt F hF ((y + 1) / 2)).comp y hinner
  have harg : 2 * ((y + 1) / 2) - 1 = y := by ring
  rw [harg] at h
  have hval : 2 * rvachevUp F y * 2⁻¹ = rvachevUp F y := by ring
  rw [hval] at h
  exact h

/-- **The left tail integral of the up-function** is the Fabius function
at the rescaled argument: `∫_{-∞}^y up = F((y+1)/2)`.  Below the
support both sides vanish; on the support this is the fundamental
theorem of calculus for the antiderivative above. -/
theorem setIntegral_rvachevUp_Iic (F : BoundedFabius) (hF : IsFabius F)
    (y : ℝ) :
    ∫ t in Iic y, rvachevUp F t = fabiusReal F ((y + 1) / 2) := by
  rcases le_or_gt y (-1) with hy | hy
  · have hzero : EqOn (rvachevUp F) (fun _ => (0 : ℝ)) (Iic y) := fun t ht =>
      rvachevUp_eq_zero_of_le_neg_one F hF (le_trans ht hy)
    rw [setIntegral_congr_fun measurableSet_Iic hzero, integral_zero,
      hF.zero_of_nonpos _ (by linarith)]
  · have hsplit : Iic y = Iic (-1 : ℝ) ∪ Ioc (-1 : ℝ) y :=
      (Iic_union_Ioc_eq_Iic hy.le).symm
    have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioc (-1 : ℝ) y) :=
      disjoint_left.mpr fun t ht ht' => absurd ht'.1 (not_lt.mpr ht)
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioc
      ((rvachevUp_integrable F hF).integrableOn)
      ((rvachevUp_integrable F hF).integrableOn)]
    have hzero : ∫ t in Iic (-1 : ℝ), rvachevUp F t = 0 := by
      have h0 : EqOn (rvachevUp F) (fun _ => (0 : ℝ)) (Iic (-1 : ℝ)) :=
        fun t ht => rvachevUp_eq_zero_of_le_neg_one F hF ht
      rw [setIntegral_congr_fun measurableSet_Iic h0, integral_zero]
    have hIoc : ∫ t in Ioc (-1 : ℝ) y, rvachevUp F t =
        fabiusReal F ((y + 1) / 2) := by
      rw [← intervalIntegral.integral_of_le hy.le,
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hasDerivAt_fabiusReal_half_shift F hF t)
          (((rvachev_contDiff F hF).continuous).intervalIntegrable (-1) y)]
      rw [show ((-1 : ℝ) + 1) / 2 = 0 by norm_num,
        hF.zero_of_nonpos 0 le_rfl, sub_zero]
    rw [hzero, hIoc, zero_add]

/-- **The CDF of the up-measure**:
`μ_up (-∞, y] = F((y+1)/2)`, in the measure's native `ℝ≥0∞` codomain. -/
theorem rvachevMeasure_Iic (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) :
    rvachevMeasure F (Iic y) =
      ENNReal.ofReal (fabiusReal F ((y + 1) / 2)) := by
  rw [rvachevMeasure, withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal
      ((rvachevUp_integrable F hF).integrableOn)
      (Eventually.of_forall fun t => rvachevUp_nonneg F t),
    setIntegral_rvachevUp_Iic F hF y]

/-- **The CDF of the random series** in `ℝ≥0∞` form: the law of
`X = ∑ U_k 2^{-k-1}` gives `(-∞, x]` the mass `F(x)`. -/
theorem weightedSumDistribution_Iic (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) :
    weightedSumDistribution (Iic x) = ENNReal.ofReal (fabiusReal F x) := by
  rw [← weightedSumCDF_eq_fabiusReal F hF x, weightedSumCDF,
    ProbabilityTheory.ofReal_cdf]

/-! ## The bridge between the two probabilistic descriptions -/

/-- **The up-measure is the law of the dyadic random series**, pushed
forward through `x ↦ 2x - 1`: the two probabilistic descriptions of
the Fabius–Rvachev system in this library are affinely the same
measure. -/
theorem rvachevMeasure_eq_map_weightedSum (F : BoundedFabius)
    (hF : IsFabius F) :
    rvachevMeasure F =
      weightedSumDistribution.map (fun x : ℝ => 2 * x - 1) := by
  haveI := rvachevMeasure_isProbability F hF
  refine Measure.ext_of_Iic (rvachevMeasure F) _ fun y => ?_
  rw [rvachevMeasure_Iic F hF y,
    Measure.map_apply
      (show Measurable fun x : ℝ => 2 * x - 1 from
        (measurable_id.const_mul 2).sub_const 1)
      measurableSet_Iic]
  have hpre : (fun x : ℝ => 2 * x - 1) ⁻¹' Iic y = Iic ((y + 1) / 2) := by
    ext x
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro h <;> linarith
  rw [hpre, weightedSumDistribution_Iic F hF]

/-- The inverse form of the bridge: the law of the random series is the
up-measure pushed forward through `y ↦ (y+1)/2`. -/
theorem weightedSum_eq_map_rvachevMeasure (F : BoundedFabius)
    (hF : IsFabius F) :
    weightedSumDistribution =
      (rvachevMeasure F).map (fun y : ℝ => (y + 1) / 2) := by
  rw [rvachevMeasure_eq_map_weightedSum F hF,
    Measure.map_map
      (show Measurable fun y : ℝ => (y + 1) / 2 from
        (measurable_id.add_const 1).div_const 2)
      (show Measurable fun x : ℝ => 2 * x - 1 from
        (measurable_id.const_mul 2).sub_const 1)]
  have hid : ((fun y : ℝ => (y + 1) / 2) ∘ fun x : ℝ => 2 * x - 1) = id := by
    funext x
    show (2 * x - 1 + 1) / 2 = x
    ring
  rw [hid, Measure.map_id]

/-! ## The characteristic function of the random series -/

/-- The characteristic function of the random series through that of
the up-measure: `E[e^{itX}] = e^{it/2} · charFun μ_up (t/2)`. -/
theorem charFun_weightedSum_eq_rvachev (F : BoundedFabius)
    (hF : IsFabius F) (t : ℝ) :
    charFun weightedSumDistribution t =
      cexp (((2⁻¹ * t : ℝ) : ℂ) * I) *
        charFun (rvachevMeasure F) (2⁻¹ * t) := by
  have hdecomp : weightedSumDistribution =
      ((rvachevMeasure F).map (2⁻¹ * ·)).map (· + 2⁻¹) := by
    rw [weightedSum_eq_map_rvachevMeasure F hF,
      Measure.map_map
        (show Measurable fun x : ℝ => x + 2⁻¹ from measurable_id.add_const _)
        (show Measurable fun x : ℝ => 2⁻¹ * x from measurable_const_mul _)]
    congr 1
    funext y
    show (y + 1) / 2 = 2⁻¹ * y + 2⁻¹
    ring
  rw [hdecomp, charFun_map_add_const, charFun_map_mul]
  simp only [Real.inner_apply]
  ring

/-- **The characteristic function of the dyadic random series** in
closed form: `E[e^{itX}] = e^{it/2} · Û(t/(4π))` where `Û` is the
Rvachev Fourier transform. -/
theorem charFun_weightedSumDistribution (F : BoundedFabius)
    (hF : IsFabius F) (t : ℝ) :
    charFun weightedSumDistribution t =
      cexp (((2⁻¹ * t : ℝ) : ℂ) * I) *
        rvachevFourier F (((2⁻¹ * t : ℝ) : ℂ) / (2 * Real.pi)) := by
  rw [charFun_weightedSum_eq_rvachev F hF t,
    rvachevMeasure_charFun_pos F hF]

/-! ## The equality-in-law splitting of the random series -/

/-- The characteristic function of the unit uniform digit:
`charFun (Uniform[0,1]) t = e^{it/2} · sinc(t/2)` — the symmetric
interval formula shifted by the interval's midpoint. -/
theorem charFun_volume_restrict_unit (t : ℝ) :
    charFun (volume.restrict (Icc (0 : ℝ) 1)) t =
      cexp (((2⁻¹ * t : ℝ) : ℂ) * I) *
        complexSinc ((2⁻¹ * t : ℝ) : ℂ) := by
  have hmap : volume.restrict (Icc (0 : ℝ) 1) =
      (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)).map (· + 2⁻¹) := by
    conv_lhs => rw [← map_add_right_eq_self volume (2⁻¹ : ℝ)]
    rw [Measure.restrict_map
      (show Measurable fun x : ℝ => x + 2⁻¹ from measurable_id.add_const _)
      measurableSet_Icc]
    have hpre : (fun x : ℝ => x + 2⁻¹) ⁻¹' Icc 0 1 =
        Icc (-(2⁻¹ : ℝ)) 2⁻¹ := by
      ext x
      simp only [mem_preimage, mem_Icc]
      constructor <;> exact fun h => ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [hpre]
  rw [hmap, charFun_map_add_const,
    charFun_volume_restrict_Icc (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  simp only [Real.inner_apply]
  have hcoef : (2 : ℂ) * ((2⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    norm_num
  rw [hcoef, one_mul, mul_comm]

/-- The refinement equation at the level of characteristic functions:
`charFun μ_up s = sinc(s/2) · charFun μ_up (s/2)`. -/
theorem charFun_rvachevMeasure_refine (F : BoundedFabius) (hF : IsFabius F)
    (s : ℝ) :
    charFun (rvachevMeasure F) s =
      complexSinc ((2⁻¹ * s : ℝ) : ℂ) *
        charFun (rvachevMeasure F) (2⁻¹ * s) := by
  haveI := rvachevMeasure_isProbability F hF
  haveI := isProbability_uniform_half
  haveI : IsProbabilityMeasure ((rvachevMeasure F).map (2⁻¹ * ·)) :=
    Measure.isProbabilityMeasure_map (measurable_const_mul _).aemeasurable
  conv_lhs => rw [rvachevMeasure_refinement F hF]
  rw [charFun_conv, charFun_map_mul,
    charFun_volume_restrict_Icc (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  have hcoef : (2 : ℂ) * ((2⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    norm_num
  rw [hcoef, one_mul]

/-- **The equality-in-law splitting of the dyadic random series**
(`eq:random-tail`, one digit): `X ≗ (U + X')/2` with `U` uniform on
`[0,1]` independent of the copy `X'` — as laws,
`law(X) = ((Uniform[0,1] ∗ law(X)) ∘ (·/2)⁻¹`.  Peeling the first
digit off the series and rescaling reproduces the whole law. -/
theorem weightedSumDistribution_self_similar :
    weightedSumDistribution =
      ((volume.restrict (Icc (0 : ℝ) 1)) ∗ weightedSumDistribution).map
        (2⁻¹ * ·) := by
  obtain ⟨F, hF⟩ : ∃ F, IsFabius F :=
    ⟨Existence.boundedCandidate, Existence.boundedCandidate_isFabius⟩
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_mul, charFun_conv, charFun_volume_restrict_unit,
    charFun_weightedSum_eq_rvachev F hF, charFun_weightedSum_eq_rvachev F hF,
    charFun_rvachevMeasure_refine F hF (2⁻¹ * t)]
  have hexp : cexp (((2⁻¹ * t : ℝ) : ℂ) * I) =
      cexp (((2⁻¹ * (2⁻¹ * t) : ℝ) : ℂ) * I) *
        cexp (((2⁻¹ * (2⁻¹ * t) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

end Fabius
