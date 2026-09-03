import FabiusFunction.WeakConvergence
import FabiusFunction.SincProductShells
import FabiusFunction.GeometricConvolutionTails

/-!
# The measure-level refinement equation of the up-function

The frontier drafts describe the up-density probabilistically: the law
of the random dyadic series `Y = ∑_{k ≥ 1} U_k 2^{-k}` with independent
uniform digits, whose tails are scaled copies of the whole
(`eq:random-tail`).  The generating identity of that description is
the **refinement equation** at the level of measures:

`μ_up = Uniform[-½,½] ∗ (μ_up ∘ (·/2)⁻¹)`

— the up-measure is the convolution of a uniform digit with a
half-scale copy of itself.  This module proves it by characteristic
functions: `charFun μ_up t` is the formal Fourier product, the dyadic
refinement `Φ(2w) = sinc(2πw)·Φ(w)` is the geometric-scale
renormalization law, `charFun` turns convolution into product and
scaling into argument scaling, and finite measures with equal
characteristic functions are equal (`Measure.ext_of_charFun`).
The iteration to all scales is not repeated here: the abstract
geometric tail law of `GeometricConvolutionTails.lean` turns the
one-step refinement into the measure-level random-tail law — `μ_up` is
the convolution of its first `m` uniform digits with a `2^{-m}`-scale
copy of itself — the drafts' `eq:random-tail` with no random variables
in sight.

* `charFun_volume_restrict_Icc` — the characteristic function of the
  symmetric interval: `charFun (volume.restrict [-c,c]) t = 2c·sinc(ct)`.
* `uniformDigitPrefix` — the law of the first `m` uniform digits, with
  its probability instance and characteristic function.
* `rvachevMeasure_refinement` — the refinement equation.
* `rvachevMeasure_eq_prefix_conv` — the iterated random-tail law.
-/

set_option autoImplicit false

open MeasureTheory Complex Real Set Finset

namespace Fabius

/-- **The characteristic function of the symmetric interval**: for
`0 ≤ c`, `charFun (volume.restrict (Icc (-c) c)) t = 2c · sinc (ct)` —
the elementary integral behind every uniform digit. -/
theorem charFun_volume_restrict_Icc {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    charFun (volume.restrict (Icc (-c) c)) t =
      2 * (c : ℂ) * complexSinc ((c * t : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hc with rfl | hcpos
  · simp [Set.Icc_self, Measure.restrict_singleton, charFun_apply]
  have hle : -c ≤ c := by linarith
  rw [charFun_apply_real, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  rcases eq_or_ne t 0 with rfl | ht
  · have h0 : ∀ x : ℝ, cexp (((0 : ℝ) : ℂ) * x * I) = 1 := by
      intro x
      norm_num
    rw [intervalIntegral.integral_congr fun x _ => h0 x,
      intervalIntegral.integral_const, complexSinc,
      if_pos (by push_cast; ring), Complex.real_smul]
    push_cast
    ring
  · have hIt : ((t : ℂ) * I) ≠ 0 :=
      mul_ne_zero (ofReal_ne_zero.mpr ht) I_ne_zero
    have hcongr : Set.EqOn (fun x : ℝ => cexp ((t : ℂ) * x * I))
        (fun x : ℝ => cexp (((t : ℂ) * I) * x)) (Set.uIcc (-c) c) := by
      intro x _
      ring_nf
    rw [intervalIntegral.integral_congr hcongr, integral_exp_mul_complex hIt]
    have hct : ((c * t : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (mul_ne_zero hcpos.ne' ht)
    rw [complexSinc, if_neg hct]
    have h1 : ((t : ℂ) * I) * ((c : ℝ) : ℂ) = ((c * t : ℝ) : ℂ) * I := by
      push_cast
      ring
    have h2 : ((t : ℂ) * I) * ((-c : ℝ) : ℂ) = -(((c * t : ℝ) : ℂ)) * I := by
      push_cast
      ring
    rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    have htC : ((t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
    field_simp
    push_cast
    ring

/-- The unit-length uniform digit is a probability measure. -/
theorem isProbability_uniform_half :
    IsProbabilityMeasure (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

/-- The law of the first `m` uniform dyadic digits `∑_{k=1}^m U_k 2^{-k}`
(`U_k` independent uniform on `[-½,½]` scaled by `2^{-(k-1)}`), defined
by the digit recursion `P_0 = δ_0`,
`P_{m+1} = Uniform[-½,½] ∗ (half-scale of P_m)`. -/
noncomputable def uniformDigitPrefix : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | m + 1 => (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) ∗
      ((uniformDigitPrefix m).map (2⁻¹ * ·))

/-- Every digit prefix is a probability measure. -/
theorem isProbabilityMeasure_uniformDigitPrefix (m : ℕ) :
    IsProbabilityMeasure (uniformDigitPrefix m) := by
  induction m with
  | zero =>
      rw [uniformDigitPrefix]
      infer_instance
  | succ m ih =>
      rw [uniformDigitPrefix]
      haveI := ih
      haveI : IsProbabilityMeasure ((uniformDigitPrefix m).map (2⁻¹ * ·)) :=
        Measure.isProbabilityMeasure_map (measurable_const_mul _).aemeasurable
      haveI := isProbability_uniform_half
      infer_instance

/-- The digit-prefix system is the abstract geometric prefix system of
`GeometricConvolutionTails.lean`, specialized to the uniform digit and
the scale `½`. -/
theorem uniformDigitPrefix_eq_mulPrefix (m : ℕ) :
    uniformDigitPrefix m =
      mulPrefix (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) 2⁻¹ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [uniformDigitPrefix, mulPrefix_succ, ih]

/-- **The characteristic function of the digit prefix** is the finite
sinc product `∏_{k<m} sinc (t/2^(k+1))`. -/
theorem charFun_uniformDigitPrefix (m : ℕ) (t : ℝ) :
    charFun (uniformDigitPrefix m) t =
      ∏ k ∈ Finset.range m, complexSinc ((t / 2 ^ (k + 1) : ℝ) : ℂ) := by
  induction m generalizing t with
  | zero =>
      rw [uniformDigitPrefix]
      simp
  | succ m ih =>
      haveI : IsProbabilityMeasure (uniformDigitPrefix m) :=
        isProbabilityMeasure_uniformDigitPrefix m
      haveI := isProbability_uniform_half
      rw [uniformDigitPrefix, charFun_conv, charFun_map_mul, ih,
        charFun_volume_restrict_Icc (by norm_num)]
      have hcoef : (2 : ℂ) * ((2⁻¹ : ℝ) : ℂ) = 1 := by
        push_cast
        norm_num
      rw [hcoef, one_mul, Finset.prod_range_succ', mul_comm]
      congr 1
      · refine Finset.prod_congr rfl fun k _ => ?_
        congr 1
        push_cast
        ring
      · congr 1
        push_cast
        ring

/-- **The measure-level refinement equation**:
`μ_up = Uniform[-½,½] ∗ (half-scale copy of μ_up)`.

The unit-mass uniform digit is `volume.restrict [-½,½]` (no
normalization needed: the interval has length one), and the half-scale
copy is the pushforward under `x ↦ x/2`. -/
theorem rvachevMeasure_refinement (F : BoundedFabius) (hF : IsFabius F) :
    rvachevMeasure F =
      (volume.restrict (Icc (-(2⁻¹ : ℝ)) 2⁻¹)) ∗
        ((rvachevMeasure F).map (2⁻¹ * ·)) := by
  haveI hprob : IsProbabilityMeasure (rvachevMeasure F) :=
    rvachevMeasure_isProbability F hF
  haveI := isProbability_uniform_half
  haveI : IsProbabilityMeasure ((rvachevMeasure F).map (2⁻¹ * ·)) :=
    Measure.isProbabilityMeasure_map (measurable_const_mul _).aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_conv, charFun_map_mul,
    charFun_volume_restrict_Icc (by norm_num) t,
    rvachevMeasure_charFun_pos F hF, rvachevMeasure_charFun_pos F hF,
    rvachevFourier_eq_product F hF, rvachevFourier_eq_product F hF]
  have hzdef : ((((2⁻¹ * t : ℝ)) : ℂ)) / (2 * Real.pi) =
      ((t : ℂ) / (2 * Real.pi)) / 2 := by
    push_cast
    ring
  have harg : ((t : ℝ) : ℂ) / (2 * Real.pi) =
      2 * (((((2⁻¹ * t : ℝ)) : ℂ)) / (2 * Real.pi)) := by
    rw [hzdef]
    ring
  rw [harg, rvachevFourierProduct_two_mul]
  have hsinc : (Real.pi : ℂ) * (2 * (((((2⁻¹ * t : ℝ)) : ℂ)) / (2 * Real.pi))) =
      ((2⁻¹ * t : ℝ) : ℂ) := by
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  rw [hsinc]
  have hcoef : (2 : ℂ) * ((2⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    norm_num
  rw [hcoef, one_mul]

/-- **The measure-level random-tail law** (`eq:random-tail`): the
up-measure is the convolution of its first `m` uniform digits with a
`2^{-m}`-scale copy of itself.  This is the abstract geometric tail
law of `GeometricConvolutionTails.lean` applied to the refinement
equation: no characteristic functions are needed beyond the single
step `rvachevMeasure_refinement`. -/
theorem rvachevMeasure_eq_prefix_conv (F : BoundedFabius) (hF : IsFabius F)
    (m : ℕ) :
    rvachevMeasure F =
      uniformDigitPrefix m ∗
        ((rvachevMeasure F).map ((((2 : ℝ) ^ m)⁻¹) * ·)) := by
  haveI : IsProbabilityMeasure (rvachevMeasure F) :=
    rvachevMeasure_isProbability F hF
  haveI := isProbability_uniform_half
  rw [uniformDigitPrefix_eq_mulPrefix, ← inv_pow]
  exact self_similar_conv_iterate_mul (rvachevMeasure_refinement F hF) m

end Fabius
