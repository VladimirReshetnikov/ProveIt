import FabiusFunction.PeriodicRegularity
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ZetaValues

/-!
# The Gamma--zeta Fourier coefficients of the periodic correction

The zero-mean correction `Ψ = negativeLaplacePsi` fixed in
`FabiusFunction.PeriodicCorrection` is exactly one-periodic, so it has a
Fourier expansion over a period.  This module evaluates every coefficient in
closed form.  With `L = log 2` and the paper's frequencies `χₖ = 2πik / L`,

`negativeLaplacePsiFourierCoeff k = -Γ(-χₖ) ζ(1 - χₖ) / L`  for `k ≠ 0`,

the zero mode vanishes by the normalization, and the resulting series
converges absolutely and reconstructs `Ψ` pointwise.

The mechanism is the substitution `x = 2 ^ t` that already drives
`FabiusFunction.PeriodicMean`.  In the logarithmic variable `t` the weight
`e^{-2πikt}` becomes the power `x ^ (-χₖ)`, so a Fourier coefficient is a
Mellin transform evaluated at the pure imaginary point `s = -χₖ`.  The dyadic
partitions `smallDyadicInterval` and `largeDyadicInterval` reassemble the
termwise integrals of `negativeLaplaceLog (2 ^ t)` and
`negativeLaplaceForwardTail (2 ^ t)` into one Mellin integral of the Bose
finite-part kernel over `(0,∞)`, and for `k ≠ 0` the remaining elementary
piece `log 2 / 2 * (t ^ 2 - t)` contributes exactly the term that cancels the
`1 / s ^ 2` regularizing the double pole of `-Γ(s) ζ(1+s)` at the origin.
What `FabiusFunction.PeriodicMean` does for the mode `k = 0`, this module
does for every mode.

Downstream what matters is nonvanishing rather than the formula:
`FabiusFunction.FabiusWikipediaObstruction` consumes
`negativeLaplacePsi_not_constant` to show that the periodic term missing from
the elementary small-argument formula cannot be absorbed into an
`O(1 / (-log x))` error, and `FabiusFunction.FabiusSharpAsymptotic` reexports
that obstruction beside the corrected asymptotic.

## Main results

* `negativeLaplacePsiFourierCoeff` — the coefficient `∫₀¹ Ψ(t) e^{-2πikt} dt`,
  defined through Mathlib's `fourierCoeffOn zero_lt_one`.
* `negativeLaplacePsiFourierCoeff_eq_neg_gamma_zeta` — the closed form above;
  `negativeLaplacePsiFourierCoeff_eq_gamma_zeta` is the same identity written
  in the Mellin frequency `negativeLaplaceMellinFrequency k = -χₖ`.
* `negativeLaplacePsiFourierCoeff_zero` — the zero mode vanishes.
* `negativeLaplacePsiFourierCoeff_ne_zero` and
  `negativeLaplacePsi_not_constant` — no nonzero mode vanishes, hence `Ψ` is
  genuinely nonconstant.  This is the export the rest of the corpus uses.
* `summable_negativeLaplacePsiFourierCoeff` — absolute summability of the
  coefficients.
* `hasSum_negativeLaplacePsi_fourierSeries` and
  `tsum_negativeLaplacePsi_gammaZeta_fourierSeries` — pointwise Fourier
  reconstruction on the real line, first with the abstract coefficients and
  then with the closed sequence `negativeLaplacePsiGammaZetaFourierCoeff`.
* `mellin_boseRegularizedMellinKernel_eq_gammaZeta_of_pos_re` and
  `mellin_boseRegularizedMellinKernel_eq_gammaZeta_of_re_zero` — the analytic
  engine.  The Mellin transform of `boseRegularizedMellinKernel` equals
  `gammaZetaMellinFinitePart` on the open right half-plane, by the identity
  theorem from the real evaluations of
  `FabiusFunction.BoseFinitePartIntegral`, and on the punctured imaginary
  axis by continuity.
* `negativeLaplacePsiCircle` — `Ψ` as a `C(AddCircle 1, ℂ)`, the object
  Mathlib's Fourier inversion theorem is stated for.

The remaining declarations are the change-of-variable, integrability,
dominated-convergence, and Bernoulli-coefficient steps feeding those results.

Conventions and caveats.  The Fourier convention is Mathlib's: coefficients
are taken against `e^{-2πikt}` and the series is summed against `e^{2πikt}`.
That sign is why the Mellin variable is `-χₖ` and not `χₖ`, and why both
spellings of the closed form are supplied.  The frequencies sit on the
imaginary axis, so the kernel is regularized first: subtracting the
small-argument logarithmic singularity makes the Mellin transform of
`boseRegularizedMellinKernel` holomorphic on `-1 < re s`, which the raw Bose
kernel is not.  Summability is proved by integrating by parts twice against
the uniform bound on `Ψ''` from `FabiusFunction.PeriodicRegularity`, giving
only `O(1 / k ^ 2)` decay; the paper's Stirling argument for exponential
decay of `Γ(-χₖ)` is not formalized, so the bound here is sufficient for
absolute convergence but far from sharp.  Nonvanishing rests on Mathlib's
`riemannZeta_ne_zero_of_one_le_re`, since `1 - χₖ` lies on `re s = 1`.
-/

set_option autoImplicit false

open scoped BigOperators Topology Interval FourierTransform
open Set Filter MeasureTheory Asymptotics Complex

namespace Fabius

/-- The Bose logarithm with its small-argument logarithmic singularity removed.
Its Mellin transform is holomorphic on `-1 < re s`. -/
noncomputable def boseRegularizedMellinKernel (x : ℝ) : ℂ :=
  if x ≤ 1 then (x * boseFinitePartSmallKernel x : ℝ) else boseLogKernel x

/-- `boseRegularizedMellinKernel` is integrable on `(0,∞)`, proved by
splitting at `1` into the weighted small kernel on `(0,1]` and the Bose
logarithm on `(1,∞)`.  This is the input to
`locallyIntegrableOn_boseRegularizedMellinKernel`. -/
lemma integrableOn_boseRegularizedMellinKernel :
    IntegrableOn boseRegularizedMellinKernel (Ioi 0) := by
  have hsmallR : IntegrableOn
      (fun x : ℝ => x * boseFinitePartSmallKernel x) (Ioc 0 1) := by
    simpa only [Real.rpow_one] using integrableOn_small_weighted_kernel 1 (by norm_num)
  have hsmall : IntegrableOn
      (fun x : ℝ => ((x * boseFinitePartSmallKernel x : ℝ) : ℂ)) (Ioc 0 1) :=
    hsmallR.ofReal
  have hlarge : IntegrableOn
      (fun x : ℝ => (boseLogKernel x : ℂ)) (Ioi 1) :=
    integrableOn_boseLogKernel_Ioi_one.ofReal
  have hunion : IntegrableOn boseRegularizedMellinKernel (Ioc 0 1 ∪ Ioi 1) := by
    apply IntegrableOn.union
    · apply hsmall.congr_fun
      · intro x hx
        simp [boseRegularizedMellinKernel, hx.2]
      · exact measurableSet_Ioc
    · apply hlarge.congr_fun
      · intro x hx
        change 1 < x at hx
        simp [boseRegularizedMellinKernel, not_le.mpr hx]
      · exact measurableSet_Ioi
  simpa [Ioc_union_Ioi_eq_Ioi zero_le_one] using hunion

/-- Local integrability on `(0,∞)`, the shape in which Mathlib's Mellin
criteria `mellin_differentiableAt_of_isBigO_rpow_exp` and
`mellinConvergent_of_isBigO_rpow_exp` want the hypothesis. -/
lemma locallyIntegrableOn_boseRegularizedMellinKernel :
    LocallyIntegrableOn boseRegularizedMellinKernel (Ioi 0) :=
  integrableOn_boseRegularizedMellinKernel.locallyIntegrableOn

/-- Small-argument decay: the regularized kernel is `O(x)` as `x → 0⁺`.
This is the `b = -1` half of the Mellin hypotheses, and it is what pushes
the half-plane of holomorphy out to `-1 < re s`. -/
lemma boseRegularizedMellinKernel_isBigO_zero :
    boseRegularizedMellinKernel =O[𝓝[>] 0] (fun x : ℝ => x ^ (1 : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with x hx hx1
  change 0 < x at hx
  have hxmem : x ∈ Ioc (0 : ℝ) 1 := ⟨hx, hx1.le⟩
  rw [boseRegularizedMellinKernel, if_pos hx1.le]
  rw [norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hx,
    Real.rpow_one, Real.norm_eq_abs, abs_of_pos hx]
  simpa using mul_le_mul_of_nonneg_left
    (abs_boseFinitePartSmallKernel_le_one x hxmem) hx.le

/-- Large-argument decay: the regularized kernel is `O(exp (-x))` at
infinity, the `a = 1` half of the Mellin hypotheses. -/
lemma boseRegularizedMellinKernel_isBigO_atTop :
    boseRegularizedMellinKernel =O[atTop]
      (fun x : ℝ => Real.exp (-(1 * x))) := by
  let C : ℝ := 1 / (1 - Real.exp (-1))
  rw [isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [boseRegularizedMellinKernel, if_neg (not_le.mpr hx)]
  rw [norm_real, Real.norm_eq_abs]
  have h := abs_boseLogKernel_le_const_exp x hx.le
  simpa [C] using h

/-- The Mellin transform of `boseRegularizedMellinKernel` is complex
differentiable at every `s` with `-1 < re s`.  That half-plane reaches past
the imaginary axis, which is where the Fourier frequencies sit. -/
lemma differentiableAt_mellin_boseRegularizedMellinKernel
    (s : ℂ) (hs : -1 < s.re) :
    DifferentiableAt ℂ (mellin boseRegularizedMellinKernel) s := by
  apply mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := -1)
  · norm_num
  · exact locallyIntegrableOn_boseRegularizedMellinKernel
  · simpa using boseRegularizedMellinKernel_isBigO_atTop
  · simpa using boseRegularizedMellinKernel_isBigO_zero
  · exact hs

/-- For `-1 < re s` the Mellin integral of `boseRegularizedMellinKernel`
converges, that is, `x ↦ x ^ (s - 1) * f x` is integrable on `(0,∞)`.
Applied below at the purely imaginary `negativeLaplaceMellinFrequency k`. -/
lemma mellinConvergent_boseRegularizedMellinKernel
    (s : ℂ) (hs : -1 < s.re) :
    MellinConvergent boseRegularizedMellinKernel s := by
  apply mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := -1)
  · norm_num
  · exact locallyIntegrableOn_boseRegularizedMellinKernel
  · simpa using boseRegularizedMellinKernel_isBigO_atTop
  · simpa using boseRegularizedMellinKernel_isBigO_zero
  · exact hs

/-- The Mellin transform is analytic on the open half-plane `-1 < re s`;
one of the two inputs to the identity-theorem argument in
`mellin_boseRegularizedMellinKernel_eq_gammaZeta_of_pos_re`. -/
lemma analyticOnNhd_mellin_boseRegularizedMellinKernel :
    AnalyticOnNhd ℂ (mellin boseRegularizedMellinKernel) {s : ℂ | -1 < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (differentiableAt_mellin_boseRegularizedMellinKernel s hs).differentiableWithinAt
  · exact isOpen_lt continuous_const continuous_re

/-- At a real point `a` with `0 < a ≤ 1` the Mellin transform is the real
number obtained by splitting the integral at `1`: the weight `x ^ a`
against `boseFinitePartSmallKernel` on `(0,1]`, plus `x ^ (a - 1)` against
`boseLogKernel` on `(1,∞)`.  These are exactly the two integrals evaluated
in `FabiusFunction.BoseFinitePartIntegral`. -/
lemma mellin_boseRegularizedMellinKernel_ofReal
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    mellin boseRegularizedMellinKernel (a : ℂ) =
      ((∫ x : ℝ in Ioc 0 1,
          x ^ a * boseFinitePartSmallKernel x) +
        ∫ x : ℝ in Ioi 1,
          x ^ (a - 1) * boseLogKernel x : ℝ) := by
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ ((a : ℂ) - 1) * boseRegularizedMellinKernel x
  have hsmallR := integrableOn_small_weighted_kernel a ha.le
  have hlargeR := integrableOn_large_weighted_kernel a ha1
  have hsmall : IntegrableOn g (Ioc 0 1) := by
    have hcast : IntegrableOn
        (fun x : ℝ => ((x ^ a * boseFinitePartSmallKernel x : ℝ) : ℂ))
        (Ioc 0 1) := hsmallR.ofReal
    apply hcast.congr_fun
    · intro x hx
      dsimp [g]
      rw [boseRegularizedMellinKernel, if_pos hx.2]
      have hpow : (x : ℂ) ^ ((a : ℂ) - 1) = ((x ^ (a - 1) : ℝ) : ℂ) := by
        simpa only [ofReal_sub, ofReal_one] using
          (ofReal_cpow hx.1.le (a - 1)).symm
      rw [hpow]
      push_cast
      have hxpow : x ^ (a - 1) * x = x ^ a := by
        calc
          x ^ (a - 1) * x = x ^ (a - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((a - 1) + 1) := by rw [Real.rpow_add hx.1]
          _ = x ^ a := by ring_nf
      norm_cast
      rw [← mul_assoc, hxpow]
    · exact measurableSet_Ioc
  have hlarge : IntegrableOn g (Ioi 1) := by
    have hcast : IntegrableOn
        (fun x : ℝ => ((x ^ (a - 1) * boseLogKernel x : ℝ) : ℂ))
        (Ioi 1) := hlargeR.ofReal
    apply hcast.congr_fun
    · intro x hx
      change 1 < x at hx
      dsimp [g]
      rw [boseRegularizedMellinKernel, if_neg (not_le.mpr hx)]
      have hpow : (x : ℂ) ^ ((a : ℂ) - 1) = ((x ^ (a - 1) : ℝ) : ℂ) := by
        simpa only [ofReal_sub, ofReal_one] using
          (ofReal_cpow (zero_lt_one.trans hx).le (a - 1)).symm
      rw [hpow]
      push_cast
      rfl
    · exact measurableSet_Ioi
  have hdis : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    intro x hxsmall hxlarge
    exact (not_lt_of_ge hxsmall.2) hxlarge
  have hsplit := integral_union_ae hdis.aedisjoint
    measurableSet_Ioi.nullMeasurableSet hsmall hlarge
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  rw [mellin]
  change (∫ x : ℝ in Ioi 0, g x) = _
  rw [hsplit]
  rw [show (∫ x : ℝ in Ioc 0 1, g x) =
      ((∫ x : ℝ in Ioc 0 1,
        x ^ a * boseFinitePartSmallKernel x : ℝ) : ℂ) by
    have hcastIntegral :
        (∫ x : ℝ in Ioc 0 1,
          ((x ^ a * boseFinitePartSmallKernel x : ℝ) : ℂ)) =
          ((∫ x : ℝ in Ioc 0 1,
            x ^ a * boseFinitePartSmallKernel x : ℝ) : ℂ) :=
      integral_ofReal
    rw [← hcastIntegral]
    exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
      dsimp [g]
      rw [boseRegularizedMellinKernel, if_pos hx.2]
      have hpow : (x : ℂ) ^ ((a : ℂ) - 1) = ((x ^ (a - 1) : ℝ) : ℂ) := by
        simpa only [ofReal_sub, ofReal_one] using
          (ofReal_cpow hx.1.le (a - 1)).symm
      rw [hpow]
      push_cast
      have hxpow : x ^ (a - 1) * x = x ^ a := by
        calc
          x ^ (a - 1) * x = x ^ (a - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((a - 1) + 1) := by rw [Real.rpow_add hx.1]
          _ = x ^ a := by ring_nf
      norm_cast
      rw [← mul_assoc, hxpow])]
  rw [show (∫ x : ℝ in Ioi 1, g x) =
      ((∫ x : ℝ in Ioi 1,
        x ^ (a - 1) * boseLogKernel x : ℝ) : ℂ) by
    have hcastIntegral :
        (∫ x : ℝ in Ioi 1,
          ((x ^ (a - 1) * boseLogKernel x : ℝ) : ℂ)) =
          ((∫ x : ℝ in Ioi 1,
            x ^ (a - 1) * boseLogKernel x : ℝ) : ℂ) :=
      integral_ofReal
    rw [← hcastIntegral]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
      change 1 < x at hx
      dsimp [g]
      rw [boseRegularizedMellinKernel, if_neg (not_le.mpr hx)]
      have hpow : (x : ℂ) ^ ((a : ℂ) - 1) = ((x ^ (a - 1) : ℝ) : ℂ) := by
        simpa only [ofReal_sub, ofReal_one] using
          (ofReal_cpow (zero_lt_one.trans hx).le (a - 1)).symm
      rw [hpow]
      push_cast
      rfl)]
  norm_cast

/-- The analytic finite part of `-Γ(s) ζ(1+s)` at the origin. -/
noncomputable def gammaZetaMellinFinitePart (s : ℂ) : ℂ :=
  -Gamma s * riemannZeta (1 + s) + 1 / s ^ 2

/-- `gammaZetaMellinFinitePart` is complex differentiable at every `s` of
positive real part, where `Γ` has no pole, `ζ (1 + s)` stays off the pole
at `1`, and `1 / s ^ 2` is regular. -/
lemma differentiableAt_gammaZetaMellinFinitePart
    (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ gammaZetaMellinFinitePart s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hGamma : DifferentiableAt ℂ Gamma s :=
    Complex.differentiableAt_Gamma s (fun m h => by
      have hre := congrArg re h
      simp at hre
      linarith)
  have hzarg : 1 + s ≠ 1 := by simpa using hs0
  have harg : DifferentiableAt ℂ (fun z : ℂ => 1 + z) s :=
    (differentiableAt_const (c := (1 : ℂ))).add differentiableAt_id
  have hzeta : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (1 + z)) s :=
    (differentiableAt_riemannZeta hzarg).comp s harg
  have hinv : DifferentiableAt ℂ (fun z : ℂ => 1 / z ^ 2) s :=
    (differentiableAt_const (c := (1 : ℂ))).div
      (differentiableAt_id.pow 2) (pow_ne_zero 2 hs0)
  unfold gammaZetaMellinFinitePart
  exact (hGamma.neg.mul hzeta).add hinv

/-- `gammaZetaMellinFinitePart` is analytic on the open right half-plane
`0 < re s`, the second input to the identity-theorem argument. -/
lemma analyticOnNhd_gammaZetaMellinFinitePart :
    AnalyticOnNhd ℂ gammaZetaMellinFinitePart {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (differentiableAt_gammaZetaMellinFinitePart s hs).differentiableWithinAt
  · exact isOpen_lt continuous_const continuous_re

/-- The Mellin transform agrees with `gammaZetaMellinFinitePart` at every
real point of `(0,1]`, by the real evaluation proved in
`FabiusFunction.BoseFinitePartIntegral`.  Those real points accumulate at
`1 / 2`, which is what lets the identity theorem propagate the identity
across the right half-plane. -/
lemma mellin_boseRegularizedMellinKernel_ofReal_eq_gammaZeta
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    mellin boseRegularizedMellinKernel (a : ℂ) =
      gammaZetaMellinFinitePart (a : ℂ) := by
  rw [mellin_boseRegularizedMellinKernel_ofReal a ha ha1]
  rw [← gamma_zeta_finitePart_eq_regularized_integrals a ha ha1]
  have hzreal :
      (((riemannZeta (((1 + a : ℝ) : ℂ))).re : ℝ) : ℂ) =
        riemannZeta (((1 + a : ℝ) : ℂ)) := by
    apply conj_eq_iff_re.mp
    rw [← riemannZeta_conj]
    simp
  unfold gammaZetaMellinFinitePart
  rw [Gamma_ofReal]
  rw [show (1 : ℂ) + (a : ℂ) = ((1 + a : ℝ) : ℂ) by push_cast; rfl]
  rw [← hzreal]
  push_cast
  simp

/-- Analytic continuation of the regularized Bose Mellin integral throughout
the open right half-plane. -/
theorem mellin_boseRegularizedMellinKernel_eq_gammaZeta_of_pos_re
    (s : ℂ) (hs : 0 < s.re) :
    mellin boseRegularizedMellinKernel s = gammaZetaMellinFinitePart s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  let z₀ : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hmellin : AnalyticOnNhd ℂ (mellin boseRegularizedMellinKernel) U := by
    apply analyticOnNhd_mellin_boseRegularizedMellinKernel.mono
    intro z hz
    dsimp [U] at hz ⊢
    linarith
  have hgamma : AnalyticOnNhd ℂ gammaZetaMellinFinitePart U := by
    simpa [U] using analyticOnNhd_gammaZetaMellinFinitePart
  have hU : IsPreconnected U := by
    simpa [U] using (convex_halfSpace_re_gt 0).isPreconnected
  have hz₀U : z₀ ∈ U := by
    simp [z₀, U]
  have hclosure : z₀ ∈ closure
      ({z | mellin boseRegularizedMellinKernel z = gammaZetaMellinFinitePart z} \ {z₀}) := by
    rw [mem_closure_iff_seq_limit]
    let uR : ℕ → ℝ := fun n => 1 / 2 + (1 / 2 : ℝ) ^ n / 4
    let u : ℕ → ℂ := fun n => (uR n : ℂ)
    refine ⟨u, ?_, ?_⟩
    · intro n
      have hpow0 : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
      have hu0 : 0 < uR n := by
        dsimp [uR]
        positivity
      have hpone : (1 / 2 : ℝ) ^ n ≤ 1 := by
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have hu1 : uR n ≤ 1 := by
        dsimp [uR]
        nlinarith
      constructor
      · exact mellin_boseRegularizedMellinKernel_ofReal_eq_gammaZeta
          (uR n) hu0 hu1
      · simp only [mem_singleton_iff]
        intro heq
        have hre := congrArg re heq
        dsimp [u, uR, z₀] at hre
        simp at hre
    · have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have huR : Tendsto uR atTop (𝓝 (1 / 2 : ℝ)) := by
        simpa [uR] using (hp.div_const 4).const_add (1 / 2 : ℝ)
      exact (continuous_ofReal.tendsto ((1 / 2 : ℝ))).comp huR
  have heq := hmellin.eqOn_of_preconnected_of_mem_closure hgamma hU hz₀U hclosure
  exact heq hs

/-- Boundary value of the regularized Mellin identity at every nonzero point
of the imaginary axis. -/
theorem mellin_boseRegularizedMellinKernel_eq_gammaZeta_of_re_zero
    (s : ℂ) (hre : s.re = 0) (hs0 : s ≠ 0) :
    mellin boseRegularizedMellinKernel s = gammaZetaMellinFinitePart s := by
  have hmcont : ContinuousAt (mellin boseRegularizedMellinKernel) s :=
    (differentiableAt_mellin_boseRegularizedMellinKernel s (by linarith)).continuousAt
  have hGamma : DifferentiableAt ℂ Gamma s :=
    Complex.differentiableAt_Gamma s (fun m h => by
      by_cases hm : m = 0
      · subst m
        exact hs0 (by simpa using h)
      · have hre' := congrArg re h
        simp [hre] at hre'
        omega)
  have hzarg : 1 + s ≠ 1 := by simpa using hs0
  have harg : DifferentiableAt ℂ (fun z : ℂ => 1 + z) s :=
    (differentiableAt_const (c := (1 : ℂ))).add differentiableAt_id
  have hzeta : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (1 + z)) s :=
    (differentiableAt_riemannZeta hzarg).comp s harg
  have hinv : DifferentiableAt ℂ (fun z : ℂ => 1 / z ^ 2) s :=
    (differentiableAt_const (c := (1 : ℂ))).div
      (differentiableAt_id.pow 2) (pow_ne_zero 2 hs0)
  have hgcont : ContinuousAt gammaZetaMellinFinitePart s := by
    unfold gammaZetaMellinFinitePart
    exact ((hGamma.neg.mul hzeta).add hinv).continuousAt
  let u : ℕ → ℂ := fun n => s + (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hu : Tendsto u atTop (𝓝 s) := by
    simpa [u] using tendsto_const_nhds.add (continuous_ofReal.tendsto 0 |>.comp hp)
  have heq : ∀ n : ℕ,
      mellin boseRegularizedMellinKernel (u n) = gammaZetaMellinFinitePart (u n) := by
    intro n
    apply mellin_boseRegularizedMellinKernel_eq_gammaZeta_of_pos_re
    dsimp [u]
    simp [hre]
  have hmlim := hmcont.tendsto.comp hu
  have hglim := hgcont.tendsto.comp hu
  exact tendsto_nhds_unique hmlim (hglim.congr' (Eventually.of_forall fun n => (heq n).symm))

/-- The Mellin frequency corresponding to the `k`th Fourier mode in base two. -/
noncomputable def negativeLaplaceMellinFrequency (k : ℤ) : ℂ :=
  -(2 * (Real.pi : ℂ) * I * (k : ℂ)) / Real.log 2

/-- Mathlib's `e^{-2πikt}` Fourier weight, written explicitly. -/
noncomputable def negativeLaplaceFourierWeight (k : ℤ) (t : ℝ) : ℂ :=
  exp (-(2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ)))

/-- The Fourier weight has modulus one at every real `t`, so the bounds
and dominated-convergence arguments below reduce to bounds on the real
factor it multiplies. -/
lemma norm_negativeLaplaceFourierWeight (k : ℤ) (t : ℝ) :
    ‖negativeLaplaceFourierWeight k t‖ = 1 := by
  rw [negativeLaplaceFourierWeight, norm_exp]
  simp

/-- The weight is invariant under integer translations of `t`.  This is
how the termwise integrals over `[0,1]` are shifted onto the dyadic
blocks. -/
lemma negativeLaplaceFourierWeight_add_int (k m : ℤ) (t : ℝ) :
    negativeLaplaceFourierWeight k (t + m) =
      negativeLaplaceFourierWeight k t := by
  rw [negativeLaplaceFourierWeight, negativeLaplaceFourierWeight]
  push_cast
  rw [show -(2 * (Real.pi : ℂ) * I * (k : ℂ) * ((t : ℂ) + (m : ℂ))) =
      -(2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ)) +
        (-(k * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by
    push_cast
    ring]
  rw [exp_add]
  have hexp : exp (-((k * m : ℤ) : ℂ) *
      (2 * (Real.pi : ℂ) * I)) = 1 := by
    simpa only [Int.cast_neg] using exp_int_mul_two_pi_mul_I (-(k * m))
  rw [hexp]
  ring

/-- The substitution `x = 2 ^ t` in one line: at `t = logb 2 x` the
Fourier weight becomes the complex power
`x ^ negativeLaplaceMellinFrequency k`.  Stated for `0 < x`. -/
lemma negativeLaplaceFourierWeight_eq_cpow_logb
    (k : ℤ) (x : ℝ) (hx : 0 < x) :
    negativeLaplaceFourierWeight k (Real.logb 2 x) =
      (x : ℂ) ^ negativeLaplaceMellinFrequency k := by
  rw [negativeLaplaceFourierWeight, negativeLaplaceMellinFrequency]
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]
  rw [← ofReal_log hx.le]
  rw [Real.logb]
  congr 1
  push_cast
  have hlog2 : (Real.log 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (Real.log_pos (by norm_num)).ne'
  field_simp [hlog2]

/-- Change of variables `x = 2 ^ t` for the small-argument kernel: `log 2`
times the weighted integral of `negativeLaplaceKernel (2 ^ t)` over `[a,b]`
is the Mellin-weighted integral of `boseFinitePartSmallKernel` over
`[2 ^ a, 2 ^ b]`.  The `1 / x` inside the small kernel is the Jacobian. -/
lemma intervalIntegral_negativeLaplaceKernel_fourier
    (k : ℤ) (a b : ℝ) :
    Real.log 2 * (∫ t : ℝ in a..b,
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceKernel ((2 : ℝ) ^ t) : ℂ)) =
      ∫ x : ℝ in (2 : ℝ) ^ a..(2 : ℝ) ^ b,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartSmallKernel x : ℂ) := by
  let f : ℝ → ℝ := fun t => (2 : ℝ) ^ t
  let f' : ℝ → ℝ := fun t => Real.log 2 * (2 : ℝ) ^ t
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ negativeLaplaceMellinFrequency k *
      (boseFinitePartSmallKernel x : ℂ)
  have hf : ∀ t ∈ [[a, b]], HasDerivAt f (f' t) t := by
    intro t ht
    simpa [f, f'] using (hasDerivAt_id t).const_rpow (by norm_num : (0 : ℝ) < 2)
  have hf' : ContinuousOn f' [[a, b]] := by
    exact (continuous_const.mul
      (Real.continuous_const_rpow (by norm_num))).continuousOn
  have hg : ContinuousOn g (f '' [[a, b]]) := by
    apply ContinuousOn.mul
    · intro x hx
      rcases hx with ⟨t, ht, rfl⟩
      exact (continuousAt_ofReal_cpow_const _ _
        (Or.inr (Real.rpow_pos_of_pos (by norm_num) t).ne')).continuousWithinAt
    · exact (continuous_ofReal.comp_continuousOn
        continuousOn_boseFinitePartSmallKernel).mono (fun x hx => by
          rcases hx with ⟨t, ht, rfl⟩
          exact Real.rpow_pos_of_pos (by norm_num) t)
  have hsub := intervalIntegral.integral_deriv_smul_comp' (g := g) hf hf' hg
  dsimp [f, f', g] at hsub
  rw [show (fun t : ℝ =>
      ((Real.log 2 * (2 : ℝ) ^ t : ℝ) : ℂ) *
        ((((2 : ℝ) ^ t : ℝ) : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartSmallKernel ((2 : ℝ) ^ t) : ℂ))) =
      fun t : ℝ => (Real.log 2 : ℂ) *
        (negativeLaplaceFourierWeight k t *
          (negativeLaplaceKernel ((2 : ℝ) ^ t) : ℂ)) by
    funext t
    have hp : 0 < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
    have hw := negativeLaplaceFourierWeight_eq_cpow_logb k ((2 : ℝ) ^ t) hp
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at hw
    rw [← hw]
    unfold boseFinitePartSmallKernel
    push_cast
    field_simp [hp.ne']
  ] at hsub
  rw [intervalIntegral.integral_const_mul] at hsub
  exact hsub

/-- The same change of variables for the large-argument kernel: `log 2`
times the weighted integral of `boseLogKernel (2 ^ t)` over `[a,b]` is the
Mellin-weighted integral of `boseFinitePartLargeKernel` over
`[2 ^ a, 2 ^ b]`. -/
lemma intervalIntegral_boseLogKernel_fourier
    (k : ℤ) (a b : ℝ) :
    Real.log 2 * (∫ t : ℝ in a..b,
      negativeLaplaceFourierWeight k t * (boseLogKernel ((2 : ℝ) ^ t) : ℂ)) =
      ∫ x : ℝ in (2 : ℝ) ^ a..(2 : ℝ) ^ b,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartLargeKernel x : ℂ) := by
  let f : ℝ → ℝ := fun t => (2 : ℝ) ^ t
  let f' : ℝ → ℝ := fun t => Real.log 2 * (2 : ℝ) ^ t
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ negativeLaplaceMellinFrequency k *
      (boseFinitePartLargeKernel x : ℂ)
  have hf : ∀ t ∈ [[a, b]], HasDerivAt f (f' t) t := by
    intro t ht
    simpa [f, f'] using (hasDerivAt_id t).const_rpow (by norm_num : (0 : ℝ) < 2)
  have hf' : ContinuousOn f' [[a, b]] := by
    exact (continuous_const.mul
      (Real.continuous_const_rpow (by norm_num))).continuousOn
  have hg : ContinuousOn g (f '' [[a, b]]) := by
    apply ContinuousOn.mul
    · intro x hx
      rcases hx with ⟨t, ht, rfl⟩
      exact (continuousAt_ofReal_cpow_const _ _
        (Or.inr (Real.rpow_pos_of_pos (by norm_num) t).ne')).continuousWithinAt
    · exact (continuous_ofReal.comp_continuousOn
        continuousOn_boseFinitePartLargeKernel).mono (fun x hx => by
          rcases hx with ⟨t, ht, rfl⟩
          exact Real.rpow_pos_of_pos (by norm_num) t)
  have hsub := intervalIntegral.integral_deriv_smul_comp' (g := g) hf hf' hg
  dsimp [f, f', g] at hsub
  rw [show (fun t : ℝ =>
      ((Real.log 2 * (2 : ℝ) ^ t : ℝ) : ℂ) *
        ((((2 : ℝ) ^ t : ℝ) : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartLargeKernel ((2 : ℝ) ^ t) : ℂ))) =
      fun t : ℝ => (Real.log 2 : ℂ) *
        (negativeLaplaceFourierWeight k t *
          (boseLogKernel ((2 : ℝ) ^ t) : ℂ)) by
    funext t
    have hp : 0 < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
    have hw := negativeLaplaceFourierWeight_eq_cpow_logb k ((2 : ℝ) ^ t) hp
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at hw
    rw [← hw]
    unfold boseFinitePartLargeKernel
    push_cast
    field_simp [hp.ne']
  ] at hsub
  rw [intervalIntegral.integral_const_mul] at hsub
  exact hsub

/-- The `n`-th term of `negativeLaplaceLog (2 ^ t)`, integrated against
the weight over one period, is the Mellin integral of
`boseFinitePartSmallKernel` over `smallDyadicInterval n`, up to the factor
`log 2`.  The shift `t ↦ t - (n + 1)` uses periodicity of the weight. -/
lemma intervalIntegral_negativeLaplaceTerm_fourier (k : ℤ) (n : ℕ) :
    Real.log 2 * (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceTerm ((2 : ℝ) ^ t) n : ℂ)) =
      ∫ x : ℝ in smallDyadicInterval n,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartSmallKernel x : ℂ) := by
  let H : ℝ → ℂ := fun u => negativeLaplaceFourierWeight k u *
    (negativeLaplaceKernel ((2 : ℝ) ^ u) : ℂ)
  have heq : ∀ t : ℝ,
      negativeLaplaceFourierWeight k t *
          (negativeLaplaceTerm ((2 : ℝ) ^ t) n : ℂ) =
        H (t - ((n + 1 : ℕ) : ℝ)) := by
    intro t
    have hw := negativeLaplaceFourierWeight_add_int k (n + 1)
      (t - ((n + 1 : ℕ) : ℝ))
    have hshift : negativeLaplaceFourierWeight k t =
        negativeLaplaceFourierWeight k (t - ((n + 1 : ℕ) : ℝ)) := by
      convert hw using 1 <;> push_cast
      ring
    rw [hshift]
    unfold H negativeLaplaceTerm
    congr 2
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  rw [intervalIntegral.integral_congr (fun t ht => heq t)]
  rw [intervalIntegral.integral_comp_sub_right H ((n + 1 : ℕ) : ℝ)]
  rw [show (0 : ℝ) - ((n + 1 : ℕ) : ℝ) = -((n + 1 : ℕ) : ℝ) by ring]
  rw [show (1 : ℝ) - ((n + 1 : ℕ) : ℝ) = -((n : ℕ) : ℝ) by
    push_cast
    ring]
  have hchange := intervalIntegral_negativeLaplaceKernel_fourier k
    (-((n + 1 : ℕ) : ℝ)) (-((n : ℕ) : ℝ))
  have hbounds : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num) (by omega))
  rw [smallDyadicInterval, ← intervalIntegral.integral_of_le hbounds]
  have hlo : (2 : ℝ) ^ (-((n + 1 : ℕ) : ℝ)) =
      ((2 : ℝ) ^ (n + 1))⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have hhi : (2 : ℝ) ^ (-((n : ℕ) : ℝ)) = ((2 : ℝ) ^ n)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [hlo, hhi] at hchange
  exact hchange

/-- The `n`-th forward-tail term, integrated against the weight over one
period, is the Mellin integral of `boseFinitePartLargeKernel` over
`Ioc (2 ^ n) (2 ^ (n + 1))`, up to the factor `log 2`. -/
lemma intervalIntegral_negativeLaplaceForwardTerm_fourier (k : ℤ) (n : ℕ) :
    Real.log 2 * (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n : ℂ)) =
      ∫ x : ℝ in Ioc ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)),
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartLargeKernel x : ℂ) := by
  let H : ℝ → ℂ := fun u => negativeLaplaceFourierWeight k u *
    (boseLogKernel ((2 : ℝ) ^ u) : ℂ)
  have heq : ∀ t : ℝ,
      negativeLaplaceFourierWeight k t *
          (negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n : ℂ) =
        H (t + (n : ℝ)) := by
    intro t
    have hw := negativeLaplaceFourierWeight_add_int k n t
    rw [← hw]
    unfold H negativeLaplaceForwardTerm boseLogKernel
    congr 4
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  rw [intervalIntegral.integral_congr (fun t ht => heq t)]
  rw [intervalIntegral.integral_comp_add_right H (n : ℝ)]
  rw [show (0 : ℝ) + (n : ℝ) = (n : ℝ) by ring]
  rw [show (1 : ℝ) + (n : ℝ) = (n : ℝ) + 1 by ring]
  have hchange := intervalIntegral_boseLogKernel_fourier k (n : ℝ) (n + 1 : ℝ)
  have hbounds : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [← intervalIntegral.integral_of_le hbounds]
  have hlo : (2 : ℝ) ^ (n : ℝ) = (2 : ℝ) ^ n := by
    rw [Real.rpow_natCast]
  have hhi : (2 : ℝ) ^ ((n : ℝ) + 1) = (2 : ℝ) ^ (n + 1) := by
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rw [hlo, hhi] at hchange
  exact hchange

/-- The Mellin frequency is purely imaginary.  It therefore lies inside
the half-plane `-1 < re s` where the regularized Mellin transform is
analytic, but on the boundary of `0 < re s`, which is why the identity with
`gammaZetaMellinFinitePart` needs the separate boundary theorem. -/
lemma negativeLaplaceMellinFrequency_re (k : ℤ) :
    (negativeLaplaceMellinFrequency k).re = 0 := by
  unfold negativeLaplaceMellinFrequency
  change
    (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) /
      ((Real.log 2 : ℝ) : ℂ)).re = 0
  have h :
      -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) /
          ((Real.log 2 : ℝ) : ℂ) =
        Complex.I *
          (((-(2 * Real.pi * (k : ℝ)) / Real.log 2 : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [h]
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The integrand `x ^ negativeLaplaceMellinFrequency k` times
`boseFinitePartSmallKernel x` is integrable on `(0,1]`; this is the
integrability hypothesis of `hasSum_integral_smallDyadicInterval_fourier`. -/
lemma integrableOn_small_negativeLaplaceMellinFrequency (k : ℤ) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ negativeLaplaceMellinFrequency k *
        (boseFinitePartSmallKernel x : ℂ)) (Ioc 0 1) := by
  have hconv := mellinConvergent_boseRegularizedMellinKernel
    (negativeLaplaceMellinFrequency k) (by
      rw [negativeLaplaceMellinFrequency_re]
      norm_num)
  rw [MellinConvergent] at hconv
  have hrest := hconv.mono_set
    (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 by exact Ioc_subset_Ioi_self)
  apply hrest.congr_fun
  · intro x hx
    simp only [boseRegularizedMellinKernel, if_pos hx.2]
    simp only [smul_eq_mul]
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
    have hpow : (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) * (x : ℂ) =
        (x : ℂ) ^ negativeLaplaceMellinFrequency k := by
      calc
        (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) * (x : ℂ) =
            (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) *
              (x : ℂ) ^ (1 : ℂ) := by rw [cpow_one]
        _ = (x : ℂ) ^ ((negativeLaplaceMellinFrequency k - 1) + 1) := by
          rw [cpow_add _ _ hx0]
        _ = (x : ℂ) ^ negativeLaplaceMellinFrequency k := by ring_nf
    push_cast
    rw [← mul_assoc, hpow]
  · exact measurableSet_Ioc

/-- The integrand `x ^ (negativeLaplaceMellinFrequency k - 1)` times
`boseLogKernel x` is integrable on `(1,∞)`. -/
lemma integrableOn_large_negativeLaplaceMellinFrequency (k : ℤ) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) *
        (boseLogKernel x : ℂ)) (Ioi 1) := by
  have hconv := mellinConvergent_boseRegularizedMellinKernel
    (negativeLaplaceMellinFrequency k) (by
      rw [negativeLaplaceMellinFrequency_re]
      norm_num)
  rw [MellinConvergent] at hconv
  have hrest := hconv.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
    intro x hx
    change 1 < x at hx
    exact zero_lt_one.trans hx)
  apply hrest.congr_fun
  · intro x hx
    change 1 < x at hx
    simp only [boseRegularizedMellinKernel, if_neg (not_le.mpr hx)]
    simp only [smul_eq_mul]
  · exact measurableSet_Ioi

/-- The previous integrability restated with the `1 / x` absorbed into
`boseFinitePartLargeKernel`; this is the hypothesis of
`hasSum_integral_largeDyadicInterval_fourier`. -/
lemma integrableOn_largeKernel_negativeLaplaceMellinFrequency (k : ℤ) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ negativeLaplaceMellinFrequency k *
        (boseFinitePartLargeKernel x : ℂ)) (Ioi 1) := by
  have h := integrableOn_large_negativeLaplaceMellinFrequency k
  apply h.congr_fun
  · intro x hx
    change 1 < x at hx
    unfold boseFinitePartLargeKernel
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
    have hpow : (x : ℂ) ^ negativeLaplaceMellinFrequency k / (x : ℂ) =
        (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) := by
      rw [div_eq_mul_inv, ← cpow_neg_one, ← cpow_add _ _ hx0]
      congr 1
    push_cast
    rw [← hpow]
    ring
  · exact measurableSet_Ioi

/-- The Mellin integrals over the intervals `smallDyadicInterval n` sum to
the integral over `(0,1]`, those intervals being pairwise disjoint with
union `(0,1]`. -/
lemma hasSum_integral_smallDyadicInterval_fourier (k : ℤ) :
    HasSum (fun n : ℕ => ∫ x : ℝ in smallDyadicInterval n,
      (x : ℂ) ^ negativeLaplaceMellinFrequency k *
        (boseFinitePartSmallKernel x : ℂ))
      (∫ x : ℝ in Ioc 0 1,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartSmallKernel x : ℂ)) := by
  have h := hasSum_integral_iUnion
    (f := fun x : ℝ =>
      (x : ℂ) ^ negativeLaplaceMellinFrequency k *
        (boseFinitePartSmallKernel x : ℂ))
    (s := smallDyadicInterval)
    (fun n => measurableSet_Ioc) pairwise_disjoint_smallDyadicInterval
    (by simpa [iUnion_smallDyadicInterval] using
      integrableOn_small_negativeLaplaceMellinFrequency k)
  simpa [iUnion_smallDyadicInterval] using h

/-- The Mellin integrals over the blocks `Ioc (2 ^ n) (2 ^ (n + 1))` sum
to the integral over `(1,∞)`; the half-open `largeDyadicInterval` used in
the proof is traded for `Ioc` up to a null set. -/
lemma hasSum_integral_largeDyadicInterval_fourier (k : ℤ) :
    HasSum (fun n : ℕ => ∫ x : ℝ in Ioc ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)),
      (x : ℂ) ^ negativeLaplaceMellinFrequency k *
        (boseFinitePartLargeKernel x : ℂ))
      (∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartLargeKernel x : ℂ)) := by
  have hIntIci : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ negativeLaplaceMellinFrequency k *
        (boseFinitePartLargeKernel x : ℂ)) (Ici 1) :=
    IntegrableOn.congr_set_ae
      (integrableOn_largeKernel_negativeLaplaceMellinFrequency k) Ioi_ae_eq_Ici.symm
  have h := hasSum_integral_iUnion
    (f := fun x : ℝ =>
      (x : ℂ) ^ negativeLaplaceMellinFrequency k *
        (boseFinitePartLargeKernel x : ℂ))
    (s := largeDyadicInterval)
    (fun n => measurableSet_Ico) pairwise_disjoint_largeDyadicInterval
    (by simpa [iUnion_largeDyadicInterval] using hIntIci)
  have h' := h.congr_fun (fun n => setIntegral_congr_set Ico_ae_eq_Ioc.symm)
  rw [iUnion_largeDyadicInterval] at h'
  rw [setIntegral_congr_set Ioi_ae_eq_Ici]
  exact h'

/-- Continuity of the Fourier weight, used throughout for interval
integrability of the products it multiplies. -/
lemma continuous_negativeLaplaceFourierWeight (k : ℤ) :
    Continuous (negativeLaplaceFourierWeight k) := by
  unfold negativeLaplaceFourierWeight
  fun_prop

/-- Termwise integration of `negativeLaplaceLog (2 ^ t)` over one period:
the weighted integrals of the terms sum to the weighted integral of the
series, by dominated convergence against the geometric bound `1 / 2 ^ n`,
which holds on `[0,1]`. -/
lemma hasSum_intervalIntegral_negativeLaplaceTerm_fourier (k : ℤ) :
    HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceTerm ((2 : ℝ) ^ t) n : ℂ))
      (∫ t : ℝ in (0 : ℝ)..1,
        negativeLaplaceFourierWeight k t *
          (negativeLaplaceLog ((2 : ℝ) ^ t) : ℂ)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n : ℕ => fun _ : ℝ => 1 / (2 : ℝ) ^ n)
  · intro n
    exact ((continuous_negativeLaplaceFourierWeight k).mul
      (continuous_ofReal.comp
        (continuous_negativeLaplaceTerm_two_rpow n))).aestronglyMeasurable
  · intro n
    filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht1 : t ≤ 1 := ht.2
    rw [norm_mul, norm_negativeLaplaceFourierWeight, one_mul,
      norm_real, Real.norm_eq_abs]
    refine (abs_negativeLaplaceTerm_le ((2 : ℝ) ^ t)
      (Real.rpow_pos_of_pos (by norm_num) _) n).trans ?_
    have hs : (2 : ℝ) ^ t ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) ht1
    calc
      (2 : ℝ) ^ t / 2 / 2 ^ n ≤ 2 / 2 / 2 ^ n := by gcongr
      _ = 1 / 2 ^ n := by ring
  · filter_upwards with t ht
    have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa [one_div, inv_pow] using hgeom
  · simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ =>
        ∑' n : ℕ, 1 / (2 : ℝ) ^ n) volume 0 1)
  · filter_upwards with t ht
    exact ((Complex.hasSum_ofReal.mpr
      (summable_negativeLaplaceTerm ((2 : ℝ) ^ t)
        (Real.rpow_pos_of_pos (by norm_num) _)).hasSum).mul_left
          (negativeLaplaceFourierWeight k t))

/-- Termwise integration of `negativeLaplaceForwardTail (2 ^ t)` over one
period, by dominated convergence against the geometric bound
`r ^ (n + 1) / (1 - r)` with `r = exp (-1)`, which holds on `[0,1]`. -/
lemma hasSum_intervalIntegral_negativeLaplaceForwardTerm_fourier (k : ℤ) :
    HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n : ℂ))
      (∫ t : ℝ in (0 : ℝ)..1,
        negativeLaplaceFourierWeight k t *
          (negativeLaplaceForwardTail ((2 : ℝ) ^ t) : ℂ)) := by
  let r : ℝ := Real.exp (-1)
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hmajor : Summable (fun n : ℕ => r ^ (n + 1) / (1 - r)) := by
    have hgeom : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr0 hr1
    refine (hgeom.mul_left (r / (1 - r))).congr ?_
    intro n
    rw [pow_succ']
    ring
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n : ℕ => fun _ : ℝ => r ^ (n + 1) / (1 - r))
  · intro n
    exact ((continuous_negativeLaplaceFourierWeight k).mul
      (continuous_ofReal.comp
        (continuous_negativeLaplaceForwardTerm_two_rpow n))).aestronglyMeasurable
  · intro n
    filter_upwards with t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : 0 ≤ t := ht.1.le
    have hs1 : 1 ≤ (2 : ℝ) ^ t := Real.one_le_rpow (by norm_num) ht0
    rw [norm_mul, norm_negativeLaplaceFourierWeight, one_mul,
      norm_real, Real.norm_eq_abs]
    refine (abs_negativeLaplaceForwardTerm_le ((2 : ℝ) ^ t)
      (Real.rpow_pos_of_pos (by norm_num) _) n).trans ?_
    have hexp : Real.exp (-((2 : ℝ) ^ t)) ≤ r := by
      dsimp [r]
      exact Real.exp_le_exp.mpr (by linarith)
    have hnum : Real.exp (-((2 : ℝ) ^ t)) ^ (n + 1) ≤ r ^ (n + 1) :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hexp _
    have hden : 0 < 1 - r := sub_pos.mpr hr1
    have hden' : 1 - r ≤ 1 - Real.exp (-((2 : ℝ) ^ t)) :=
      sub_le_sub_left hexp 1
    exact (div_le_div_of_nonneg_left
      (pow_nonneg (Real.exp_nonneg _) _) hden hden').trans
        (div_le_div_of_nonneg_right hnum hden.le)
  · filter_upwards with t ht
    exact hmajor
  · simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ =>
        ∑' n : ℕ, r ^ (n + 1) / (1 - r)) volume 0 1)
  · filter_upwards with t ht
    exact ((Complex.hasSum_ofReal.mpr
      (summable_negativeLaplaceForwardTerm ((2 : ℝ) ^ t)
        (Real.rpow_pos_of_pos (by norm_num) _)).hasSum).mul_left
          (negativeLaplaceFourierWeight k t))

/-- The weighted integral of `negativeLaplaceLog (2 ^ t)` over one period
is the Mellin integral of `boseFinitePartSmallKernel` over `(0,1]`, divided
by `log 2`: the two dyadic sums above have the same terms. -/
theorem intervalIntegral_negativeLaplaceLog_fourier (k : ℤ) :
    (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceLog ((2 : ℝ) ^ t) : ℂ)) =
      (∫ x : ℝ in Ioc 0 1,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartSmallKernel x : ℂ)) / (Real.log 2 : ℂ) := by
  have hlog2 : (Real.log 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (Real.log_pos (by norm_num)).ne'
  have hdy := (hasSum_integral_smallDyadicInterval_fourier k).div_const
    (Real.log 2 : ℂ)
  have hdy' : HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceTerm ((2 : ℝ) ^ t) n : ℂ))
      ((∫ x : ℝ in Ioc 0 1,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartSmallKernel x : ℂ)) / (Real.log 2 : ℂ)) := by
    apply hdy.congr_fun
    intro n
    have hn := intervalIntegral_negativeLaplaceTerm_fourier k n
    rw [eq_div_iff hlog2]
    calc
      (∫ t : ℝ in (0 : ℝ)..1,
          negativeLaplaceFourierWeight k t *
            (negativeLaplaceTerm ((2 : ℝ) ^ t) n : ℂ)) *
            (Real.log 2 : ℂ) =
          (Real.log 2 : ℂ) * (∫ t : ℝ in (0 : ℝ)..1,
            negativeLaplaceFourierWeight k t *
              (negativeLaplaceTerm ((2 : ℝ) ^ t) n : ℂ)) := by ring
      _ = ∫ x : ℝ in smallDyadicInterval n,
          (x : ℂ) ^ negativeLaplaceMellinFrequency k *
            (boseFinitePartSmallKernel x : ℂ) := hn
  exact (hasSum_intervalIntegral_negativeLaplaceTerm_fourier k).unique hdy'

/-- The weighted integral of `negativeLaplaceForwardTail (2 ^ t)` over one
period is the Mellin integral of `boseFinitePartLargeKernel` over `(1,∞)`,
divided by `log 2`. -/
theorem intervalIntegral_negativeLaplaceForwardTail_fourier (k : ℤ) :
    (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceForwardTail ((2 : ℝ) ^ t) : ℂ)) =
      (∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartLargeKernel x : ℂ)) / (Real.log 2 : ℂ) := by
  have hlog2 : (Real.log 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (Real.log_pos (by norm_num)).ne'
  have hdy := (hasSum_integral_largeDyadicInterval_fourier k).div_const
    (Real.log 2 : ℂ)
  have hdy' : HasSum (fun n : ℕ => ∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n : ℂ))
      ((∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartLargeKernel x : ℂ)) / (Real.log 2 : ℂ)) := by
    apply hdy.congr_fun
    intro n
    have hn := intervalIntegral_negativeLaplaceForwardTerm_fourier k n
    rw [eq_div_iff hlog2]
    calc
      (∫ t : ℝ in (0 : ℝ)..1,
          negativeLaplaceFourierWeight k t *
            (negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n : ℂ)) *
            (Real.log 2 : ℂ) =
          (Real.log 2 : ℂ) * (∫ t : ℝ in (0 : ℝ)..1,
            negativeLaplaceFourierWeight k t *
              (negativeLaplaceForwardTerm ((2 : ℝ) ^ t) n : ℂ)) := by ring
      _ = ∫ x : ℝ in Ioc ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)),
          (x : ℂ) ^ negativeLaplaceMellinFrequency k *
            (boseFinitePartLargeKernel x : ℂ) := hn
  exact (hasSum_intervalIntegral_negativeLaplaceForwardTerm_fourier k).unique hdy'

/-- At the frequency `negativeLaplaceMellinFrequency k` the Mellin
transform splits at `1` into the small-kernel integral over `(0,1]` and the
large-kernel integral over `(1,∞)`, matching the two previous lemmas. -/
lemma mellin_boseRegularizedMellinKernel_split_frequency (k : ℤ) :
    mellin boseRegularizedMellinKernel (negativeLaplaceMellinFrequency k) =
      (∫ x : ℝ in Ioc 0 1,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartSmallKernel x : ℂ)) +
      ∫ x : ℝ in Ioi 1,
        (x : ℂ) ^ negativeLaplaceMellinFrequency k *
          (boseFinitePartLargeKernel x : ℂ) := by
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) *
      boseRegularizedMellinKernel x
  have hconv := mellinConvergent_boseRegularizedMellinKernel
    (negativeLaplaceMellinFrequency k) (by
      rw [negativeLaplaceMellinFrequency_re]
      norm_num)
  rw [MellinConvergent] at hconv
  have hsmall : IntegrableOn g (Ioc 0 1) :=
    hconv.mono_set (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 by exact Ioc_subset_Ioi_self)
  have hlarge : IntegrableOn g (Ioi 1) :=
    hconv.mono_set (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro x hx
      change 1 < x at hx
      exact zero_lt_one.trans hx)
  have hdis : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    intro x hxsmall hxlarge
    exact (not_lt_of_ge hxsmall.2) hxlarge
  have hsplit := integral_union_ae hdis.aedisjoint
    measurableSet_Ioi.nullMeasurableSet hsmall hlarge
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hsplit
  rw [mellin]
  change (∫ x : ℝ in Ioi 0, g x) = _
  rw [hsplit]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
      dsimp [g]
      rw [boseRegularizedMellinKernel, if_pos hx.2]
      have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
      have hpow :
          (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) * (x : ℂ) =
            (x : ℂ) ^ negativeLaplaceMellinFrequency k := by
        calc
          (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) * (x : ℂ) =
              (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) *
                (x : ℂ) ^ (1 : ℂ) := by rw [cpow_one]
          _ = (x : ℂ) ^ ((negativeLaplaceMellinFrequency k - 1) + 1) := by
            rw [cpow_add _ _ hx0]
          _ = (x : ℂ) ^ negativeLaplaceMellinFrequency k := by ring_nf
      push_cast
      rw [← mul_assoc, hpow])
  · exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
      change 1 < x at hx
      dsimp [g]
      rw [boseRegularizedMellinKernel, if_neg (not_le.mpr hx)]
      unfold boseFinitePartLargeKernel
      have hx0 : (x : ℂ) ≠ 0 :=
        ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'
      have hpow :
          (x : ℂ) ^ negativeLaplaceMellinFrequency k / (x : ℂ) =
            (x : ℂ) ^ (negativeLaplaceMellinFrequency k - 1) := by
        rw [div_eq_mul_inv, ← cpow_neg_one, ← cpow_add _ _ hx0]
        congr 1
      push_cast
      rw [← hpow]
      ring)

/-- The two nonelementary pieces of the periodic correction assemble into
a single Mellin transform: the weighted integral of
`negativeLaplaceLog (2 ^ t) + negativeLaplaceForwardTail (2 ^ t)` over one
period is `mellin boseRegularizedMellinKernel` at the frequency, divided by
`log 2`.  No hypothesis on `k` is needed. -/
theorem intervalIntegral_negativeLaplaceLog_add_tail_fourier (k : ℤ) :
    (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        ((negativeLaplaceLog ((2 : ℝ) ^ t) +
          negativeLaplaceForwardTail ((2 : ℝ) ^ t) : ℝ) : ℂ)) =
      mellin boseRegularizedMellinKernel (negativeLaplaceMellinFrequency k) /
        (Real.log 2 : ℂ) := by
  rw [show (fun t : ℝ =>
      negativeLaplaceFourierWeight k t *
        ((negativeLaplaceLog ((2 : ℝ) ^ t) +
          negativeLaplaceForwardTail ((2 : ℝ) ^ t) : ℝ) : ℂ)) =
      fun t : ℝ =>
        negativeLaplaceFourierWeight k t *
            (negativeLaplaceLog ((2 : ℝ) ^ t) : ℂ) +
          negativeLaplaceFourierWeight k t *
            (negativeLaplaceForwardTail ((2 : ℝ) ^ t) : ℂ) by
    funext t
    push_cast
    ring]
  have hf : IntervalIntegrable (fun t : ℝ =>
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceLog ((2 : ℝ) ^ t) : ℂ)) volume 0 1 := by
    have hc : Continuous (fun t : ℝ =>
        negativeLaplaceFourierWeight k t *
          (negativeLaplaceLog ((2 : ℝ) ^ t) : ℂ)) := by
      exact (continuous_negativeLaplaceFourierWeight k).mul
        (continuous_ofReal.comp continuous_negativeLaplaceLog_two_rpow)
    exact hc.intervalIntegrable 0 1
  have hg : IntervalIntegrable (fun t : ℝ =>
      negativeLaplaceFourierWeight k t *
        (negativeLaplaceForwardTail ((2 : ℝ) ^ t) : ℂ)) volume 0 1 := by
    have hc : Continuous (fun t : ℝ =>
        negativeLaplaceFourierWeight k t *
          (negativeLaplaceForwardTail ((2 : ℝ) ^ t) : ℂ)) := by
      exact (continuous_negativeLaplaceFourierWeight k).mul
        (continuous_ofReal.comp continuous_negativeLaplaceForwardTail_two_rpow)
    exact hc.intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hf hg]
  rw [intervalIntegral_negativeLaplaceLog_fourier,
    intervalIntegral_negativeLaplaceForwardTail_fourier,
    ← add_div, ← mellin_boseRegularizedMellinKernel_split_frequency]

/-- Mathlib's character `fourier (-k)` on `AddCircle 1`, evaluated at the
image of a real number `t`, is the explicit weight
`negativeLaplaceFourierWeight k t`. -/
lemma fourier_neg_coe_eq_negativeLaplaceFourierWeight (k : ℤ) (t : ℝ) :
    @fourier (1 : ℝ) (-k) (t : AddCircle (1 : ℝ)) =
      negativeLaplaceFourierWeight k t := by
  rw [fourier_coe_apply]
  unfold negativeLaplaceFourierWeight
  congr 1
  push_cast
  ring

/-- Mathlib's `fourierCoeffOn zero_lt_one` unfolded on the period `[0,1]`:
for any `f : ℝ → ℂ` the coefficient is the interval integral of `f` against
the explicit weight.  Most coefficient computations below factor through
this. -/
lemma fourierCoeffOn_zero_one_eq_weight_integral
    (f : ℝ → ℂ) (k : ℤ) :
    fourierCoeffOn zero_lt_one f k =
      ∫ t : ℝ in (0 : ℝ)..1,
        negativeLaplaceFourierWeight k t * f t := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div, inv_one, one_smul, smul_eq_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [fourier_coe_apply]
  unfold negativeLaplaceFourierWeight
  congr 2
  push_cast
  norm_num

/-- The Fourier coefficient convention used for the periodic correction:
`∫₀¹ Ψ(t)e^{-2πikt} dt`. -/
noncomputable def negativeLaplacePsiFourierCoeff (k : ℤ) : ℂ :=
  fourierCoeffOn zero_lt_one (fun t : ℝ => (negativeLaplacePsi t : ℂ)) k

/-- The defining coefficient of `Ψ` as an explicit interval integral over
one period. -/
theorem negativeLaplacePsiFourierCoeff_eq_integral (k : ℤ) :
    negativeLaplacePsiFourierCoeff k =
      ∫ t : ℝ in (0 : ℝ)..1,
        negativeLaplaceFourierWeight k t * (negativeLaplacePsi t : ℂ) := by
  exact fourierCoeffOn_zero_one_eq_weight_integral _ k

/-- For `k ≠ 0` the weight integrates to zero over a period, so a constant
summand of the integrand contributes nothing to the coefficient.  Read off
Mathlib's degree-zero Bernoulli Fourier coefficient. -/
lemma intervalIntegral_negativeLaplaceFourierWeight_eq_zero
    (k : ℤ) (hk : k ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1, negativeLaplaceFourierWeight k t) = 0 := by
  have hzero := bernoulli_zero_fourier_coeff hk
  rw [bernoulliFourierCoeff,
    fourierCoeffOn_zero_one_eq_weight_integral] at hzero
  simpa using hzero

/-- For `k ≠ 0` the weighted integral of `t ^ 2 - t` over one period is
`-2 / (2πik) ^ 2`, read off Mathlib's Fourier coefficients of the second
Bernoulli function `bernoulliFun 2 t = t ^ 2 - t + 1 / 6`. -/
lemma intervalIntegral_quadratic_fourier
    (k : ℤ) (hk : k ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t * ((t ^ 2 - t : ℝ) : ℂ)) =
      -(2 : ℂ) / (2 * (Real.pi : ℂ) * I * (k : ℂ)) ^ 2 := by
  have htwo := bernoulliFourierCoeff_eq (k := 2) (by norm_num) k
  rw [bernoulliFourierCoeff,
    fourierCoeffOn_zero_one_eq_weight_integral] at htwo
  simp only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at htwo
  have hw : IntervalIntegrable (negativeLaplaceFourierWeight k) volume 0 1 :=
    (continuous_negativeLaplaceFourierWeight k).intervalIntegrable 0 1
  have hp : IntervalIntegrable (fun t : ℝ =>
      negativeLaplaceFourierWeight k t * ((t ^ 2 - t : ℝ) : ℂ)) volume 0 1 := by
    have hc : Continuous (fun t : ℝ =>
        negativeLaplaceFourierWeight k t * ((t ^ 2 - t : ℝ) : ℂ)) := by
      exact (continuous_negativeLaplaceFourierWeight k).mul
        (continuous_ofReal.comp ((continuous_id.pow 2).sub continuous_id))
    exact hc.intervalIntegrable 0 1
  have hsplit :
      (∫ t : ℝ in (0 : ℝ)..1,
        negativeLaplaceFourierWeight k t * (bernoulliFun 2 t : ℂ)) =
        (∫ t : ℝ in (0 : ℝ)..1,
          negativeLaplaceFourierWeight k t * ((t ^ 2 - t : ℝ) : ℂ)) +
          (6 : ℂ)⁻¹ *
            ∫ t : ℝ in (0 : ℝ)..1, negativeLaplaceFourierWeight k t := by
    rw [show (fun t : ℝ =>
        negativeLaplaceFourierWeight k t * (bernoulliFun 2 t : ℂ)) =
      fun t : ℝ =>
        negativeLaplaceFourierWeight k t * ((t ^ 2 - t : ℝ) : ℂ) +
          (6 : ℂ)⁻¹ * negativeLaplaceFourierWeight k t by
      funext t
      rw [bernoulliFun_two]
      push_cast
      ring]
    rw [intervalIntegral.integral_add hp
      (hw.const_mul (6 : ℂ)⁻¹)]
    rw [intervalIntegral.integral_const_mul]
  rw [hsplit, intervalIntegral_negativeLaplaceFourierWeight_eq_zero k hk,
    mul_zero, add_zero] at htwo
  exact htwo

/-- For `k ≠ 0` the Mellin frequency is nonzero, which is what makes the
`1 / s ^ 2` term of `gammaZetaMellinFinitePart` and the reciprocals below
meaningful. -/
lemma negativeLaplaceMellinFrequency_ne_zero
    (k : ℤ) (hk : k ≠ 0) :
    negativeLaplaceMellinFrequency k ≠ 0 := by
  unfold negativeLaplaceMellinFrequency
  apply div_ne_zero
  · apply neg_ne_zero.mpr
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num)
        (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
      (Int.cast_ne_zero.mpr hk)
  · exact ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'

/-- For `k ≠ 0` the elementary piece `log 2 / 2 * (t ^ 2 - t)` of the
periodic correction contributes exactly
`-(1 / negativeLaplaceMellinFrequency k ^ 2) / log 2`, the term that
cancels the `1 / s ^ 2` regularizer inside
`gammaZetaMellinFinitePart`. -/
lemma intervalIntegral_quadraticCorrection_fourier
    (k : ℤ) (hk : k ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t *
        ((Real.log 2 / 2 * (t ^ 2 - t) : ℝ) : ℂ)) =
      -(1 / negativeLaplaceMellinFrequency k ^ 2) /
        (Real.log 2 : ℂ) := by
  rw [show (fun t : ℝ =>
      negativeLaplaceFourierWeight k t *
        ((Real.log 2 / 2 * (t ^ 2 - t) : ℝ) : ℂ)) =
      fun t : ℝ => (Real.log 2 / 2 : ℂ) *
        (negativeLaplaceFourierWeight k t * ((t ^ 2 - t : ℝ) : ℂ)) by
    funext t
    push_cast
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_quadratic_fourier k hk]
  unfold negativeLaplaceMellinFrequency
  have hlog : (Real.log 2 : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hkC : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  field_simp [hlog, hpi, hkC, I_ne_zero]

/-- For `k ≠ 0` the whole coefficient integral of `Ψ` is the Mellin
transform at the frequency minus `1 / negativeLaplaceMellinFrequency k ^ 2`,
both divided by `log 2`.  The three components of `negativeLaplacePsi`
contribute the Mellin piece, the quadratic piece, and nothing at all for
the constant mean. -/
lemma intervalIntegral_negativeLaplacePsi_fourier
    (k : ℤ) (hk : k ≠ 0) :
    (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight k t * (negativeLaplacePsi t : ℂ)) =
      mellin boseRegularizedMellinKernel (negativeLaplaceMellinFrequency k) /
          (Real.log 2 : ℂ) -
        (1 / negativeLaplaceMellinFrequency k ^ 2) /
          (Real.log 2 : ℂ) := by
  let A : ℝ → ℂ := fun t =>
    negativeLaplaceFourierWeight k t *
      ((negativeLaplaceLog ((2 : ℝ) ^ t) +
        negativeLaplaceForwardTail ((2 : ℝ) ^ t) : ℝ) : ℂ)
  let B : ℝ → ℂ := fun t =>
    negativeLaplaceFourierWeight k t *
      ((Real.log 2 / 2 * (t ^ 2 - t) : ℝ) : ℂ)
  let D : ℝ → ℂ := fun t =>
    -(negativeLaplacePeriodicMean : ℂ) * negativeLaplaceFourierWeight k t
  have hpoint : (fun t : ℝ =>
      negativeLaplaceFourierWeight k t * (negativeLaplacePsi t : ℂ)) =
      fun t : ℝ => A t + B t + D t := by
    funext t
    rw [negativeLaplacePsi,
      negativeLaplacePeriodicCorrection_eq_components]
    dsimp [A, B, D]
    push_cast
    ring
  have hA : IntervalIntegrable A volume 0 1 := by
    have hc : Continuous A := by
      dsimp [A]
      exact (continuous_negativeLaplaceFourierWeight k).mul
        (continuous_ofReal.comp
          (continuous_negativeLaplaceLog_two_rpow.add
            continuous_negativeLaplaceForwardTail_two_rpow))
    exact hc.intervalIntegrable 0 1
  have hB : IntervalIntegrable B volume 0 1 := by
    have hc : Continuous B := by
      dsimp [B]
      exact (continuous_negativeLaplaceFourierWeight k).mul
        (continuous_ofReal.comp
          (continuous_const.mul ((continuous_id.pow 2).sub continuous_id)))
    exact hc.intervalIntegrable 0 1
  have hD : IntervalIntegrable D volume 0 1 := by
    dsimp [D]
    exact ((continuous_negativeLaplaceFourierWeight k).const_mul
      (-(negativeLaplacePeriodicMean : ℂ))).intervalIntegrable 0 1
  rw [hpoint]
  rw [intervalIntegral.integral_add (hA.add hB) hD,
    intervalIntegral.integral_add hA hB]
  have hDzero : (∫ t : ℝ in (0 : ℝ)..1, D t) = 0 := by
    dsimp [D]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_negativeLaplaceFourierWeight_eq_zero k hk, mul_zero]
  rw [show (∫ t : ℝ in (0 : ℝ)..1, A t) =
      mellin boseRegularizedMellinKernel (negativeLaplaceMellinFrequency k) /
        (Real.log 2 : ℂ) by
    exact intervalIntegral_negativeLaplaceLog_add_tail_fourier k]
  rw [show (∫ t : ℝ in (0 : ℝ)..1, B t) =
      -(1 / negativeLaplaceMellinFrequency k ^ 2) /
        (Real.log 2 : ℂ) by
    exact intervalIntegral_quadraticCorrection_fourier k hk]
  rw [hDzero]
  ring

/-- Every nonconstant Fourier coefficient of the zero-mean correction, in the
Mathlib convention `e^{-2πikt}`.  Here
`negativeLaplaceMellinFrequency k = -2πik / log 2`. -/
theorem negativeLaplacePsiFourierCoeff_eq_gamma_zeta
    (k : ℤ) (hk : k ≠ 0) :
    negativeLaplacePsiFourierCoeff k =
      -Gamma (negativeLaplaceMellinFrequency k) *
          riemannZeta (1 + negativeLaplaceMellinFrequency k) /
        (Real.log 2 : ℂ) := by
  rw [negativeLaplacePsiFourierCoeff_eq_integral,
    intervalIntegral_negativeLaplacePsi_fourier k hk]
  rw [mellin_boseRegularizedMellinKernel_eq_gammaZeta_of_re_zero
    (negativeLaplaceMellinFrequency k)
    (negativeLaplaceMellinFrequency_re k)
    (negativeLaplaceMellinFrequency_ne_zero k hk)]
  unfold gammaZetaMellinFinitePart
  ring

/-- The usual positive frequency `χₖ = 2πik / log 2`; the Mellin frequency
used above is `-χₖ`. -/
noncomputable def negativeLaplaceFourierFrequency (k : ℤ) : ℂ :=
  2 * (Real.pi : ℂ) * I * (k : ℂ) / Real.log 2

/-- The two frequency conventions differ by a sign:
`negativeLaplaceMellinFrequency k = -negativeLaplaceFourierFrequency k`. -/
lemma negativeLaplaceMellinFrequency_eq_neg_fourierFrequency (k : ℤ) :
    negativeLaplaceMellinFrequency k = -negativeLaplaceFourierFrequency k := by
  unfold negativeLaplaceMellinFrequency negativeLaplaceFourierFrequency
  ring

/-- Requested `χₖ` form of the nonzero Fourier coefficients:
`-Γ(-χₖ) ζ(1-χₖ) / log 2`. -/
theorem negativeLaplacePsiFourierCoeff_eq_neg_gamma_zeta
    (k : ℤ) (hk : k ≠ 0) :
    negativeLaplacePsiFourierCoeff k =
      -Gamma (-negativeLaplaceFourierFrequency k) *
          riemannZeta (1 - negativeLaplaceFourierFrequency k) /
        (Real.log 2 : ℂ) := by
  rw [negativeLaplacePsiFourierCoeff_eq_gamma_zeta k hk,
    negativeLaplaceMellinFrequency_eq_neg_fourierFrequency]
  ring

/-- The zero mode vanishes, which is exactly the normalization built into
`negativeLaplacePsi`. -/
theorem negativeLaplacePsiFourierCoeff_zero :
    negativeLaplacePsiFourierCoeff 0 = 0 := by
  rw [negativeLaplacePsiFourierCoeff_eq_integral]
  have hweight : ∀ t : ℝ, negativeLaplaceFourierWeight 0 t = 1 := by
    intro t
    simp [negativeLaplaceFourierWeight]
  rw [show (fun t : ℝ =>
      negativeLaplaceFourierWeight 0 t * (negativeLaplacePsi t : ℂ)) =
      fun t : ℝ => (negativeLaplacePsi t : ℂ) by
    funext t
    rw [hweight]
    simp]
  rw [intervalIntegral.integral_ofReal]
  rw [integral_negativeLaplacePsi_zero]
  simp

/-- For `k ≠ 0` the value of `Γ` at the Mellin frequency is nonzero: `Γ`
never vanishes, and the frequency is not a nonpositive integer because it
is purely imaginary and nonzero. -/
lemma Gamma_negativeLaplaceMellinFrequency_ne_zero
    (k : ℤ) (hk : k ≠ 0) :
    Gamma (negativeLaplaceMellinFrequency k) ≠ 0 := by
  apply Gamma_ne_zero
  intro m hm
  have hre : (0 : ℝ) = -(m : ℝ) := by
    simpa [negativeLaplaceMellinFrequency_re] using congrArg re hm
  have hmR : (m : ℝ) = 0 := by linarith
  have hm0 : m = 0 := by exact_mod_cast hmR
  subst m
  exact negativeLaplaceMellinFrequency_ne_zero k hk (by simpa using hm)

/-- The value `riemannZeta (1 + negativeLaplaceMellinFrequency k)` is
nonzero for every `k`, since the argument has real part one and Mathlib's
`riemannZeta_ne_zero_of_one_le_re` applies there. -/
lemma riemannZeta_one_add_negativeLaplaceMellinFrequency_ne_zero
    (k : ℤ) :
    riemannZeta (1 + negativeLaplaceMellinFrequency k) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  rw [add_re, one_re, negativeLaplaceMellinFrequency_re]
  norm_num

/-- In fact every nonzero Fourier mode of `Ψ` is nonzero. -/
theorem negativeLaplacePsiFourierCoeff_ne_zero
    (k : ℤ) (hk : k ≠ 0) :
    negativeLaplacePsiFourierCoeff k ≠ 0 := by
  rw [negativeLaplacePsiFourierCoeff_eq_gamma_zeta k hk]
  apply div_ne_zero
  · exact mul_ne_zero
      (neg_ne_zero.mpr (Gamma_negativeLaplaceMellinFrequency_ne_zero k hk))
      (riemannZeta_one_add_negativeLaplaceMellinFrequency_ne_zero k)
  · exact ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'

/-- The first mode is nonzero; this single mode is all that
`negativeLaplacePsi_not_constant` consumes. -/
theorem negativeLaplacePsiFourierCoeff_one_ne_zero :
    negativeLaplacePsiFourierCoeff 1 ≠ 0 :=
  negativeLaplacePsiFourierCoeff_ne_zero 1 one_ne_zero

/-- The periodic fluctuation is genuinely nonconstant. -/
theorem negativeLaplacePsi_not_constant :
    ¬ ∃ c : ℝ, ∀ t : ℝ, negativeLaplacePsi t = c := by
  rintro ⟨c, hconst⟩
  apply negativeLaplacePsiFourierCoeff_one_ne_zero
  rw [negativeLaplacePsiFourierCoeff_eq_integral]
  calc
    (∫ t : ℝ in (0 : ℝ)..1,
      negativeLaplaceFourierWeight 1 t * (negativeLaplacePsi t : ℂ)) =
        (negativeLaplacePsi 0 : ℂ) *
          ∫ t : ℝ in (0 : ℝ)..1,
            negativeLaplaceFourierWeight 1 t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [hconst t, hconst 0]
      ring
    _ = 0 := by
      rw [intervalIntegral_negativeLaplaceFourierWeight_eq_zero 1 one_ne_zero,
        mul_zero]

/-- Integration by parts twice, for `k ≠ 0`: the coefficient of `Ψ` is
`(1 / (-2πik)) ^ 2` times the coefficient of `deriv (deriv Ψ)`.  The
boundary terms cancel because `Ψ` and its derivative are one-periodic. -/
lemma negativeLaplacePsiFourierCoeff_eq_secondDerivCoeff
    (k : ℤ) (hk : k ≠ 0) :
    negativeLaplacePsiFourierCoeff k =
      (1 / (-2 * (Real.pi : ℂ) * I * (k : ℂ))) ^ 2 *
        fourierCoeffOn zero_lt_one
          (fun t : ℝ => ((deriv (deriv negativeLaplacePsi) t : ℝ) : ℂ)) k := by
  have hfirst := fourierCoeffOn_of_hasDerivAt zero_lt_one hk
    (f := fun t : ℝ => (negativeLaplacePsi t : ℂ))
    (f' := fun t : ℝ => ((deriv negativeLaplacePsi t : ℝ) : ℂ))
    (fun x hx => (negativeLaplacePsi_hasDerivAt x).ofReal_comp)
    ((continuous_ofReal.comp continuous_deriv_negativeLaplacePsi).intervalIntegrable 0 1)
  have hsecond := fourierCoeffOn_of_hasDerivAt zero_lt_one hk
    (f := fun t : ℝ => ((deriv negativeLaplacePsi t : ℝ) : ℂ))
    (f' := fun t : ℝ => ((deriv (deriv negativeLaplacePsi) t : ℝ) : ℂ))
    (fun x hx => (negativeLaplacePsi_deriv_hasDerivAt x).ofReal_comp)
    ((continuous_ofReal.comp continuous_secondDeriv_negativeLaplacePsi).intervalIntegrable 0 1)
  have hpend : negativeLaplacePsi 1 = negativeLaplacePsi 0 := by
    simpa using negativeLaplacePsi_add_one 0
  have hderivend : deriv negativeLaplacePsi 1 = deriv negativeLaplacePsi 0 := by
    simpa using negativeLaplacePsi_deriv_add_one 0
  rw [hpend] at hfirst
  rw [hderivend] at hsecond
  norm_num at hfirst hsecond
  unfold negativeLaplacePsiFourierCoeff
  rw [hfirst, hsecond]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hkC : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  field_simp [hpi, hkC, I_ne_zero]
  rw [show I ^ 4 = (1 : ℂ) by norm_num [pow_succ], one_mul]

/-- The Fourier coefficients of `deriv (deriv Ψ)` are bounded uniformly in
`k` by the sup bound on `Ψ''` from `FabiusFunction.PeriodicRegularity`,
because the weight has modulus one on a period of length one. -/
lemma exists_bound_negativeLaplacePsi_secondDerivFourierCoeff :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ,
      ‖fourierCoeffOn zero_lt_one
        (fun t : ℝ => ((deriv (deriv negativeLaplacePsi) t : ℝ) : ℂ)) k‖ ≤ C := by
  rcases exists_bound_abs_secondDeriv_negativeLaplacePsi with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, fun k => ?_⟩
  rw [fourierCoeffOn_zero_one_eq_weight_integral]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => negativeLaplaceFourierWeight k t *
      ((deriv (deriv negativeLaplacePsi) t : ℝ) : ℂ))
      (a := 0) (b := 1) (C := C) (by
      intro t ht
      rw [norm_mul, norm_negativeLaplaceFourierWeight, one_mul,
        norm_real, Real.norm_eq_abs]
      exact hC t)
  norm_num at hbound ⊢
  exact hbound

/-- The elementary norm computation
`‖1 / (-2πik)‖ ^ 2 = (1 / (4 * π ^ 2)) * (1 / k ^ 2)`, in the shape needed
for the `O(1 / k ^ 2)` majorant.  Both sides vanish at `k = 0` under Lean's
`1 / 0 = 0` convention. -/
lemma norm_fourierDenominator_inv_sq (k : ℤ) :
    ‖(1 / (-2 * (Real.pi : ℂ) * I * (k : ℂ)))‖ ^ 2 =
      (1 / (4 * Real.pi ^ 2)) * (1 / (k : ℝ) ^ 2) := by
  simp only [norm_div, norm_one, norm_mul, norm_neg, norm_ofNat,
    norm_real, norm_I, norm_intCast, mul_one]
  rw [Real.norm_eq_abs]
  rw [div_pow]
  rw [show (2 * |Real.pi| * |(k : ℝ)|) ^ 2 =
      4 * Real.pi ^ 2 * (k : ℝ) ^ 2 by
    rw [abs_of_pos Real.pi_pos]
    nlinarith [sq_abs (k : ℝ)]
  ]
  ring

/-- Absolute summability of the coefficients.  The decay used is only the
`O(1 / k ^ 2)` produced by the two integrations by parts against the bound
on `Ψ''`; no exponential decay of `Γ` is claimed. -/
theorem summable_negativeLaplacePsiFourierCoeff :
    Summable negativeLaplacePsiFourierCoeff := by
  rcases exists_bound_negativeLaplacePsi_secondDerivFourierCoeff with
    ⟨C, hC0, hC⟩
  let A : ℝ := C * (1 / (4 * Real.pi ^ 2))
  have hmajor : Summable (fun k : ℤ =>
      A * (1 / (k : ℝ) ^ 2)) := by
    exact (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left A
  apply Summable.of_norm_bounded hmajor
  intro k
  by_cases hk : k = 0
  · subst k
    simp [negativeLaplacePsiFourierCoeff_zero, A]
  · rw [negativeLaplacePsiFourierCoeff_eq_secondDerivCoeff k hk,
      norm_mul, norm_pow, norm_fourierDenominator_inv_sq]
    calc
      (1 / (4 * Real.pi ^ 2) * (1 / (k : ℝ) ^ 2)) *
          ‖fourierCoeffOn zero_lt_one
            (fun t : ℝ => ((deriv (deriv negativeLaplacePsi) t : ℝ) : ℂ)) k‖ ≤
        (1 / (4 * Real.pi ^ 2) * (1 / (k : ℝ) ^ 2)) * C := by
          exact mul_le_mul_of_nonneg_left (hC k) (by positivity)
      _ = A * (1 / (k : ℝ) ^ 2) := by
        dsimp [A]
        ring

/-- The complex-valued `Ψ` is one-periodic; this is the datum that
`negativeLaplacePsiCircle` lifts to `AddCircle 1`. -/
lemma negativeLaplacePsi_complex_periodic :
    Function.Periodic (fun t : ℝ => (negativeLaplacePsi t : ℂ)) 1 := by
  intro t
  change (negativeLaplacePsi (t + 1) : ℂ) =
    (negativeLaplacePsi t : ℂ)
  rw [negativeLaplacePsi_add_one]

/-- The normalized correction as a continuous function on the unit circle. -/
noncomputable def negativeLaplacePsiCircle : C(AddCircle (1 : ℝ), ℂ) where
  toFun := negativeLaplacePsi_complex_periodic.lift
  continuous_toFun := continuous_coinduced_dom.mpr (by
    change Continuous (fun t : ℝ => (negativeLaplacePsi t : ℂ))
    exact continuous_ofReal.comp continuous_negativeLaplacePsi)

@[simp] lemma negativeLaplacePsiCircle_coe (t : ℝ) :
    negativeLaplacePsiCircle (t : AddCircle (1 : ℝ)) =
      (negativeLaplacePsi t : ℂ) := by
  rfl

/-- Mathlib's `fourierCoeff` of the circle-valued `Ψ` agrees with
`negativeLaplacePsiFourierCoeff`, so the coefficients computed above are
the ones Mathlib's Fourier inversion theorem sums. -/
lemma fourierCoeff_negativeLaplacePsiCircle (k : ℤ) :
    fourierCoeff negativeLaplacePsiCircle k =
      negativeLaplacePsiFourierCoeff k := by
  rw [fourierCoeff_eq_intervalIntegral negativeLaplacePsiCircle k 0]
  rw [negativeLaplacePsiFourierCoeff_eq_integral]
  norm_num only [zero_add, one_div, inv_one, one_smul, smul_eq_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [negativeLaplacePsiCircle_coe]
  rw [fourier_coe_apply]
  unfold negativeLaplaceFourierWeight
  congr 2
  push_cast
  norm_num

/-- Summability transported to `negativeLaplacePsiCircle`, the hypothesis
of `has_pointwise_sum_fourier_series_of_summable`. -/
theorem summable_fourierCoeff_negativeLaplacePsiCircle :
    Summable (fourierCoeff negativeLaplacePsiCircle) :=
  summable_negativeLaplacePsiFourierCoeff.congr
    (fun k => (fourierCoeff_negativeLaplacePsiCircle k).symm)

/-- Pointwise Fourier reconstruction on `AddCircle 1`.  The real-line form
`hasSum_negativeLaplacePsi_fourierSeries` is this statement pulled back
along `t ↦ (t : AddCircle 1)`. -/
theorem hasSum_negativeLaplacePsi_fourierSeries_circle
    (x : AddCircle (1 : ℝ)) :
    HasSum (fun k : ℤ =>
      negativeLaplacePsiFourierCoeff k • fourier k x)
      (negativeLaplacePsiCircle x) := by
  simpa only [fourierCoeff_negativeLaplacePsiCircle] using
    has_pointwise_sum_fourier_series_of_summable
      summable_fourierCoeff_negativeLaplacePsiCircle x

/-- Absolutely convergent Fourier reconstruction on the real line. -/
theorem hasSum_negativeLaplacePsi_fourierSeries (t : ℝ) :
    HasSum (fun k : ℤ =>
      negativeLaplacePsiFourierCoeff k *
        exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ)))
      (negativeLaplacePsi t : ℂ) := by
  simpa only [smul_eq_mul, fourier_coe_apply, ofReal_one, div_one,
    negativeLaplacePsiCircle_coe] using
    hasSum_negativeLaplacePsi_fourierSeries_circle
      (t : AddCircle (1 : ℝ))

/-- The closed-form coefficient sequence, including the zero mode. -/
noncomputable def negativeLaplacePsiGammaZetaFourierCoeff (k : ℤ) : ℂ :=
  if k = 0 then 0 else
    -Gamma (-negativeLaplaceFourierFrequency k) *
        riemannZeta (1 - negativeLaplaceFourierFrequency k) /
      (Real.log 2 : ℂ)

/-- The closed-form sequence agrees with the abstract coefficients at
every `k`, the zero mode included, where both sides vanish. -/
theorem negativeLaplacePsiGammaZetaFourierCoeff_eq (k : ℤ) :
    negativeLaplacePsiGammaZetaFourierCoeff k =
      negativeLaplacePsiFourierCoeff k := by
  by_cases hk : k = 0
  · subst k
    simp [negativeLaplacePsiGammaZetaFourierCoeff,
      negativeLaplacePsiFourierCoeff_zero]
  · rw [negativeLaplacePsiGammaZetaFourierCoeff, if_neg hk,
      negativeLaplacePsiFourierCoeff_eq_neg_gamma_zeta k hk]

/-- The closed-form `Γζ` coefficient sequence is absolutely summable. -/
theorem summable_negativeLaplacePsiGammaZetaFourierCoeff :
    Summable negativeLaplacePsiGammaZetaFourierCoeff :=
  summable_negativeLaplacePsiFourierCoeff.congr
    (fun k => (negativeLaplacePsiGammaZetaFourierCoeff_eq k).symm)

/-- The explicit `Γζ` Fourier series of the zero-mean periodic correction. -/
theorem hasSum_negativeLaplacePsi_gammaZeta_fourierSeries (t : ℝ) :
    HasSum (fun k : ℤ =>
      negativeLaplacePsiGammaZetaFourierCoeff k *
        exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ)))
      (negativeLaplacePsi t : ℂ) := by
  exact (hasSum_negativeLaplacePsi_fourierSeries t).congr_fun
    (fun k => by rw [negativeLaplacePsiGammaZetaFourierCoeff_eq])

/-- The explicit `Γζ` Fourier series, in `tsum` form. -/
theorem tsum_negativeLaplacePsi_gammaZeta_fourierSeries (t : ℝ) :
    (∑' k : ℤ,
      negativeLaplacePsiGammaZetaFourierCoeff k *
        exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ))) =
      (negativeLaplacePsi t : ℂ) :=
  (hasSum_negativeLaplacePsi_gammaZeta_fourierSeries t).tsum_eq

end Fabius
