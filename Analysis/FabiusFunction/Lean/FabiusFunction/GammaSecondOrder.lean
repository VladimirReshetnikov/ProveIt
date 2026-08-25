import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Second-order expansion of `Γ(1 + z)` at the origin

This module computes the quadratic Taylor coefficient of the Gamma function at
the point `1` and packages the expansion

`Γ(1 + z) = 1 - γ z + (γ² / 2 + π² / 12) z² + O(z³)`,

where `γ` is the Euler--Mascheroni constant.  Mathlib already supplies
`Γ'(1) = -γ`; the new ingredient is `Γ''(1) = γ² + π² / 6`, extracted from the
reflection formula in the cross-multiplied form
`Γ(1 + z) Γ(1 - z) sin(π z) = π z`, which extends across the puncture at the
origin, so that differentiating it three times at `0` leaves a linear equation
for `Γ''(1)` in which every other term is already known.

The module is the Gamma-side half of the regularization of the Gamma--zeta
product at `s = 0`; the zeta-side half is
`mul_riemannZeta_one_add_taylor_second` of `FabiusFunction.StieltjesConstant`.
`FabiusFunction.MellinFinitePart` multiplies the two expansions to cancel the
double pole of `Γ(s) ζ(1 + s)` and to identify the finite part with the
Euler--Stieltjes constant `gammaZetaConstant`, from which the mean of the
periodic correction and the sharp Fabius asymptotic constant are built.
Nothing here mentions the Fabius function; the file imports only Mathlib, and
`FabiusFunction.MellinBose` merely forwards it along the import chain.

## Main results

* `iteratedDeriv_two_complexGamma_one` — `Γ''(1) = γ² + π² / 6`.
* `exists_complexGamma_one_add_taylor_remainder` — the expansion with an
  explicit remainder `z ^ 3 * R z`, with `R` analytic at the origin.
* `complexGamma_one_add_taylor_second` — the same expansion as a little-o
  statement at `nhds 0`, which is the form downstream files consume.

Statements are complex throughout (`Complex.Gamma`) and are phrased for the
shifted function `z ↦ Γ(1 + z)`, so the expansion point is `0`.  The remainder
identity is asserted for every `z : ℂ`, but `R` is only claimed analytic at the
origin, so its content is local: away from a neighbourhood of `0` the equation
merely defines `R`.
-/

set_option autoImplicit false

open Filter Set
open Asymptotics
open scoped Topology

namespace Fabius

private theorem analyticAt_complexGamma_one : AnalyticAt ℂ Complex.Gamma 1 := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hU : {z : ℂ | 0 < z.re} ∈ nhds (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
  filter_upwards [hU] with z hz
  exact Complex.differentiableAt_Gamma z (fun m hm ↦ by
    have hre := congrArg Complex.re hm
    simp at hre
    linarith)

private theorem gamma_reflection_cross_eventually :
    Filter.EventuallyEq (nhds 0)
      (fun z : ℂ ↦ Complex.Gamma (1 + z) * Complex.Gamma (1 - z) *
        Complex.sin (Real.pi * z))
      (fun z : ℂ ↦ Real.pi * z) := by
  have hsin : HasDerivAt (fun z : ℂ ↦ Complex.sin ((Real.pi : ℂ) * z))
      (Real.pi : ℂ) 0 := by
    have hlin : HasDerivAt (fun z : ℂ ↦ (Real.pi : ℂ) * z) Real.pi 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)
    have hout : HasDerivAt Complex.sin 1 ((Real.pi : ℂ) * 0) := by
      simpa using Complex.hasDerivAt_sin 0
    have hc := hout.comp (0 : ℂ) hlin
    convert! hc using 1
    simp
  have hne : {z : ℂ | Complex.sin (Real.pi * z) ≠ 0} ∈
      nhdsWithin (0 : ℂ) ({0} : Set ℂ)ᶜ :=
    hsin.eventually_ne (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpunct : {z : ℂ |
      Complex.Gamma (1 + z) * Complex.Gamma (1 - z) *
        Complex.sin (Real.pi * z) = Real.pi * z} ∈
      nhdsWithin (0 : ℂ) ({0} : Set ℂ)ᶜ := by
    filter_upwards [hne, self_mem_nhdsWithin] with z hz hzmem
    have hz0 : z ≠ 0 := by simpa using hzmem
    rw [add_comm, Complex.Gamma_add_one z hz0]
    have hz' : Complex.sin (z * Real.pi) ≠ 0 := by simpa [mul_comm] using hz
    calc
      _ = z * (Complex.Gamma z * Complex.Gamma (1 - z)) *
            Complex.sin (Real.pi * z) := by ring
      _ = z * ((Real.pi : ℂ) / Complex.sin (Real.pi * z)) *
            Complex.sin (Real.pi * z) := by rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = Real.pi * z := by field_simp [hz']
  rw [eventuallyEq_iff_exists_mem]
  refine ⟨insert (0 : ℂ) {z : ℂ |
      Complex.Gamma (1 + z) * Complex.Gamma (1 - z) *
        Complex.sin (Real.pi * z) = Real.pi * z},
    insert_mem_nhds_iff.mpr hpunct, ?_⟩
  intro z hz
  rcases hz with rfl | hz
  · simp
  · exact hz

/-- The second complex derivative of the Gamma function at `1`. -/
theorem iteratedDeriv_two_complexGamma_one :
    iteratedDeriv 2 Complex.Gamma 1 =
      (Real.eulerMascheroniConstant : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2 / 6 := by
  let gp : ℂ → ℂ := fun z ↦ Complex.Gamma (1 + z)
  let gm : ℂ → ℂ := fun z ↦ Complex.Gamma (1 - z)
  let sn : ℂ → ℂ := fun z ↦ Complex.sin (Real.pi * z)
  let q : ℂ → ℂ := gp * gm
  have hgp : ContDiffAt ℂ 3 gp 0 := by
    have hadd : ContDiffAt ℂ 3 (fun z : ℂ ↦ 1 + z) 0 := by fun_prop
    have hGamma : ContDiffAt ℂ 3 Complex.Gamma ((1 : ℂ) + 0) := by
      simpa using (analyticAt_complexGamma_one.contDiffAt :
        ContDiffAt ℂ 3 Complex.Gamma 1)
    simpa only [gp, Function.comp_def] using
      (ContDiffAt.comp (𝕜 := ℂ) (E := ℂ) (F := ℂ) (G := ℂ) (n := 3)
        (f := fun z : ℂ ↦ 1 + z) (g := Complex.Gamma) 0
        hGamma hadd)
  have hgm : ContDiffAt ℂ 3 gm 0 := by
    have hsub : ContDiffAt ℂ 3 (fun z : ℂ ↦ 1 - z) 0 := by fun_prop
    have hGamma : ContDiffAt ℂ 3 Complex.Gamma ((1 : ℂ) - 0) := by
      simpa using (analyticAt_complexGamma_one.contDiffAt :
        ContDiffAt ℂ 3 Complex.Gamma 1)
    simpa only [gm, Function.comp_def] using
      (ContDiffAt.comp (𝕜 := ℂ) (E := ℂ) (F := ℂ) (G := ℂ) (n := 3)
        (f := fun z : ℂ ↦ 1 - z) (g := Complex.Gamma) 0
        hGamma hsub)
  have hsn : ContDiffAt ℂ 3 sn 0 := by
    fun_prop
  have hq : ContDiffAt ℂ 3 q 0 := hgp.mul hgm
  have hq2 : iteratedDeriv 2 q 0 =
      2 * iteratedDeriv 2 Complex.Gamma 1 -
        2 * (Real.eulerMascheroniConstant : ℂ) ^ 2 := by
    rw [iteratedDeriv_mul (hgp.of_le (by norm_num)) (hgm.of_le (by norm_num))]
    simp only [Finset.sum_range_succ]
    simp [gp, gm, iteratedDeriv_comp_const_add,
      iteratedDeriv_comp_const_sub, Complex.Gamma_one,
      Complex.hasDerivAt_Gamma_one.deriv]
    ring
  have href := gamma_reflection_cross_eventually.iteratedDeriv_eq 3
  change iteratedDeriv 3 (q * sn) 0 =
    iteratedDeriv 3 (fun z : ℂ ↦ Real.pi * z) 0 at href
  rw [iteratedDeriv_mul hq hsn] at href
  simp only [Finset.sum_range_succ] at href
  simp [q, gp, gm, sn, iteratedDeriv_comp_const_mul,
    Complex.contDiff_sin, Complex.Gamma_one] at href
  rw [hq2] at href
  have hrhs : iteratedDeriv 3 (fun z : ℂ ↦ Real.pi * z) 0 = 0 := by
    simp [iteratedDeriv_succ]
  rw [hrhs] at href
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_left_cancel₀ hpi
  linear_combination href / 6

/-- Exact second-order Taylor factorization of `Γ(1 + z)` at the origin.

The remainder is a cubic power times a function analytic at the origin. -/
theorem exists_complexGamma_one_add_taylor_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ z : ℂ,
      Complex.Gamma (1 + z) =
        1 - (Real.eulerMascheroniConstant : ℂ) * z +
          ((Real.eulerMascheroniConstant : ℂ) ^ 2 / 2 +
            (Real.pi : ℂ) ^ 2 / 12) * z ^ 2 + z ^ 3 * R z := by
  have hadd : AnalyticAt ℂ (fun z : ℂ ↦ 1 + z) 0 := by fun_prop
  have hGamma : AnalyticAt ℂ Complex.Gamma ((1 : ℂ) + 0) := by
    simpa using analyticAt_complexGamma_one
  have hf : AnalyticAt ℂ (fun z : ℂ ↦ Complex.Gamma (1 + z)) 0 := by
    simpa only [Function.comp_def] using hGamma.comp hadd
  obtain ⟨R, hRa, hR⟩ := hf.exists_eq_sum_add_pow_mul 3
  refine ⟨R, hRa, fun z ↦ ?_⟩
  specialize hR z
  simp only [Finset.sum_range_succ] at hR
  simp [iteratedDeriv_comp_const_add, Complex.Gamma_one,
    Complex.hasDerivAt_Gamma_one.deriv,
    iteratedDeriv_two_complexGamma_one] at hR
  rw [hR]
  ring

/-- Second-order Taylor expansion of `Γ(1 + z)` in complex little-o form. -/
theorem complexGamma_one_add_taylor_second :
    (fun z : ℂ ↦ Complex.Gamma (1 + z) -
      (1 - (Real.eulerMascheroniConstant : ℂ) * z +
        ((Real.eulerMascheroniConstant : ℂ) ^ 2 / 2 +
          (Real.pi : ℂ) ^ 2 / 12) * z ^ 2)) =o[nhds 0]
      (fun z : ℂ ↦ z ^ 2) := by
  obtain ⟨R, hRa, hR⟩ := exists_complexGamma_one_add_taylor_remainder
  have hpow : (fun z : ℂ ↦ z ^ 3) =o[nhds 0] (fun z : ℂ ↦ z ^ 2) :=
    isLittleO_pow_pow (by norm_num)
  have hRbig : R =O[nhds 0] (fun _ : ℂ ↦ (1 : ℂ)) :=
    isBigO_const_of_tendsto hRa.continuousAt one_ne_zero
  have hrem := hpow.mul_isBigO hRbig
  refine hrem.congr' ?_ (Filter.Eventually.of_forall fun z ↦ by simp)
  exact Filter.Eventually.of_forall fun z ↦ by
    dsimp
    rw [hR z]
    ring

end Fabius
