import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Poisson summation and the Fourier transform of a complex Gaussian

This module formalizes two statements of the section *Poisson summation and modular inversion*
of the `q`-Pochhammer / `q`-binomial monograph:

* `qg:thm-poisson`, Poisson summation `∑_{n ∈ ℤ} f n = ∑_{k ∈ ℤ} 𝓕 f k` for Schwartz `f`, and
* `qg:lem-gaussian-fourier`, the Gaussian integral

  `∫_ℝ exp (π i τ x ^ 2 + 2 π i u x) dx = (-i τ) ^ (-1/2) * exp (-π i u ^ 2 / τ)`
  for `Im τ > 0` and `u ∈ ℂ`, with the principal square-root branch.

The monograph's Fourier convention `qg:def-fourier-transform`,
`𝓕 f ξ = ∫_ℝ f x * exp (-2 π i x ξ) dx`, is *exactly* Mathlib's `𝓕`
(`Real.fourier_real_eq_integral_exp_smul`): there is no `1 / √(2 π)` normalisation and no sign
flip to repair, so the statements below are the printed ones verbatim.

## What IS covered

* `poisson_summation_schwartz` — `qg:thm-poisson` verbatim.
* `poisson_summation_of_rpow_decay` — the same conclusion under a hypothesis weaker than the
  monograph's: `f` is continuous and both `f` and `𝓕 f` are `O(|x| ^ (-b))` for a single `b > 1`.
  The monograph states only the Schwartz case; this is the honest generality, and it is the form
  the corpus needs downstream, because Mathlib has no Gaussian-to-Schwartz constructor.
* `integral_cexp_pi_I_mul_sq_add` — `qg:lem-gaussian-fourier` verbatim, and
  `integral_cexp_pi_I_mul_sq_add'` the same with the prefactor in Mathlib's normal form
  `1 / (-i τ) ^ (1/2)` rather than the monograph's `(-i τ) ^ (-1/2)`.
* `fourier_cexp_pi_I_mul_sq_add` — the strengthening of `qg:lem-gaussian-fourier` to the **whole**
  Fourier transform, `𝓕 (x ↦ exp (π i τ x ^ 2 + 2 π i u x)) ξ = (-i τ) ^ (-1/2) *
  exp (-π i (u - ξ) ^ 2 / τ)`.  The monograph states only the value at frequency `0`, but its own
  proof of `qg:thm-jacobi-imaginary` then evaluates `𝓕 f` at every integer frequency, recovering
  it by absorbing `-k` into `u`; that absorption is free here.
* `integrable_cexp_pi_I_mul_sq_add` — integrability of the Gaussian integrand.  Not in the source,
  but every integral statement above is vacuous-looking without it.
* `tsum_cexp_pi_I_mul_sq_add` — the raw series form of the Jacobi imaginary transformation
  `∑_{n ∈ ℤ} exp (π i τ n ^ 2 + 2 π i z n) = (-i τ) ^ (-1/2) ∑_{k ∈ ℤ} exp (-π i (z - k) ^ 2 / τ)`,
  which is precisely what the monograph's proof of `qg:thm-jacobi-imaginary` derives before it
  renames the two sides `ϑ₃`.

## What is NOT covered

* **The monograph's proofs are not reproduced.**  The formal statements are the text's; the proofs
  are Mathlib's, and they take different routes.  Mathlib proves Poisson summation through the
  Fourier series of the periodisation on `UnitAddCircle` (the same argument as the text's), and it
  proves the Gaussian transform by a contour shift (Cauchy's theorem) rather than the text's
  ODE-plus-two-identity-theorems route.
* **The theta functions `ϑ₂, ϑ₃, ϑ₄` of `qg:def-jacobi-theta` are not defined here**, and
  `qg:thm-jacobi-imaginary` is not proved in its `ϑ`-notation form; only the raw series identity
  `tsum_cexp_pi_I_mul_sq_add` is.  The three null-value specialisations `eq:qg-theta2-modular`,
  `eq:qg-theta3-null-modular`, `eq:qg-theta4-modular` are out of scope.
* **No `SchwartzMap` structure is built on the Gaussian.**  The source's assertion that the
  Gaussian is Schwartz is correct, but Mathlib supplies no constructor for it, and none is needed
  here: `tsum_cexp_pi_I_mul_sq_add` is obtained from Mathlib's `Complex.tsum_exp_neg_quadratic`,
  which routes around the Schwartz space through the rpow-decay form of Poisson summation.
* **No ring-level generalisation is available.**  Contrary to the usual house preference, both
  statements are irreducibly analytic over `ℝ` and `ℂ` (Lebesgue integral, Schwartz space,
  principal `Complex.cpow`); the only free generality actually available is in the frequency
  variable and in the Poisson hypothesis, and both are taken above.

## Branch convention

Every occurrence of `(-i τ) ^ (·)` is Mathlib's `Complex.cpow`, i.e. `exp (Complex.log _ * ·)`
with the principal logarithm.  For `0 < τ.im` one has `(-i τ).re = τ.im > 0`
(`neg_I_mul_re`), so `-i τ` lies in the open right half-plane, off the principal cut, and
`Complex.cpow` there *is* the principal square root.  On the positive imaginary axis `τ = i t`
with `t > 0` this gives `(-i · i t) ^ (1/2) = t ^ (1/2)`, which is exactly the normalisation the
monograph uses to pin the branch down.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap Real

namespace Fabius

/-! ### Elementary algebra of the substitution `b = -i τ` -/

/-- The single positivity bridge: the real part of `-i τ` is the imaginary part of `τ`.  This is
what turns the monograph's hypothesis `Im τ > 0` into Mathlib's `0 < b.re`. -/
private lemma neg_I_mul_re (τ : ℂ) : (-Complex.I * τ).re = τ.im := by
  rw [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]

/-- A point of the open upper half-plane is nonzero. -/
private lemma im_pos_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : τ ≠ 0 := by
  intro h
  rw [h, Complex.zero_im] at hτ
  exact lt_irrefl 0 hτ

/-- `i * (i * u) = -u`.  Used to turn Mathlib's shifted square `(ξ + i c) ^ 2` at `c = i u` into
the monograph's `(u - ξ) ^ 2`. -/
private lemma I_mul_I_mul (u : ℂ) : Complex.I * (Complex.I * u) = -u := by
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-- `-i τ ≠ 0` whenever `τ ≠ 0`. -/
private lemma neg_I_mul_ne_zero {τ : ℂ} (hτ : τ ≠ 0) : -Complex.I * τ ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ

/-- The exponent appearing in Mathlib's Gaussian Fourier transform, rewritten in the monograph's
shape: `-π / (-i τ) * (w + i (i u)) ^ 2 = -π i (u - w) ^ 2 / τ`. -/
private lemma neg_pi_div_neg_I_mul_sq {τ : ℂ} (hτ : τ ≠ 0) (u w : ℂ) :
    -(π : ℂ) / (-Complex.I * τ) * (w + Complex.I * (Complex.I * u)) ^ 2
      = -(π : ℂ) * Complex.I * (u - w) ^ 2 / τ := by
  have hden : -Complex.I * τ ≠ 0 := neg_I_mul_ne_zero hτ
  have hcoef : -(π : ℂ) / (-Complex.I * τ) = -((π : ℂ) * Complex.I) / τ := by
    rw [div_eq_div_iff hden hτ]
    have hrw : -((π : ℂ) * Complex.I) * (-Complex.I * τ)
        = (π : ℂ) * (Complex.I * Complex.I) * τ := by ring
    rw [hrw, Complex.I_mul_I]
    ring
  rw [I_mul_I_mul, hcoef]
  ring

/-- The monograph's prefactor `(-i τ) ^ (-1/2)` and Mathlib's normal form `1 / (-i τ) ^ (1/2)`
agree; both are the principal branch. -/
private lemma neg_I_mul_cpow_neg_half (τ : ℂ) :
    (-Complex.I * τ) ^ (-(1 / 2) : ℂ) = 1 / (-Complex.I * τ) ^ (1 / 2 : ℂ) := by
  rw [Complex.cpow_neg]
  exact (one_div _).symm

/-! ### Poisson summation (`qg:thm-poisson`) -/

/-- **Poisson summation** for Schwartz functions, `qg:thm-poisson`:
`∑_{n ∈ ℤ} f n = ∑_{k ∈ ℤ} 𝓕 f k`.

The Fourier transform on the right is the honest integral transform of the underlying function
`ℝ → ℂ`, in the monograph's convention `qg:def-fourier-transform`. -/
theorem poisson_summation_schwartz (f : 𝓢(ℝ, ℂ)) :
    ∑' n : ℤ, f (n : ℝ) = ∑' k : ℤ, 𝓕 (f : ℝ → ℂ) (k : ℝ) := by
  simpa only [zero_add, SchwartzMap.fourier_coe, fourier_coe_apply, Complex.ofReal_zero,
    mul_zero, zero_div, Complex.exp_zero, mul_one] using f.tsum_eq_tsum_fourier 0

/-- Poisson summation under a decay hypothesis weaker than the monograph's: `f` is continuous and
both `f` and `𝓕 f` are `O(|x| ^ (-b))` along `cocompact ℝ` for a single `b > 1`.

The monograph states only the Schwartz case (`poisson_summation_schwartz`); this is the version
the corpus actually needs downstream, because Mathlib provides no Gaussian-to-Schwartz
constructor. -/
theorem poisson_summation_of_rpow_decay {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b)))
    (hFf : (𝓕 f) =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-b))) :
    ∑' n : ℤ, f (n : ℝ) = ∑' k : ℤ, 𝓕 f (k : ℝ) := by
  simpa only [zero_add, fourier_coe_apply, Complex.ofReal_zero, mul_zero, zero_div,
    Complex.exp_zero, mul_one] using
    Real.tsum_eq_tsum_fourier_of_rpow_decay hc hb hf hFf 0

/-! ### The Fourier transform of a complex Gaussian (`qg:lem-gaussian-fourier`) -/

/-- The monograph's Gaussian integrand `exp (π i τ x ^ 2 + 2 π i u x)` is integrable on `ℝ`
whenever `Im τ > 0`.  (Not stated in the source, but every integral below needs it.) -/
theorem integrable_cexp_pi_I_mul_sq_add {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) :
    Integrable (fun x : ℝ ↦ Complex.exp ((π : ℂ) * Complex.I * τ * (x : ℂ) ^ 2
      + 2 * (π : ℂ) * Complex.I * u * (x : ℂ))) := by
  have hb : 0 < ((π : ℂ) * (-Complex.I * τ)).re := by
    rw [Complex.re_ofReal_mul, neg_I_mul_re]
    exact mul_pos Real.pi_pos hτ
  have hfun : (fun x : ℝ ↦ Complex.exp (-((π : ℂ) * (-Complex.I * τ)) * (x : ℂ) ^ 2
        + 2 * (π : ℂ) * Complex.I * u * (x : ℂ) + 0))
      = fun x : ℝ ↦ Complex.exp ((π : ℂ) * Complex.I * τ * (x : ℂ) ^ 2
        + 2 * (π : ℂ) * Complex.I * u * (x : ℂ)) := by
    funext x
    exact congrArg Complex.exp (by ring)
  rw [← hfun]
  exact integrable_cexp_quadratic hb (2 * (π : ℂ) * Complex.I * u) 0

/-- **The Fourier transform of a complex Gaussian**, at every frequency.  For `Im τ > 0` and
`u ∈ ℂ`,
`𝓕 (x ↦ exp (π i τ x ^ 2 + 2 π i u x)) ξ = (-i τ) ^ (-1/2) * exp (-π i (u - ξ) ^ 2 / τ)`,
with `(-i τ) ^ (-1/2)` the principal branch.

This is `qg:lem-gaussian-fourier` with the frequency left free; the source states only `ξ = 0`
(see `integral_cexp_pi_I_mul_sq_add`) and recovers the general frequency by absorbing it into
`u`. -/
theorem fourier_cexp_pi_I_mul_sq_add {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) :
    𝓕 (fun x : ℝ ↦ Complex.exp ((π : ℂ) * Complex.I * τ * (x : ℂ) ^ 2
        + 2 * (π : ℂ) * Complex.I * u * (x : ℂ)))
      = fun ξ : ℝ ↦ (-Complex.I * τ) ^ (-(1 / 2) : ℂ) *
          Complex.exp (-(π : ℂ) * Complex.I * (u - (ξ : ℂ)) ^ 2 / τ) := by
  have hτ0 : τ ≠ 0 := im_pos_ne_zero hτ
  have hb : 0 < (-Complex.I * τ).re := by
    rw [neg_I_mul_re]
    exact hτ
  have hfun : (fun x : ℝ ↦ Complex.exp ((π : ℂ) * Complex.I * τ * (x : ℂ) ^ 2
        + 2 * (π : ℂ) * Complex.I * u * (x : ℂ)))
      = fun x : ℝ ↦ Complex.exp (-(π : ℂ) * (-Complex.I * τ) * (x : ℂ) ^ 2
        + 2 * (π : ℂ) * (Complex.I * u) * (x : ℂ)) := by
    funext x
    exact congrArg Complex.exp (by ring)
  -- The pointwise identity is proved separately, so that the two rewrites below act on an
  -- explicitly written goal rather than on whatever `funext` leaves behind.
  have hpt : ∀ ξ : ℝ, 1 / (-Complex.I * τ) ^ (1 / 2 : ℂ) *
        Complex.exp (-(π : ℂ) / (-Complex.I * τ)
          * ((ξ : ℂ) + Complex.I * (Complex.I * u)) ^ 2)
      = (-Complex.I * τ) ^ (-(1 / 2) : ℂ) *
        Complex.exp (-(π : ℂ) * Complex.I * (u - (ξ : ℂ)) ^ 2 / τ) := by
    intro ξ
    rw [neg_I_mul_cpow_neg_half, neg_pi_div_neg_I_mul_sq hτ0 u (ξ : ℂ)]
  rw [hfun, fourier_gaussian_pi' hb (Complex.I * u)]
  exact funext hpt

/-- **Fourier transform of a complex Gaussian**, `qg:lem-gaussian-fourier` verbatim: if
`Im τ > 0` and `u ∈ ℂ`, then, with the principal square-root branch,
`∫_ℝ exp (π i τ x ^ 2 + 2 π i u x) dx = (-i τ) ^ (-1/2) * exp (-π i u ^ 2 / τ)`. -/
theorem integral_cexp_pi_I_mul_sq_add {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) :
    ∫ x : ℝ, Complex.exp ((π : ℂ) * Complex.I * τ * (x : ℂ) ^ 2
        + 2 * (π : ℂ) * Complex.I * u * (x : ℂ))
      = (-Complex.I * τ) ^ (-(1 / 2) : ℂ) *
        Complex.exp (-(π : ℂ) * Complex.I * u ^ 2 / τ) := by
  have hF := congrFun (fourier_cexp_pi_I_mul_sq_add hτ u) 0
  rw [Real.fourier_real_eq_integral_exp_smul] at hF
  simpa only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
    smul_eq_mul, one_mul, sub_zero] using hF

/-- `qg:lem-gaussian-fourier` with the prefactor in Mathlib's normal form `1 / (-i τ) ^ (1/2)`,
so that downstream rewriting never stalls on `one_div`.  Same statement as
`integral_cexp_pi_I_mul_sq_add`. -/
theorem integral_cexp_pi_I_mul_sq_add' {τ : ℂ} (hτ : 0 < τ.im) (u : ℂ) :
    ∫ x : ℝ, Complex.exp ((π : ℂ) * Complex.I * τ * (x : ℂ) ^ 2
        + 2 * (π : ℂ) * Complex.I * u * (x : ℂ))
      = 1 / (-Complex.I * τ) ^ (1 / 2 : ℂ) *
        Complex.exp (-(π : ℂ) * Complex.I * u ^ 2 / τ) := by
  rw [integral_cexp_pi_I_mul_sq_add hτ u, neg_I_mul_cpow_neg_half]

/-! ### The series form of the Jacobi imaginary transformation -/

/-- The two statements joined: applying Poisson summation to the complex Gaussian gives, for
`Im τ > 0` and `z ∈ ℂ`,
`∑_{n ∈ ℤ} exp (π i τ n ^ 2 + 2 π i z n)
  = (-i τ) ^ (-1/2) * ∑_{k ∈ ℤ} exp (-π i (z - k) ^ 2 / τ)`.

This is exactly the series identity that the monograph's proof of `qg:thm-jacobi-imaginary`
produces before it renames the two sides `ϑ₃`; the `ϑ`-notation form itself is not covered by
this module. -/
theorem tsum_cexp_pi_I_mul_sq_add {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    ∑' n : ℤ, Complex.exp ((π : ℂ) * Complex.I * τ * (n : ℂ) ^ 2
        + 2 * (π : ℂ) * Complex.I * z * (n : ℂ))
      = (-Complex.I * τ) ^ (-(1 / 2) : ℂ) *
        ∑' k : ℤ, Complex.exp (-(π : ℂ) * Complex.I * (z - (k : ℂ)) ^ 2 / τ) := by
  have hτ0 : τ ≠ 0 := im_pos_ne_zero hτ
  have hb : 0 < (-Complex.I * τ).re := by
    rw [neg_I_mul_re]
    exact hτ
  have key := Complex.tsum_exp_neg_quadratic hb (Complex.I * z)
  have hleft : ∀ n : ℤ, Complex.exp ((π : ℂ) * Complex.I * τ * (n : ℂ) ^ 2
        + 2 * (π : ℂ) * Complex.I * z * (n : ℂ))
      = Complex.exp (-(π : ℂ) * (-Complex.I * τ) * (n : ℂ) ^ 2
        + 2 * (π : ℂ) * (Complex.I * z) * (n : ℂ)) :=
    fun n ↦ congrArg Complex.exp (by ring)
  have hright : ∀ n : ℤ, Complex.exp (-(π : ℂ) / (-Complex.I * τ)
        * ((n : ℂ) + Complex.I * (Complex.I * z)) ^ 2)
      = Complex.exp (-(π : ℂ) * Complex.I * (z - (n : ℂ)) ^ 2 / τ) :=
    fun n ↦ congrArg Complex.exp (neg_pi_div_neg_I_mul_sq hτ0 z (n : ℂ))
  have hR : (∑' n : ℤ, Complex.exp (-(π : ℂ) / (-Complex.I * τ)
        * ((n : ℂ) + Complex.I * (Complex.I * z)) ^ 2))
      = ∑' k : ℤ, Complex.exp (-(π : ℂ) * Complex.I * (z - (k : ℂ)) ^ 2 / τ) :=
    tsum_congr hright
  calc ∑' n : ℤ, Complex.exp ((π : ℂ) * Complex.I * τ * (n : ℂ) ^ 2
          + 2 * (π : ℂ) * Complex.I * z * (n : ℂ))
      = ∑' n : ℤ, Complex.exp (-(π : ℂ) * (-Complex.I * τ) * (n : ℂ) ^ 2
          + 2 * (π : ℂ) * (Complex.I * z) * (n : ℂ)) := tsum_congr hleft
    _ = 1 / (-Complex.I * τ) ^ (1 / 2 : ℂ) *
          ∑' n : ℤ, Complex.exp (-(π : ℂ) / (-Complex.I * τ)
            * ((n : ℂ) + Complex.I * (Complex.I * z)) ^ 2) := key
    _ = (-Complex.I * τ) ^ (-(1 / 2) : ℂ) *
          ∑' k : ℤ, Complex.exp (-(π : ℂ) * Complex.I * (z - (k : ℂ)) ^ 2 / τ) := by
        rw [neg_I_mul_cpow_neg_half, hR]

end Fabius
