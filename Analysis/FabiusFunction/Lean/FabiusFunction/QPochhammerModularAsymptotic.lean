import FabiusFunction.QBinomialTheoremInfinite
import FabiusFunction.WeierstrassProductBound
import FabiusFunction.QGammaLogDerivative
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The exact modular form of the Euler product `(q;q)_∞` and its `q → 1⁻` asymptotics

For `t > 0` put `q = e^{-t}` and `Q = e^{-4π²/t}`.  The Dedekind eta transformation under
`S : τ ↦ -1/τ`, evaluated on the positive imaginary axis, turns the slowly convergent Euler
product `(q;q)_∞` into one with an exponentially small nome:

`(q;q)_∞ = √(2π/t) · exp(-π²/(6t) + t/24) · (Q;Q)_∞`.

This is `qPochhammerInfIn_exp_neg_modular`, proved here **exactly and for every `t > 0`**, with
no smallness restriction.  The two printed corollaries follow with explicit constants.

## The geometry: the imaginary axis and the `S`-involution

`modularPoint t = i·t/(2π)` is the point `τ` of the source's proof.  On the imaginary axis the
`S`-transformation is exactly the involution `t ↦ 4π²/t`: this is `neg_one_div_modularPoint`,
`-1 / modularPoint t = modularPoint (4π²/t)`, isolated so that it can be reused for the theta
asymptotics elsewhere.

## Main declarations

* `Fabius.modularPoint`, `Fabius.im_modularPoint`,
  `Fabius.modularPoint_mem_upperHalfPlaneSet`, `Fabius.modularPoint_mul_modularPoint`,
  `Fabius.neg_one_div_modularPoint` — the imaginary-axis point and the `S`-involution.
* `Fabius.eta_eq_qPochhammerInfIn` — `η z = 𝕢 24 z · (𝕢 1 z ; 𝕢 1 z)_∞`, for **every** `z : ℂ`.
* `Fabius.eta_modularPoint`, `Fabius.eta_modularPoint_ofReal` — the source's
  `η(it/(2π)) = e^{-t/24} (e^{-t};e^{-t})_∞`.
* `Fabius.csqrt_I_mul_ofReal`, `Fabius.csqrt_I_eq`, `Fabius.csqrt_I_inv_mul_csqrt_I_mul`,
  `Fabius.csqrt_I_inv_mul_csqrt_modularPoint` — the positive square-root branch on the positive
  imaginary axis, `(√i)⁻¹ √(i c) = √c` for `c ≥ 0`.
* `Fabius.eta_modularPoint_neg_inv` — the inversion formula on the imaginary axis.
* `Fabius.qPochhammerInfIn_exp_neg_modular` — **the target**, the exact modular identity.
* `Fabius.qPochhammerInfIn_self_le_one`, `Fabius.one_sub_div_le_qPochhammerInfIn_self`,
  `Fabius.abs_qPochhammerInfIn_self_sub_one_le`, `Fabius.abs_log_qPochhammerInfIn_self_le`,
  `Fabius.abs_log_qPochhammerInfIn_self_le_two_mul`, `Fabius.div_one_sub_le_two_mul` — the
  remainder estimates, stated for an arbitrary real `x ∈ [0,1)` rather than for
  `x = e^{-4π²/t}`.
* `Fabius.exp_neg_four_pi_sq_div_le_quarter` — `e^{-4π²/t} ≤ 1/4` for `0 < t ≤ 2π²`, the
  explicit replacement for the source's unspecified `t₀`.
* `Fabius.abs_qPochhammerInfIn_exp_neg_div_sub_one_le`,
  `Fabius.log_qPochhammerInfIn_exp_neg_modular`,
  `Fabius.abs_log_qPochhammerInfIn_exp_neg_sub_le`,
  `Fabius.isBigO_qPochhammerInfIn_exp_neg_ratio_sub_one`,
  `Fabius.isBigO_log_qPochhammerInfIn_exp_neg_sub` — the two printed asymptotics, both with an
  explicit uniform constant and in their literal `O`-readings.

## What is covered, and in what generality

The printed theorem asserts the exact identity plus two `O(e^{-4π²/t})` statements "uniform for
`0 < t ≤ t₀`, for every fixed `t₀ > 0` small enough".  Everything printed is proved here, and
each consequence is proved in a **stronger** form:

* the ratio bound `|(q;q)_∞ / (√(2π/t) e^{-π²/(6t)+t/24}) - 1| ≤ Q/(1-Q)` holds for **every**
  `t > 0`, with no smallness restriction at all;
* the logarithmic form is an **exact identity**,
  `log (q;q)_∞ = -π²/(6t) + ½ log(2π/t) + t/24 + log (Q;Q)_∞`, valid for every `t > 0`, with the
  error isolated as `log (Q;Q)_∞` and then bounded by `2Q` on the explicit range `0 < t ≤ 2π²`;
* the constant is sharper than the printed one.  The printed argument is correct: it routes
  through `-log(1-u) ≤ u/(1-u)` and `∑_m Q^m/(1-Q^m) ≤ Q/(1-Q)^2 ≤ 4Q`, landing on `4Q`.  The
  Weierstrass product inequality already in the corpus gives `(Q;Q)_∞ ≥ 1 - Q/(1-Q)` in one
  step, whence `|(Q;Q)_∞ - 1| ≤ Q/(1-Q) ≤ 2Q`.  Nothing in the source is being corrected here,
  only the constant improved.

Three generalisations are free and are taken:

* `eta_eq_qPochhammerInfIn` has **no** upper-half-plane hypothesis: both sides are literally the
  same `tprod`, so they agree even where the product diverges and Mathlib's junk value is `1`.
* the remainder estimates are about an arbitrary `x ∈ [0,1)`, not about `e^{-4π²/t}`; they are
  reusable facts about `(x;x)_∞`.
* `neg_one_div_modularPoint` records the `S`-involution `t ↦ 4π²/t` on its own.

## What is NOT covered

1. **The eta `S`-transformation itself is imported, not reproved.**  It enters as Mathlib's
   `ModularForm.eta_comp_eq_csqrt_I_inv`, whose proof goes through `logDeriv η = (πi/12)E₂` and
   the `E₂` transformation.  The monograph instead derives it from the theta–eta product
   `ϑ₂ϑ₃ϑ₄ = 2η³` together with a cube-root-of-unity constancy argument.  The identity is the
   same identity, so the target theorem is fully proved, but the monograph's *route* through
   its theta chapter is a separate, unformalized target.
2. The translation law `η(τ+1) = e^{πi/12} η(τ)` and the theta–eta product are not touched.
3. **Nothing about roots of unity.**  The printed theorem concerns only the real ray
   `q = e^{-t}`, `t → 0⁺`.  No Dedekind-sum / eta-multiplier asymptotic at a general root of
   unity is claimed or proved here.
4. The Fabius function itself does not appear; this is a pure `q`-series/modularity module.

Everything below is over `ℝ` and `ℂ`, which is the natural generality: the statements are about
`Real.exp`, `Real.sqrt` and `Real.log` of a real parameter, and about Mathlib's `ModularForm.eta`,
which is a function of a complex variable.
-/

set_option autoImplicit false

open Filter Topology

open scoped Real

namespace Fabius

/-! ## The imaginary-axis point and the `S`-involution -/

/-- The point `τ = i t / (2π)` on the positive imaginary axis at which the eta transformation is
evaluated.  For `t > 0` this lies in the upper half-plane, and `q = e^{2πiτ} = e^{-t}`. -/
noncomputable def modularPoint (t : ℝ) : ℂ := Complex.I * ((t / (2 * π) : ℝ) : ℂ)

/-- The imaginary part of `modularPoint t` is `t/(2π)`. -/
theorem im_modularPoint (t : ℝ) : (modularPoint t).im = t / (2 * π) := by
  rw [modularPoint, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- For `t > 0` the point `i t/(2π)` lies in the upper half-plane. -/
theorem modularPoint_mem_upperHalfPlaneSet {t : ℝ} (ht : 0 < t) :
    modularPoint t ∈ UpperHalfPlane.upperHalfPlaneSet := by
  show 0 < (modularPoint t).im
  rw [im_modularPoint]
  exact div_pos ht (by linarith [Real.pi_pos])

/-- `modularPoint t` vanishes only at `t = 0`. -/
theorem modularPoint_ne_zero {t : ℝ} (ht : t ≠ 0) : modularPoint t ≠ 0 := by
  have hπ2 : (0 : ℝ) < 2 * π := by linarith [Real.pi_pos]
  intro h
  have him : t / (2 * π) = 0 := by
    rw [← im_modularPoint t, h, Complex.zero_im]
  rcases div_eq_zero_iff.mp him with h1 | h2
  · exact ht h1
  · exact hπ2.ne' h2

/-- **The `S`-involution on the imaginary axis, in product form.**  The two points
`i t/(2π)` and `i (4π²/t)/(2π) = 2πi/t` multiply to `-1`. -/
theorem modularPoint_mul_modularPoint {t : ℝ} (ht : 0 < t) :
    modularPoint (4 * π ^ 2 / t) * modularPoint t = -1 := by
  have hπ2 : (0 : ℝ) < 2 * π := by linarith [Real.pi_pos]
  have hval : 4 * π ^ 2 / t / (2 * π) = 2 * π / t := by
    rw [div_div, div_eq_div_iff (mul_ne_zero ht.ne' hπ2.ne') ht.ne']
    ring
  have hprod : 2 * π / t * (t / (2 * π)) = 1 := by
    rw [div_mul_div_comm, show 2 * π * t = t * (2 * π) from by ring,
      div_self (mul_ne_zero ht.ne' hπ2.ne')]
  have hcast : ((2 * π / t : ℝ) : ℂ) * ((t / (2 * π) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hprod, Complex.ofReal_one]
  simp only [modularPoint, hval]
  linear_combination (Complex.I * Complex.I) * hcast + Complex.I_mul_I

/-- **The `S`-involution on the imaginary axis.**  `-1 / (i t/(2π)) = i (4π²/t)/(2π)`, i.e. on
the positive imaginary axis the modular inversion is exactly the involution `t ↦ 4π²/t`. -/
theorem neg_one_div_modularPoint {t : ℝ} (ht : 0 < t) :
    -1 / modularPoint t = modularPoint (4 * π ^ 2 / t) := by
  rw [div_eq_iff (modularPoint_ne_zero ht.ne')]
  exact (modularPoint_mul_modularPoint ht).symm

/-! ## The nome on the imaginary axis -/

/-- The `q`-parameter of period `h` at a point `i c` of the imaginary axis is the real number
`e^{-2πc/h}`.  No hypothesis on `h` is needed: at `h = 0` both sides are `1` by Lean's
division convention. -/
theorem qParam_I_mul_ofReal (h c : ℝ) :
    Function.Periodic.qParam h (Complex.I * (c : ℂ))
      = ((Real.exp (-(2 * π * c / h)) : ℝ) : ℂ) := by
  simp only [Function.Periodic.qParam, Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (2 * (π : ℂ) * (c : ℂ) / (h : ℂ)) * Complex.I_mul_I

/-- The `q`-parameter of period `h` at `modularPoint t` is `e^{-t/h}`. -/
theorem qParam_modularPoint (h t : ℝ) :
    Function.Periodic.qParam h (modularPoint t) = ((Real.exp (-(t / h)) : ℝ) : ℂ) := by
  have hπ2 : (0 : ℝ) < 2 * π := by linarith [Real.pi_pos]
  have hcancel : 2 * π * (t / (2 * π)) = t := mul_div_cancel₀ t hπ2.ne'
  simp only [modularPoint]
  rw [qParam_I_mul_ofReal, hcancel]

/-! ## Dedekind eta as a `q`-Pochhammer symbol -/

/-- **The eta function is a `q`-Pochhammer symbol**: `η z = 𝕢 24 z · (𝕢 1 z ; 𝕢 1 z)_∞`.

This holds for **every** `z : ℂ`, with no upper-half-plane hypothesis: both infinite products
are the same `tprod`, term by term, so they agree also where the product fails to converge and
Mathlib's junk value `1` is returned. -/
theorem eta_eq_qPochhammerInfIn (z : ℂ) :
    ModularForm.eta z = Function.Periodic.qParam 24 z *
      qPochhammerInfIn (Function.Periodic.qParam 1 z) (Function.Periodic.qParam 1 z) := by
  have hprod : ∏' n : ℕ, (1 - ModularForm.eta_q n z)
      = ∏' j : ℕ, (1 - Function.Periodic.qParam 1 z * Function.Periodic.qParam 1 z ^ j) :=
    tprod_congr fun n => by
      show (1 : ℂ) - Function.Periodic.qParam 1 z ^ (n + 1)
        = 1 - Function.Periodic.qParam 1 z * Function.Periodic.qParam 1 z ^ n
      rw [pow_succ']
  simp only [ModularForm.eta, qPochhammerInfIn_eq_tprod, hprod]

/-- **The eta function at a small imaginary argument.**
`η(i t/(2π)) = e^{-t/24} (e^{-t}; e^{-t})_∞`. -/
theorem eta_modularPoint (t : ℝ) :
    ModularForm.eta (modularPoint t)
      = ((Real.exp (-(t / 24)) : ℝ) : ℂ) *
        qPochhammerInfIn ((Real.exp (-t) : ℝ) : ℂ) ((Real.exp (-t) : ℝ) : ℂ) := by
  rw [eta_eq_qPochhammerInfIn, qParam_modularPoint, qParam_modularPoint, div_one]

/-- The same evaluation, with the right-hand side exhibited as a real number. -/
theorem eta_modularPoint_ofReal {t : ℝ} (ht : 0 < t) :
    ModularForm.eta (modularPoint t)
      = ((Real.exp (-(t / 24)) * qPochhammerInfIn (Real.exp (-t)) (Real.exp (-t)) : ℝ) : ℂ) := by
  have hq : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  rw [eta_modularPoint t, Complex.ofReal_mul, ofReal_qPochhammerInfIn hq]

/-! ## The positive square-root branch on the imaginary axis -/

/-- The principal complex square root of `i c` for real `c ≥ 0`. -/
theorem csqrt_I_mul_ofReal {c : ℝ} (hc : 0 ≤ c) :
    Complex.sqrt (Complex.I * (c : ℂ)) = ((Real.sqrt (c / 2) : ℝ) : ℂ) * (1 + Complex.I) := by
  have hre : (Complex.I * (c : ℂ)).re = 0 := by simp [Complex.mul_re]
  have him : (Complex.I * (c : ℂ)).im = c := by simp [Complex.mul_im]
  have hnorm : ‖Complex.I * (c : ℂ)‖ = c := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [hre, him, hnorm, add_zero, sub_zero]
  split_ifs with h
  · ring
  all_goals exact absurd hc h

/-- The principal square root of `i` itself, obtained from `csqrt_I_mul_ofReal` at `c = 1` so
that the statement does not depend on the exact phrasing of Mathlib's `Complex.sqrt_I`. -/
theorem csqrt_I_eq :
    Complex.sqrt Complex.I = ((Real.sqrt (1 / 2 : ℝ) : ℝ) : ℂ) * (1 + Complex.I) := by
  have h := csqrt_I_mul_ofReal (show (0 : ℝ) ≤ 1 from zero_le_one)
  rwa [Complex.ofReal_one, mul_one] at h

/-- An algebraic cancellation used to normalise the square-root branch. -/
private theorem mul_inv_mul_cancel_aux {A B x : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) :
    (A * B)⁻¹ * (x * A * B) = x := by
  rw [mul_inv]
  calc A⁻¹ * B⁻¹ * (x * A * B) = A⁻¹ * A * (B⁻¹ * B * x) := by ring
    _ = x := by rw [inv_mul_cancel₀ hA, inv_mul_cancel₀ hB, one_mul, one_mul]

/-- **The branch normalisation.**  `(√i)⁻¹ · √(i c) = √c` for every real `c ≥ 0`: the factor
`(√i)⁻¹` in the eta transformation exactly cancels the phase of `√(i c)`, leaving the *positive*
real square root.  This is the content of the source's parenthetical "with its positive square
root on the positive imaginary axis". -/
theorem csqrt_I_inv_mul_csqrt_I_mul {c : ℝ} (hc : 0 ≤ c) :
    (Complex.sqrt Complex.I)⁻¹ * Complex.sqrt (Complex.I * (c : ℂ))
      = ((Real.sqrt c : ℝ) : ℂ) := by
  have h2 : ((Real.sqrt (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hI1 : (1 : ℂ) + Complex.I ≠ 0 := by
    intro h
    have h' : (1 + Complex.I).im = (0 : ℂ).im := by rw [h]
    simp at h'
  have hsplit : Real.sqrt (c / 2) = Real.sqrt c * Real.sqrt (1 / 2 : ℝ) := by
    rw [show c / 2 = c * (1 / 2 : ℝ) from by ring, Real.sqrt_mul hc]
  rw [csqrt_I_eq, csqrt_I_mul_ofReal hc, hsplit, Complex.ofReal_mul]
  exact mul_inv_mul_cancel_aux h2 hI1

/-- The branch normalisation at `modularPoint t`: `(√i)⁻¹ √(i t/(2π)) = √(t/(2π))`. -/
theorem csqrt_I_inv_mul_csqrt_modularPoint {t : ℝ} (ht : 0 ≤ t) :
    (Complex.sqrt Complex.I)⁻¹ * Complex.sqrt (modularPoint t)
      = ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ) := by
  have hc : 0 ≤ t / (2 * π) := div_nonneg ht (by linarith [Real.pi_pos])
  simp only [modularPoint]
  exact csqrt_I_inv_mul_csqrt_I_mul hc

/-! ## The exact modular identity -/

/-- **The eta inversion formula on the positive imaginary axis.**
`η(2πi/t) = √(t/(2π)) · η(i t/(2π))`.

The `S`-transformation itself is Mathlib's `ModularForm.eta_comp_eq_csqrt_I_inv`; what is done
here is the evaluation on the imaginary axis, where the square-root branch becomes the positive
real square root. -/
theorem eta_modularPoint_neg_inv {t : ℝ} (ht : 0 < t) :
    ModularForm.eta (modularPoint (4 * π ^ 2 / t))
      = ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ) * ModularForm.eta (modularPoint t) := by
  have h : ModularForm.eta (-1 / modularPoint t)
      = (Complex.sqrt Complex.I)⁻¹ *
        (Complex.sqrt (modularPoint t) * ModularForm.eta (modularPoint t)) := by
    simpa only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using
      ModularForm.eta_comp_eq_csqrt_I_inv (modularPoint_mem_upperHalfPlaneSet ht)
  rw [neg_one_div_modularPoint ht] at h
  rw [h, ← mul_assoc, csqrt_I_inv_mul_csqrt_modularPoint ht.le]

/-- Solving `X = A (E Y)` for `Y`. -/
private theorem eq_inv_mul_mul_inv_of_eq {A E X Y : ℝ} (hA : A ≠ 0) (hE : E ≠ 0)
    (h : X = A * (E * Y)) : Y = A⁻¹ * X * E⁻¹ := by
  rw [h, show A⁻¹ * (A * (E * Y)) * E⁻¹ = A⁻¹ * A * (E * E⁻¹ * Y) from by ring,
    inv_mul_cancel₀ hA, mul_inv_cancel₀ hE, one_mul, one_mul]

/-- **Exact modular form of the Euler product.**  For every `t > 0`, with `q = e^{-t}` and
`Q = e^{-4π²/t}`,

`(q;q)_∞ = √(2π/t) · exp(-π²/(6t) + t/24) · (Q;Q)_∞`.

This is the printed identity, and it is exact: there is no error term and no restriction on `t`
beyond positivity. -/
theorem qPochhammerInfIn_exp_neg_modular {t : ℝ} (ht : 0 < t) :
    qPochhammerInfIn (Real.exp (-t)) (Real.exp (-t))
      = Real.sqrt (2 * π / t) * Real.exp (-(π ^ 2 / (6 * t)) + t / 24) *
        qPochhammerInfIn (Real.exp (-(4 * π ^ 2 / t))) (Real.exp (-(4 * π ^ 2 / t))) := by
  have hπ2 : (0 : ℝ) < 2 * π := by linarith [Real.pi_pos]
  have hs : 0 < 4 * π ^ 2 / t := div_pos (by positivity) ht
  have hA : 0 < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.mpr (div_pos ht hπ2)
  have hEt : Real.exp (-(t / 24)) ≠ 0 := (Real.exp_pos _).ne'
  -- the complex inversion formula, pushed down to `ℝ`
  have hkey : Real.exp (-(4 * π ^ 2 / t / 24)) *
        qPochhammerInfIn (Real.exp (-(4 * π ^ 2 / t))) (Real.exp (-(4 * π ^ 2 / t)))
      = Real.sqrt (t / (2 * π)) *
        (Real.exp (-(t / 24)) * qPochhammerInfIn (Real.exp (-t)) (Real.exp (-t))) := by
    have h := eta_modularPoint_neg_inv ht
    rw [eta_modularPoint_ofReal hs, eta_modularPoint_ofReal ht, ← Complex.ofReal_mul] at h
    exact_mod_cast h
  -- the two elementary rewritings `(4π²/t)/24 = π²/(6t)` and `√(2π/t) = (√(t/(2π)))⁻¹`
  have ha : 4 * π ^ 2 / t / 24 = π ^ 2 / (6 * t) := by
    rw [div_div, div_eq_div_iff (mul_ne_zero ht.ne' (by norm_num : (24 : ℝ) ≠ 0))
      (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0) ht.ne')]
    ring
  have hb : Real.sqrt (2 * π / t) = (Real.sqrt (t / (2 * π)))⁻¹ := by
    rw [← Real.sqrt_inv, inv_div]
  have hEtinv : (Real.exp (-(t / 24)))⁻¹ = Real.exp (t / 24) := by
    rw [Real.exp_neg, inv_inv]
  have hexp : Real.exp (-(π ^ 2 / (6 * t)) + t / 24)
      = Real.exp (-(4 * π ^ 2 / t / 24)) * (Real.exp (-(t / 24)))⁻¹ := by
    rw [hEtinv, Real.exp_add, ← ha]
  rw [hb, hexp, eq_inv_mul_mul_inv_of_eq hA.ne' hEt hkey]
  ring

/-! ## The remainder, as elementary facts about `(x;x)_∞` -/

/-- `(x;x)_∞ ≤ 1` for `0 ≤ x < 1`. -/
theorem qPochhammerInfIn_self_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    qPochhammerInfIn x x ≤ 1 := by
  have hnorm : ‖x‖ < 1 := by rwa [Real.norm_of_nonneg hx0]
  have h0 : ∀ j : ℕ, 0 ≤ x * x ^ j := fun j => mul_nonneg hx0 (pow_nonneg hx0 j)
  have h1 : ∀ j : ℕ, x * x ^ j ≤ 1 := fun j =>
    mul_le_one₀ hx1.le (pow_nonneg hx0 j) (pow_le_one₀ hx0 hx1.le)
  have hmul : Multipliable fun j : ℕ => 1 - x * x ^ j :=
    multipliable_one_sub_mul_pow_of_norm_lt_one x hnorm
  have h : (∏' j : ℕ, (1 - x * x ^ j)) ≤ 1 :=
    tprod_one_sub_le_one (fun j : ℕ => x * x ^ j) h0 h1 hmul
  rw [qPochhammerInfIn_eq_tprod]
  exact h

/-- **The Weierstrass lower bound** `1 - x/(1-x) ≤ (x;x)_∞` for `0 ≤ x < 1`.  This is the step
that sharpens the source's constant: the printed argument routes through
`-log(1-u) ≤ u/(1-u)` and lands on a constant twice as large. -/
theorem one_sub_div_le_qPochhammerInfIn_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    1 - x / (1 - x) ≤ qPochhammerInfIn x x := by
  have hnorm : ‖x‖ < 1 := by rwa [Real.norm_of_nonneg hx0]
  have h0 : ∀ j : ℕ, 0 ≤ x * x ^ j := fun j => mul_nonneg hx0 (pow_nonneg hx0 j)
  have h1 : ∀ j : ℕ, x * x ^ j ≤ 1 := fun j =>
    mul_le_one₀ hx1.le (pow_nonneg hx0 j) (pow_le_one₀ hx0 hx1.le)
  have hsum : Summable fun j : ℕ => x * x ^ j :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left x
  have hmul : Multipliable fun j : ℕ => 1 - x * x ^ j :=
    multipliable_one_sub_mul_pow_of_norm_lt_one x hnorm
  have hW : 1 - (∑' j : ℕ, x * x ^ j) ≤ ∏' j : ℕ, (1 - x * x ^ j) :=
    one_sub_tsum_le_tprod_one_sub (fun j : ℕ => x * x ^ j) h0 h1 hsum hmul
  have htsum : (∑' j : ℕ, x * x ^ j) = x / (1 - x) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1, div_eq_mul_inv]
  rw [qPochhammerInfIn_eq_tprod]
  linarith [hW, htsum.le, htsum.symm.le]

/-- `|(x;x)_∞ - 1| ≤ x/(1-x)` for `0 ≤ x < 1`. -/
theorem abs_qPochhammerInfIn_self_sub_one_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |qPochhammerInfIn x x - 1| ≤ x / (1 - x) := by
  have hup := qPochhammerInfIn_self_le_one hx0 hx1
  have hlo := one_sub_div_le_qPochhammerInfIn_self hx0 hx1
  have hnn : 0 ≤ x / (1 - x) := div_nonneg hx0 (by linarith)
  rw [abs_le]
  constructor <;> linarith

/-- `|log (x;x)_∞| ≤ x/(1-2x)` for `0 ≤ x < 1/2`. -/
theorem abs_log_qPochhammerInfIn_self_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1 / 2) :
    |Real.log (qPochhammerInfIn x x)| ≤ x / (1 - 2 * x) := by
  have hx1' : x < 1 := by linarith
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have h2x : (0 : ℝ) < 1 - 2 * x := by linarith
  have hP : 0 < qPochhammerInfIn x x := qPochhammerInfIn_pos_of_lt_one hx0 hx1' hx0 hx1'
  have hPle : qPochhammerInfIn x x ≤ 1 := qPochhammerInfIn_self_le_one hx0 hx1'
  have heq : (1 : ℝ) - x / (1 - x) = (1 - 2 * x) / (1 - x) := by
    rw [one_sub_div h1x.ne', show (1 : ℝ) - x - x = 1 - 2 * x from by ring]
  have hlow : (1 - 2 * x) / (1 - x) ≤ qPochhammerInfIn x x := by
    rw [← heq]
    exact one_sub_div_le_qPochhammerInfIn_self hx0 hx1'
  have hinv : (qPochhammerInfIn x x)⁻¹ ≤ (1 - x) / (1 - 2 * x) := by
    have h := inv_anti₀ (div_pos h2x h1x) hlow
    rwa [inv_div] at h
  have hcalc : (1 : ℝ) - (1 - x) / (1 - 2 * x) = -(x / (1 - 2 * x)) := by
    rw [one_sub_div h2x.ne', show (1 : ℝ) - 2 * x - (1 - x) = -x from by ring, neg_div]
  have hlog_lb : -(x / (1 - 2 * x)) ≤ Real.log (qPochhammerInfIn x x) := by
    have hlog := Real.one_sub_inv_le_log_of_pos hP
    have hstep : -(x / (1 - 2 * x)) ≤ 1 - (qPochhammerInfIn x x)⁻¹ := by
      rw [← hcalc]
      linarith
    linarith
  have hlog_ub : Real.log (qPochhammerInfIn x x) ≤ 0 := Real.log_nonpos hP.le hPle
  have hnn : 0 ≤ x / (1 - 2 * x) := div_nonneg hx0 h2x.le
  rw [abs_le]
  constructor <;> linarith

/-- `|log (x;x)_∞| ≤ 2x` for `0 ≤ x ≤ 1/4`. -/
theorem abs_log_qPochhammerInfIn_self_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    |Real.log (qPochhammerInfIn x x)| ≤ 2 * x := by
  have h2x : (0 : ℝ) < 1 - 2 * x := by linarith
  refine (abs_log_qPochhammerInfIn_self_le hx0 (by linarith)).trans ?_
  rw [div_le_iff₀ h2x]
  nlinarith [mul_nonneg hx0 (show (0 : ℝ) ≤ 1 - 4 * x by linarith)]

/-- `x/(1-x) ≤ 2x` for `0 ≤ x ≤ 1/2`. -/
theorem div_one_sub_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    x / (1 - x) ≤ 2 * x := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  rw [div_le_iff₀ h1x]
  nlinarith [mul_nonneg hx0 (show (0 : ℝ) ≤ 1 - 2 * x by linarith)]

/-! ## Smallness of the transformed nome -/

/-- `e² ≥ 4`, with no decimal constants: `e ≥ 2` from `1 + x ≤ e^x`. -/
private theorem four_le_exp_two : (4 : ℝ) ≤ Real.exp 2 := by
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [h]
  nlinarith [he1]

/-- **The transformed nome is small.**  `Q = e^{-4π²/t} ≤ 1/4` as soon as `0 < t ≤ 2π²`.

The source asks for `t ≤ t₀` with `t₀` "small enough"; the proof needs only `Q ≤ 1/2`, and the
explicit range `0 < t ≤ 2π²` already gives `Q ≤ e^{-2} ≤ 1/4`. -/
theorem exp_neg_four_pi_sq_div_le_quarter {t : ℝ} (ht : 0 < t) (ht' : t ≤ 2 * π ^ 2) :
    Real.exp (-(4 * π ^ 2 / t)) ≤ 1 / 4 := by
  have h4 : (2 : ℝ) ≤ 4 * π ^ 2 / t := by
    rw [le_div_iff₀ ht]
    linarith
  have hmono : Real.exp (-(4 * π ^ 2 / t)) ≤ Real.exp (-(2 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hmul : Real.exp (-(2 : ℝ)) * Real.exp 2 = 1 := by
    rw [← Real.exp_add]; norm_num
  have hpos : 0 < Real.exp (-(2 : ℝ)) := Real.exp_pos _
  have hquarter : Real.exp (-(2 : ℝ)) ≤ 1 / 4 := by
    nlinarith [hmul, four_le_exp_two, hpos]
  linarith

/-! ## The two printed asymptotics, with explicit uniform constants -/

/-- **The first printed asymptotic, in explicit two-sided form.**  For **every** `t > 0`,

`|(q;q)_∞ / (√(2π/t) e^{-π²/(6t)+t/24}) - 1| ≤ Q/(1-Q)`,   `Q = e^{-4π²/t}`.

The source states this only as `O(Q)` uniformly on `0 < t ≤ t₀` for `t₀` small enough; here
there is no restriction on `t` at all, and the constant `Q/(1-Q)` is sharper than the printed
`4Q`. -/
theorem abs_qPochhammerInfIn_exp_neg_div_sub_one_le {t : ℝ} (ht : 0 < t) :
    |qPochhammerInfIn (Real.exp (-t)) (Real.exp (-t)) /
        (Real.sqrt (2 * π / t) * Real.exp (-(π ^ 2 / (6 * t)) + t / 24)) - 1|
      ≤ Real.exp (-(4 * π ^ 2 / t)) / (1 - Real.exp (-(4 * π ^ 2 / t))) := by
  have hπ2 : (0 : ℝ) < 2 * π := by linarith [Real.pi_pos]
  have hs : 0 < 4 * π ^ 2 / t := div_pos (by positivity) ht
  have hc : 0 < Real.sqrt (2 * π / t) * Real.exp (-(π ^ 2 / (6 * t)) + t / 24) :=
    mul_pos (Real.sqrt_pos.mpr (div_pos hπ2 ht)) (Real.exp_pos _)
  have hdiv : qPochhammerInfIn (Real.exp (-t)) (Real.exp (-t)) /
      (Real.sqrt (2 * π / t) * Real.exp (-(π ^ 2 / (6 * t)) + t / 24))
      = qPochhammerInfIn (Real.exp (-(4 * π ^ 2 / t))) (Real.exp (-(4 * π ^ 2 / t))) := by
    rw [qPochhammerInfIn_exp_neg_modular ht]
    exact mul_div_cancel_left₀ _ hc.ne'
  rw [hdiv]
  exact abs_qPochhammerInfIn_self_sub_one_le (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs))

/-- **The second printed asymptotic, as an exact identity.**  For every `t > 0`,

`log (q;q)_∞ = -π²/(6t) + ½ log(2π/t) + t/24 + log (Q;Q)_∞`.

The source writes `+ O(e^{-4π²/t})` where the last term stands; isolating it costs nothing and
makes the error term available for a separate estimate. -/
theorem log_qPochhammerInfIn_exp_neg_modular {t : ℝ} (ht : 0 < t) :
    Real.log (qPochhammerInfIn (Real.exp (-t)) (Real.exp (-t)))
      = -(π ^ 2 / (6 * t)) + Real.log (2 * π / t) / 2 + t / 24
        + Real.log (qPochhammerInfIn (Real.exp (-(4 * π ^ 2 / t)))
            (Real.exp (-(4 * π ^ 2 / t)))) := by
  have hπ2 : (0 : ℝ) < 2 * π := by linarith [Real.pi_pos]
  have hs : 0 < 4 * π ^ 2 / t := div_pos (by positivity) ht
  have hQ0 : 0 < Real.exp (-(4 * π ^ 2 / t)) := Real.exp_pos _
  have hQ1 : Real.exp (-(4 * π ^ 2 / t)) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)
  have hR : 0 < qPochhammerInfIn (Real.exp (-(4 * π ^ 2 / t))) (Real.exp (-(4 * π ^ 2 / t))) :=
    qPochhammerInfIn_pos_of_lt_one hQ0.le hQ1 hQ0.le hQ1
  have hsq : 0 < Real.sqrt (2 * π / t) := Real.sqrt_pos.mpr (div_pos hπ2 ht)
  have hE : (0 : ℝ) < Real.exp (-(π ^ 2 / (6 * t)) + t / 24) := Real.exp_pos _
  have hAE : (0 : ℝ) <
      Real.sqrt (2 * π / t) * Real.exp (-(π ^ 2 / (6 * t)) + t / 24) := mul_pos hsq hE
  rw [qPochhammerInfIn_exp_neg_modular ht, Real.log_mul hAE.ne' hR.ne',
    Real.log_mul hsq.ne' hE.ne', Real.log_sqrt (div_pos hπ2 ht).le, Real.log_exp]
  ring

/-- **The second printed asymptotic, with an explicit uniform constant.**  On `0 < t ≤ 2π²`,

`|log (q;q)_∞ - (-π²/(6t) + ½ log(2π/t) + t/24)| ≤ 2 e^{-4π²/t}`.

The source's constant is `4Q` and its range is `0 < t ≤ t₀` for an unspecified small `t₀`. -/
theorem abs_log_qPochhammerInfIn_exp_neg_sub_le {t : ℝ} (ht : 0 < t) (ht' : t ≤ 2 * π ^ 2) :
    |Real.log (qPochhammerInfIn (Real.exp (-t)) (Real.exp (-t)))
        - (-(π ^ 2 / (6 * t)) + Real.log (2 * π / t) / 2 + t / 24)|
      ≤ 2 * Real.exp (-(4 * π ^ 2 / t)) := by
  have hsub : ∀ a b : ℝ, a + b - a = b := fun a b => by ring
  rw [log_qPochhammerInfIn_exp_neg_modular ht, hsub]
  exact abs_log_qPochhammerInfIn_self_le_two_mul (Real.exp_pos _).le
    (exp_neg_four_pi_sq_div_le_quarter ht ht')

/-! ## The literal `O`-readings -/

/-- The two facts about `𝓝[>] 0` used by the `O`-statements. -/
private theorem eventually_pos_and_lt_two_pi_sq :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 2 * π ^ 2 := by
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t :=
    eventually_nhdsWithin_of_forall fun _ hx => hx
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 2 * π ^ 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_lt_nhds (by positivity))
  filter_upwards [hpos, hsmall] with t ht ht2 using ⟨ht, ht2⟩

/-- **`eq:qg-qpochhammer-modular-asymptotic`, in its literal `O`-reading.**

`(q;q)_∞ = √(2π/t) e^{-π²/(6t)+t/24} (1 + O(e^{-4π²/t}))` as `t → 0⁺`.

This is a corollary of `abs_qPochhammerInfIn_exp_neg_div_sub_one_le`, which is stronger: it
holds for every `t > 0` and carries the explicit constant `Q/(1-Q)`. -/
theorem isBigO_qPochhammerInfIn_exp_neg_ratio_sub_one :
    (fun t : ℝ => qPochhammerInfIn (Real.exp (-t)) (Real.exp (-t)) /
        (Real.sqrt (2 * π / t) * Real.exp (-(π ^ 2 / (6 * t)) + t / 24)) - 1)
      =O[𝓝[>] (0 : ℝ)] fun t : ℝ => Real.exp (-(4 * π ^ 2 / t)) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_pos_and_lt_two_pi_sq] with t ht
  have hQpos : 0 < Real.exp (-(4 * π ^ 2 / t)) := Real.exp_pos _
  have hQ : Real.exp (-(4 * π ^ 2 / t)) ≤ 1 / 4 :=
    exp_neg_four_pi_sq_div_le_quarter ht.1 ht.2.le
  simp only [Real.norm_eq_abs, abs_of_pos hQpos]
  refine (abs_qPochhammerInfIn_exp_neg_div_sub_one_le ht.1).trans ?_
  exact div_one_sub_le_two_mul hQpos.le (by linarith)

/-- **`eq:qg-qpochhammer-log-asymptotic`, in its literal `O`-reading.**

`log (q;q)_∞ = -π²/(6t) + ½ log(2π/t) + t/24 + O(e^{-4π²/t})` as `t → 0⁺`.

This is a corollary of `abs_log_qPochhammerInfIn_exp_neg_sub_le`, which is stronger: it carries
the explicit constant `2` on the explicit range `0 < t ≤ 2π²`. -/
theorem isBigO_log_qPochhammerInfIn_exp_neg_sub :
    (fun t : ℝ => Real.log (qPochhammerInfIn (Real.exp (-t)) (Real.exp (-t)))
        - (-(π ^ 2 / (6 * t)) + Real.log (2 * π / t) / 2 + t / 24))
      =O[𝓝[>] (0 : ℝ)] fun t : ℝ => Real.exp (-(4 * π ^ 2 / t)) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_pos_and_lt_two_pi_sq] with t ht
  have hQpos : 0 < Real.exp (-(4 * π ^ 2 / t)) := Real.exp_pos _
  simp only [Real.norm_eq_abs, abs_of_pos hQpos]
  exact abs_log_qPochhammerInfIn_exp_neg_sub_le ht.1 ht.2.le

end Fabius
