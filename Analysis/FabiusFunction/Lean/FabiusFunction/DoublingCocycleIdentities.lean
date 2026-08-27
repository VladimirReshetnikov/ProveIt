import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The doubling cocycle `ψ = log (2 sin π·)` and its martingale difference

Documents 6 and 8 of the second-wave Fourier-decay corpus reduce the
whole fluctuation theory of the dyadic sine product to two elementary
identities for the cocycle `ψ(t) = log (2 sin (π t))` under the
doubling map, audited in the second-wave comparative audit:

* the **Perron halving law** `𝒫ψ = ψ/2`, whose multiplicative form
  `(2 sin (πx/2))·(2 sin (π(x+1)/2)) = 2 sin (πx)` is an exact,
  unconditional double-angle identity (no absolute values, no
  exceptional set); and
* the **martingale difference** `d = 2ψ - ψ∘T = log |tan (π·)|`,
  which satisfies `𝒫d = 0` — the two doubling preimages of any point
  carry opposite log-tangent values, because
  `tan (θ + π/2) = -1/tan θ`.

Together they give the one-line Gordin decomposition
`S_n = Σ_{j<n} d∘Tʲ - ψ + ψ∘Tⁿ` behind the exact per-level variance
`π²/4` and the corrected law of the iterated logarithm (constant
`π/√2`, not the published `π`).  This file proves the pointwise layer;
`Real.log` takes absolute values silently (`Real.log_abs`), so the
statements need nonvanishing hypotheses only where a genuine zero of
the sine or cosine would make a term degenerate.

* `two_sin_half_mul_two_sin_succ_half` — the unconditional
  multiplicative halving identity, over `ℝ` and over `ℂ`.
* `log_two_sin_half_add` — `ψ(x/2) + ψ((x+1)/2) = ψ(x)` wherever
  `sin (πx) ≠ 0`; this is `𝒫ψ = ψ/2`.
* `two_log_two_sin_sub` — `2ψ(t) - ψ(2t) = log |tan (πt)|` wherever
  `sin (2πt) ≠ 0`: the martingale difference is the log-tangent.
* `log_abs_tan_half_add` — `d(x/2) + d((x+1)/2) = 0`: the martingale
  difference has zero Perron mean.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-- The multiplicative Perron halving identity, complex form:
`(2 sin (πz/2))·(2 sin (π(z+1)/2)) = 2 sin (πz)`, unconditionally. -/
theorem two_sin_half_mul_two_sin_succ_half_complex (z : ℂ) :
    (2 * Complex.sin (π * z / 2)) * (2 * Complex.sin (π * (z + 1) / 2)) =
      2 * Complex.sin (π * z) := by
  have h1 : (π : ℂ) * (z + 1) / 2 = π * z / 2 + π / 2 := by
    ring
  rw [h1, Complex.sin_add_pi_div_two]
  have h2 : Complex.sin (π * z) =
      2 * Complex.sin (π * z / 2) * Complex.cos (π * z / 2) := by
    rw [← Complex.sin_two_mul]
    ring_nf
  rw [h2]
  ring

/-- The multiplicative Perron halving identity:
`(2 sin (πx/2))·(2 sin (π(x+1)/2)) = 2 sin (πx)`, exactly and
unconditionally — the double-angle formula in disguise, since
`sin (π(x+1)/2) = cos (πx/2)`. -/
theorem two_sin_half_mul_two_sin_succ_half (x : ℝ) :
    (2 * Real.sin (π * x / 2)) * (2 * Real.sin (π * (x + 1) / 2)) =
      2 * Real.sin (π * x) := by
  have h1 : π * (x + 1) / 2 = π * x / 2 + π / 2 := by ring
  rw [h1, Real.sin_add_pi_div_two]
  have h2 : Real.sin (π * x) =
      2 * Real.sin (π * x / 2) * Real.cos (π * x / 2) := by
    rw [← Real.sin_two_mul]
    ring_nf
  rw [h2]
  ring

/-- **The Perron halving law `𝒫ψ = ψ/2`** for the doubling cocycle
`ψ(t) = log (2 sin (πt))`: summing `ψ` over the two doubling preimages
of `x` returns `ψ(x)`, wherever `sin (πx) ≠ 0`. -/
theorem log_two_sin_half_add (x : ℝ) (hx : Real.sin (π * x) ≠ 0) :
    Real.log (2 * Real.sin (π * x / 2)) +
      Real.log (2 * Real.sin (π * (x + 1) / 2)) =
      Real.log (2 * Real.sin (π * x)) := by
  have hprod := two_sin_half_mul_two_sin_succ_half x
  have h2 : (2:ℝ) * Real.sin (π * x) ≠ 0 := mul_ne_zero two_ne_zero hx
  have ha : (2:ℝ) * Real.sin (π * x / 2) ≠ 0 := by
    intro h0
    apply h2
    rw [← hprod, h0, zero_mul]
  have hb : (2:ℝ) * Real.sin (π * (x + 1) / 2) ≠ 0 := by
    intro h0
    apply h2
    rw [← hprod, h0, mul_zero]
  rw [← Real.log_mul ha hb, hprod]

/-- **The martingale difference is the log-tangent**:
`2 log (2 sin (πt)) - log (2 sin (2πt)) = log |tan (πt)|` wherever
`sin (2πt) ≠ 0`.  This is `d = 2ψ - ψ∘T` of the Gordin decomposition. -/
theorem two_log_two_sin_sub (t : ℝ) (ht : Real.sin (π * (2 * t)) ≠ 0) :
    2 * Real.log (2 * Real.sin (π * t)) -
      Real.log (2 * Real.sin (π * (2 * t))) =
      Real.log |Real.tan (π * t)| := by
  have hst : Real.sin (π * (2 * t)) =
      2 * Real.sin (π * t) * Real.cos (π * t) := by
    rw [show π * (2 * t) = 2 * (π * t) by ring, Real.sin_two_mul]
  have hs : Real.sin (π * t) ≠ 0 := by
    intro h0
    apply ht
    rw [hst, h0]
    ring
  have hc : Real.cos (π * t) ≠ 0 := by
    intro h0
    apply ht
    rw [hst, h0]
    ring
  rw [hst,
    show (2:ℝ) * (2 * Real.sin (π * t) * Real.cos (π * t)) =
      (2 * Real.sin (π * t)) * (2 * Real.cos (π * t)) by ring,
    Real.log_mul (mul_ne_zero two_ne_zero hs) (mul_ne_zero two_ne_zero hc),
    Real.log_abs, Real.tan_eq_sin_div_cos, Real.log_div hs hc,
    Real.log_mul two_ne_zero hs, Real.log_mul two_ne_zero hc]
  ring

/-- **Zero Perron mean of the martingale difference, `𝒫d = 0`**: the
two doubling preimages of any point carry opposite log-tangent values,
`log |tan (πx/2)| + log |tan (π(x+1)/2)| = 0`, because
`tan (θ + π/2) = -1/tan θ`. -/
theorem log_abs_tan_half_add (x : ℝ) (hs : Real.sin (π * x / 2) ≠ 0)
    (hc : Real.cos (π * x / 2) ≠ 0) :
    Real.log |Real.tan (π * x / 2)| +
      Real.log |Real.tan (π * (x + 1) / 2)| = 0 := by
  have h1 : π * (x + 1) / 2 = π * x / 2 + π / 2 := by ring
  have hsin1 : Real.sin (π * (x + 1) / 2) = Real.cos (π * x / 2) := by
    rw [h1, Real.sin_add_pi_div_two]
  have hcos1 : Real.cos (π * (x + 1) / 2) = -Real.sin (π * x / 2) := by
    rw [h1, Real.cos_add_pi_div_two]
  rw [Real.log_abs, Real.log_abs, Real.tan_eq_sin_div_cos,
    Real.tan_eq_sin_div_cos, hsin1, hcos1, Real.log_div hs hc,
    Real.log_div hc (neg_ne_zero.mpr hs), Real.log_neg_eq_log]
  ring

end Fabius
