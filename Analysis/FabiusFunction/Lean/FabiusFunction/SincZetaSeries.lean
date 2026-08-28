import FabiusFunction.SincEulerProduct
import FabiusFunction.EulerLogTransform
import FabiusFunction.EvenZetaSeries

/-!
# The Euler–zeta expansion of the complex sinc

The frontier drafts' `lem:logsinc` (Fabius/Rvachev–Thue–Morse frontier
results, `eq:logsinc`): on the disk `|z| < π`,

`log sinc z = -∑_{r ≥ 1} ζ(2r)/(r π^{2r}) · z^{2r}`,

with the branch vanishing at `z = 0`.  The branch-free content is the
exponential form proved here:

`sinc (πx) = exp (-∑_{r ≥ 1} ζ(2r) x^{2r} / r)` for `‖x‖ < 1`,

obtained by feeding the Euler product of the sinc
(`tprod_one_add_sineTerm`) through the Euler log transform
(`EulerLogTransform`); the power sums of the family `x²/(n+1)²`
collapse to `ζ(2r)·x^{2r}` (`EvenZetaSeries`).  For real `x` the
series is real, the sinc value is the positive real `exp` of it, and
taking `Real.log` recovers `eq:logsinc` literally.

* `complexSinc_pi_mul_eq_cexp` — the exponential form at `πx`, `‖x‖ < 1`.
* `complexSinc_eq_cexp` — the same at `z`, `‖z‖ < π` (the draft's
  normalization).
* `complexSinc_pi_mul_ofReal` — real arguments: the value is the
  coercion of a positive real exponential.
* `log_sin_div_pi_mul` — `eq:logsinc` for real `0 < |x| < 1`:
  `log (sin (πx)/(πx)) = -∑_{r ≥ 1} ζ(2r) x^{2r} / r`.
-/

set_option autoImplicit false

open Complex Real

namespace Fabius

/-- The Euler factors of the sinc at `πx` are `1 - x²/(n+1)²`:
`1 + sineTerm x n` in Mathlib's normalization. -/
theorem one_add_sineTerm_eq (x : ℂ) (n : ℕ) :
    1 + sineTerm x n = 1 - x ^ 2 / ((n : ℂ) + 1) ^ 2 := by
  rw [sineTerm, sub_eq_add_neg, neg_div]

/-- Norms of the sinc Euler family `x²/(n+1)²` stay below `1` for
`‖x‖ < 1`. -/
theorem sinc_family_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) (n : ℕ) :
    ‖x ^ 2 / ((n : ℂ) + 1) ^ 2‖ < 1 := by
  have hn : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.succ_ne_zero
  rw [norm_div, norm_pow, norm_pow]
  calc ‖x‖ ^ 2 / ‖(n : ℂ) + 1‖ ^ 2 ≤ ‖x‖ ^ 2 :=
        div_le_self (by positivity) (one_le_pow₀ hn)
    _ < 1 := pow_lt_one₀ (norm_nonneg x) hx two_ne_zero

/-- The sinc Euler family is norm-summable. -/
theorem sinc_family_norm_summable (x : ℂ) :
    Summable fun n : ℕ => ‖x ^ 2 / ((n : ℂ) + 1) ^ 2‖ := by
  have h := (summable_one_div_add_one_pow one_ne_zero).mul_left (‖x‖ ^ 2)
  refine h.congr fun n => ?_
  rw [norm_div, norm_pow, norm_pow,
    show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
    Complex.norm_natCast]
  push_cast
  rw [mul_one_div]
  norm_num

/-- The power sums of the sinc Euler family are even zeta values:
`∑' n, (x²/(n+1)²)^(r+1) = ζ(2(r+1)) · x^(2(r+1))`. -/
theorem sinc_family_powerSum (x : ℂ) (r : ℕ) :
    ∑' n : ℕ, (x ^ 2 / ((n : ℂ) + 1) ^ 2) ^ (r + 1) =
      (evenZeta (r + 1) : ℂ) * x ^ (2 * (r + 1)) := by
  have hterm : ∀ n : ℕ, (x ^ 2 / ((n : ℂ) + 1) ^ 2) ^ (r + 1) =
      x ^ (2 * (r + 1)) * (1 / ((n : ℂ) + 1) ^ (2 * (r + 1))) := by
    intro n
    rw [div_pow, ← pow_mul, ← pow_mul, div_eq_mul_one_div]
  rw [tsum_congr hterm, tsum_mul_left, ← ofReal_evenZeta, mul_comm]

/-- **The Euler–zeta expansion of the sinc, exponential form**
(`lem:logsinc`, branch-free): for `‖x‖ < 1`,

`sinc (πx) = exp (-∑'_{r} ζ(2(r+1)) · x^(2(r+1)) / (r+1))`.

The sum over `r : ℕ` realizes `∑_{r ≥ 1} ζ(2r) x^{2r} / r`. -/
theorem complexSinc_pi_mul_eq_cexp {x : ℂ} (hx : ‖x‖ < 1) :
    complexSinc (π * x) =
      Complex.exp (-∑' r : ℕ,
        (evenZeta (r + 1) : ℂ) * x ^ (2 * (r + 1)) / ((r : ℂ) + 1)) := by
  rw [← tprod_one_add_sineTerm x,
    tprod_congr (one_add_sineTerm_eq x),
    tprod_one_sub_eq_cexp_powerSum (sinc_family_norm_lt_one hx)
      (sinc_family_norm_summable x)]
  congr 2
  exact tsum_congr fun r => by rw [sinc_family_powerSum]

/-- **The Euler–zeta expansion on the disk `‖z‖ < π`** — the draft's
normalization `sinc z = exp (-∑_{r ≥ 1} ζ(2r)/(r π^{2r}) · z^{2r})`,
written with the scaled variable `(z/π)^{2r}`. -/
theorem complexSinc_eq_cexp {z : ℂ} (hz : ‖z‖ < π) :
    complexSinc z =
      Complex.exp (-∑' r : ℕ,
        (evenZeta (r + 1) : ℂ) * (z / π) ^ (2 * (r + 1)) / ((r : ℂ) + 1)) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have hx : ‖z / (π : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
    exact (div_lt_one pi_pos).mpr hz
  have h := complexSinc_pi_mul_eq_cexp hx
  rwa [mul_comm (π : ℂ) (z / π), div_mul_cancel₀ z hπ] at h

/-- For real `x` with `|x| < 1`, the sinc value at `πx` is the coercion
of a **positive real** exponential: the whole Euler–zeta series is
real. -/
theorem complexSinc_pi_mul_ofReal {x : ℝ} (hx : |x| < 1) :
    complexSinc ((π : ℂ) * (x : ℂ)) =
      ((Real.exp (-∑' r : ℕ,
        evenZeta (r + 1) * x ^ (2 * (r + 1)) / ((r : ℝ) + 1)) : ℝ) : ℂ) := by
  have h := complexSinc_pi_mul_eq_cexp (x := (x : ℂ))
    (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rw [h, ← Complex.ofReal_exp]
  congr 1
  calc -∑' r : ℕ, (evenZeta (r + 1) : ℂ) * (x : ℂ) ^ (2 * (r + 1)) / ((r : ℂ) + 1)
      = -∑' r : ℕ, ((evenZeta (r + 1) * x ^ (2 * (r + 1)) / ((r : ℝ) + 1) : ℝ) : ℂ) := by
        congr 1
        exact tsum_congr fun r => by push_cast; ring
    _ = ((-∑' r : ℕ, evenZeta (r + 1) * x ^ (2 * (r + 1)) / ((r : ℝ) + 1) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_tsum, Complex.ofReal_neg]

/-- **`eq:logsinc` for real arguments**: for `0 < |x| < 1`,

`log (sin (πx) / (πx)) = -∑'_{r} ζ(2(r+1)) · x^(2(r+1)) / (r+1)`,

the branch of the logarithm being the real one — the series itself. -/
theorem log_sin_div_pi_mul {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 1) :
    Real.log (Real.sin (π * x) / (π * x)) =
      -∑' r : ℕ, evenZeta (r + 1) * x ^ (2 * (r + 1)) / ((r : ℝ) + 1) := by
  have hπx : (π * x : ℝ) ≠ 0 := mul_ne_zero pi_ne_zero hx0
  have hsinc : complexSinc ((π * x : ℝ) : ℂ) =
      ((Real.sin (π * x) / (π * x) : ℝ) : ℂ) := by
    rw [complexSinc, if_neg (ofReal_ne_zero.mpr hπx), ← Complex.ofReal_sin,
      ← Complex.ofReal_div]
  have h := complexSinc_pi_mul_ofReal hx
  rw [Complex.ofReal_mul] at hsinc
  rw [hsinc] at h
  have hreal : Real.sin (π * x) / (π * x) =
      Real.exp (-∑' r : ℕ, evenZeta (r + 1) * x ^ (2 * (r + 1)) / ((r : ℝ) + 1)) :=
    Complex.ofReal_injective h
  rw [hreal, Real.log_exp]

end Fabius
