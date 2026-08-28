import FabiusFunction.EvenZetaSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Closed evaluations of the even zeta values

The link between the elementary series `evenZeta` of
`EvenZetaSeries` and the closed special values: Euler's
`ζ(2) = π²/6` and `ζ(4) = π⁴/90`, the general Bernoulli-number
formula, and the identification with Mathlib's analytically continued
`riemannZeta` at even integers.  These are exactly the substitutions
that turn the symbolic coefficients of the sinc-tail calculus
(`SincZetaSeries`, `SincZetaRemainder`) into the printed numerical
forms of the frontier drafts — e.g. the first correction
`exp(-t²·4^{-m}/18)` of `eq:Q-first-terms` comes from
`ζ(2)·4/(1·(4-1)) = 2π²/9`, and the remainder constant `4ζ(2)/3` is
`2π²/9`.

* `evenZeta_one` — Euler: `evenZeta 1 = π²/6`.
* `evenZeta_two` — `evenZeta 2 = π⁴/90`.
* `evenZeta_eq_bernoulli` — the general closed form.
* `ofReal_evenZeta_eq_riemannZeta` — agreement with the analytic
  continuation: `(evenZeta k : ℂ) = riemannZeta (2k)` for `k ≥ 1`.
-/

set_option autoImplicit false

open Real
open scoped Nat

namespace Fabius

/-- Dropping a vanishing initial term reindexes a `HasSum` over `ℕ`. -/
private theorem hasSum_shift {f : ℕ → ℝ} {S : ℝ} (h0 : f 0 = 0)
    (h : HasSum f S) : HasSum (fun n : ℕ => f (n + 1)) S := by
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simpa [h0] using h'

/-- **Euler's evaluation**: `evenZeta 1 = π²/6`. -/
theorem evenZeta_one : evenZeta 1 = π ^ 2 / 6 := by
  have h := hasSum_shift (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (by norm_num) hasSum_zeta_two
  have hfun : (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * 1)) =
      fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    funext n
    push_cast
    norm_num
  rw [evenZeta, hfun]
  exact h.tsum_eq

/-- `evenZeta 2 = π⁴/90`. -/
theorem evenZeta_two : evenZeta 2 = π ^ 4 / 90 := by
  have h := hasSum_shift (f := fun n : ℕ => 1 / (n : ℝ) ^ 4)
    (by norm_num) hasSum_zeta_four
  have hfun : (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * 2)) =
      fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 4 := by
    funext n
    push_cast
    norm_num
  rw [evenZeta, hfun]
  exact h.tsum_eq

/-- **The Bernoulli closed form of the even zeta values**:
`evenZeta k = (-1)^(k+1) · 2^(2k-1) · π^(2k) · B_(2k) / (2k)!` for
`k ≥ 1`. -/
theorem evenZeta_eq_bernoulli {k : ℕ} (hk : k ≠ 0) :
    evenZeta k = (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
      bernoulli (2 * k) / (2 * k)! := by
  have h0 : (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k)) 0 = 0 := by
    rw [Nat.cast_zero, zero_pow (by omega : 2 * k ≠ 0), div_zero]
  have h := hasSum_shift h0 (hasSum_zeta_nat hk)
  have hfun : (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * k)) =
      fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (2 * k) := by
    funext n
    push_cast
    ring
  rw [evenZeta, hfun]
  exact h.tsum_eq

/-- **Agreement with the analytic continuation**: for `k ≥ 1` the
elementary series equals Mathlib's `riemannZeta` at the even integer
`2k`. -/
theorem ofReal_evenZeta_eq_riemannZeta {k : ℕ} (hk : k ≠ 0) :
    ((evenZeta k : ℝ) : ℂ) = riemannZeta (2 * k) := by
  rw [riemannZeta_two_mul_nat hk, evenZeta_eq_bernoulli hk]
  push_cast
  ring

end Fabius
