import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Basic

/-!
# Even zeta values as elementary series

The values `ζ(2k)`, `k ≥ 1`, enter the sinc-tail calculus of the
frontier drafts as the power sums of the family `n ↦ 1/(n+1)²` — the
inner sums produced by the Euler log transform of the sine product.
This module defines them by the elementary series

`evenZeta k = ∑'_{n : ℕ} 1 / (n+1)^(2k)`

and proves the handful of facts the calculus needs: summability,
the `HasSum` witness, strict positivity, antitonicity in `k`
(`evenZeta l ≤ evenZeta k` for `k ≤ l`, the engine of every
"replace `ζ(2r)` by `ζ(2)`" step), and the coercion identity
expressing the complex power sum `∑' n, 1/((n:ℂ)+1)^(2k)` as the real
value.  No Bernoulli-number or L-series machinery is imported; the
closed evaluations `ζ(2) = π²/6`, `ζ(4) = π⁴/90` live downstream with
their own imports.

* `evenZeta` — the elementary series.
* `summable_one_div_add_one_pow` — summability for `k ≠ 0`.
* `hasSum_evenZeta` — the `HasSum` witness.
* `evenZeta_pos` — strict positivity.
* `evenZeta_anti` — antitonicity on `k ≥ 1`.
* `ofReal_evenZeta` — the complex power-sum form.
-/

set_option autoImplicit false

namespace Fabius

/-- The even zeta value `ζ(2k)` as the elementary real series
`∑'_{n : ℕ} 1/(n+1)^(2k)`.  Meaningful for `k ≥ 1`; at `k = 0` the
series diverges and the `tsum` takes the junk value `0`. -/
noncomputable def evenZeta (k : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (2 * k)

/-- The defining series of `evenZeta` converges for every `k ≥ 1`. -/
theorem summable_one_div_add_one_pow {k : ℕ} (hk : k ≠ 0) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * k) := by
  have h2k : 1 < 2 * k := by omega
  have h := summable_one_div_nat_pow.mpr h2k
  have h' := (summable_nat_add_iff 1).mpr h
  refine h'.congr fun n => ?_
  push_cast
  ring

/-- `evenZeta k` is the sum of its defining series for `k ≥ 1`. -/
theorem hasSum_evenZeta {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * k)) (evenZeta k) :=
  (summable_one_div_add_one_pow hk).hasSum

/-- Every even zeta value with `k ≥ 1` is strictly positive. -/
theorem evenZeta_pos {k : ℕ} (hk : k ≠ 0) : 0 < evenZeta k := by
  have h0 : (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * k)) 0 = 1 := by norm_num
  have hle : (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 * k)) 0 ≤ evenZeta k :=
    le_tsum (summable_one_div_add_one_pow hk) 0 fun n _ => by positivity
  rw [h0] at hle
  linarith

/-- Term-by-term antitonicity: for `1 ≤ k ≤ l` the even zeta values
decrease, `evenZeta l ≤ evenZeta k`.  This is the "replace `ζ(2r)` by
`ζ(2)`" step of every uniform tail bound. -/
theorem evenZeta_anti {k l : ℕ} (hk : k ≠ 0) (hkl : k ≤ l) :
    evenZeta l ≤ evenZeta k := by
  have hl : l ≠ 0 := by omega
  refine tsum_le_tsum (fun n => ?_) (summable_one_div_add_one_pow hl)
    (summable_one_div_add_one_pow hk)
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ h1 (by omega))

/-- The complex power sum `∑' n, 1/((n:ℂ)+1)^(2k)` is the coercion of
the real even zeta value — the form in which `evenZeta` enters complex
Euler log transforms. -/
theorem ofReal_evenZeta (k : ℕ) :
    ((evenZeta k : ℝ) : ℂ) = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ (2 * k) := by
  rw [evenZeta, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  push_cast
  ring

end Fabius
