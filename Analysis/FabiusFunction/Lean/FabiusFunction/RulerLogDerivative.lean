import FabiusFunction.ThueMorseHessenberg
import FabiusFunction.ThueMorseGenerating
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The logarithmic derivative of the Thue–Morse series

The atlas's `p1:thm:log-E` reads the Euler product `E(z) = ∏ (1 - z^{2^j})`
through its logarithm,

`log E(z) = -∑_{k ≥ 1} (a_k / k) z^k,  a_k = 2^{ν₂(k)+1} - 1`,

"as a formal series, and analytically for `|z| < 1`".  A formal logarithm
carries the denominators `1/k`, so it lives over `ℚ`; but the identity has
an exactly equivalent denominator-free form over `ℤ`, obtained by
differentiating and clearing `E`:

`z E'(z) = -A(z) E(z),  A(z) = ∑_{k ≥ 1} a_k z^k`.

That is what this file proves, as an identity of formal power series with
integer coefficients: `X_mul_derivative_thueMorseSeries`.  Comparing the
coefficient of `z^n` is precisely the ruler-convolution recurrence
`n ε_n = -∑_{k=1}^{n} a_k ε_{n-k}` of `ThueMorseEulerTransform.ruler_convolution`,
so the proof is a coefficient computation on top of that combinatorial
theorem.  Nothing about convergence is used; the analytic reading for
`|z| < 1` follows by evaluating both sides, and the `ℚ`-logarithm by
integrating coefficientwise, neither of which is done here.

## Main declarations

* `rulerSeries` — `A(X) = ∑_{k ≥ 1} a_k X^k` in `ℤ⟦X⟧`, built on the
  corpus's `rulerCoeff k = 2^{ν₂(k)+1} - 1` from `ThueMorseHessenberg`.
* `sum_range_succ_eq_add_sum_Icc` — `∑_{k ≤ n} f k = f 0 + ∑_{1 ≤ k ≤ n} f k`.
* `X_mul_derivative_thueMorseSeries` — **`X · E' = -(A · E)`**, the
  denominator-free form of `p1:eq:log-E`.
-/

set_option autoImplicit false

namespace Fabius

open PowerSeries Finset

/-- `A(X) = ∑_{k ≥ 1} a_k X^k` as an integer power series, with the ruler
coefficient `a_k = 2^{ν₂(k)+1} - 1` of `ThueMorseHessenberg.rulerCoeff` and no
constant term (the atlas's sum starts at `k = 1`; `rulerCoeff 0 = 1` would be
wrong there). -/
noncomputable def rulerSeries : PowerSeries ℤ :=
  PowerSeries.mk fun k => if k = 0 then 0 else rulerCoeff k

/-- Coefficients of `rulerSeries`, including its explicit zero constant term. -/
@[simp] theorem coeff_rulerSeries (k : ℕ) :
    coeff k rulerSeries = if k = 0 then 0 else rulerCoeff k :=
  coeff_mk k _

/-- The constant coefficient of `rulerSeries` is zero. -/
@[simp] theorem coeff_zero_rulerSeries : coeff 0 rulerSeries = 0 := by simp

/-- Every positive-degree coefficient of `rulerSeries` is the corresponding ruler coefficient. -/
theorem coeff_succ_rulerSeries (k : ℕ) : coeff (k + 1) rulerSeries = rulerCoeff (k + 1) := by
  simp

/-- Splitting off the `k = 0` term of a sum over `range (n + 1)`. -/
theorem sum_range_succ_eq_add_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ range (n + 1), f k = f 0 + ∑ k ∈ Icc 1 n, f k := by
  have hIcc : Icc 1 n = (range (n + 1)).filter (fun k => 1 ≤ k) := by
    ext k
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  have h0 : (range (n + 1)).filter (fun k => ¬ 1 ≤ k) = {0} := by
    ext k
    simp only [mem_filter, mem_range, mem_singleton]
    omega
  rw [hIcc, ← sum_filter_add_sum_filter_not (range (n + 1)) (fun k => 1 ≤ k)]
  simp only [h0, sum_singleton]
  exact add_comm _ _

/-- **The logarithmic derivative of the Thue–Morse series** (`p1:eq:log-E`,
denominator-free): `X · E'(X) = -(A(X) · E(X))` in `ℤ⟦X⟧`.  Coefficientwise
this is the ruler-convolution recurrence `n ε_n = -∑_{k=1}^{n} a_k ε_{n-k}`. -/
theorem X_mul_derivative_thueMorseSeries :
    (X : PowerSeries ℤ) * derivative ℤ thueMorseSeries = -(rulerSeries * thueMorseSeries) := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, map_neg, coeff_mul]
    simp
  · rw [coeff_succ_X_mul, coeff_derivative, map_neg, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ_eq_add_sum_Icc]
    simp only [coeff_rulerSeries, thueMorseSeries, coeff_mk, Nat.sub_zero, if_true, zero_mul,
      zero_add]
    have hsum : ∑ k ∈ Icc 1 (n + 1),
        (if k = 0 then (0 : ℤ) else rulerCoeff k) * thueMorseSign (n + 1 - k)
        = ∑ k ∈ Icc 1 (n + 1), ((2 : ℤ) ^ (padicValNat 2 k + 1) - 1) * thueMorseSign (n + 1 - k) := by
      refine sum_congr rfl fun k hk => ?_
      rw [if_neg (by have := (mem_Icc.mp hk).1; omega)]
      rfl
    rw [hsum]
    have h := ruler_convolution (n + 1)
    push_cast at h ⊢
    linear_combination h

end Fabius
