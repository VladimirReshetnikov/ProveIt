import FabiusFunction.RulerLogDerivative
import FabiusFunction.SaddleLogExpansionAlgebra

/-!
# The formal logarithm of the Thue–Morse series

`RulerLogDerivative` proves the denominator-free form `X · E' = -(A · E)` of
the atlas's `p1:thm:log-E`.  This file adds the reading the atlas states
first, the formal logarithm itself:

`log E(z) = -∑_{k ≥ 1} (a_k / k) z^k,   a_k = 2^{ν₂(k)+1} - 1`,

as an identity in `ℚ⟦X⟧` for the corpus's recursively defined formal
logarithm `SaddleExpansion.logCoeff`: `logCoeff ε k = -a_k/k` for `k ≥ 1`
(`logCoeff_thueMorseSign`).  No analytic logarithm and no convergence enter;
the identity is the ruler-convolution recurrence once more, read through the
uniqueness theorem `coeff_eq_logCoeff_of_derivative_mul_eq`.

## Main declarations

* `X_mul_derivative_thueMorseSeriesRat` — `X · E' = -(A · E)` over `ℚ`.
* `rulerLogCoefficient` — the candidate `-a_k/k`.
* `logCoeff_thueMorseSign` — **`p1:eq:log-E` as a formal logarithm**.
-/

set_option autoImplicit false

namespace Fabius

open PowerSeries Finset SaddleExpansion

/-- The Thue–Morse sign series over `ℚ`. -/
noncomputable def thueMorseSeriesRat : PowerSeries ℚ :=
  massSeries fun n => (thueMorseSign n : ℚ)

/-- `A(X) = ∑_{k ≥ 1} a_k X^k` over `ℚ`. -/
noncomputable def rulerSeriesRat : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k = 0 then 0 else (rulerCoeff k : ℚ)

/-- `X · E' = -(A · E)` in `ℚ⟦X⟧`: the rational form of
`X_mul_derivative_thueMorseSeries`, proved by the same coefficient
computation from `ruler_convolution`. -/
theorem X_mul_derivative_thueMorseSeriesRat :
    (X : PowerSeries ℚ) * d⁄dX ℚ thueMorseSeriesRat = -(rulerSeriesRat * thueMorseSeriesRat) := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, map_neg, coeff_mul]
    simp [rulerSeriesRat]
  · rw [coeff_succ_X_mul, coeff_derivative, map_neg, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ_eq_add_sum_Icc]
    simp only [rulerSeriesRat, thueMorseSeriesRat, coeff_mk, coeff_massSeries, Nat.sub_zero,
      if_true, zero_mul, zero_add]
    have hsum : ∑ k ∈ Icc 1 (n + 1),
        (if k = 0 then (0 : ℚ) else (rulerCoeff k : ℚ)) * (thueMorseSign (n + 1 - k) : ℚ)
        = ∑ k ∈ Icc 1 (n + 1),
            (((2 : ℤ) ^ (padicValNat 2 k + 1) - 1) * thueMorseSign (n + 1 - k) : ℤ) := by
      push_cast
      refine sum_congr rfl fun k hk => ?_
      rw [if_neg (by have := (mem_Icc.mp hk).1; omega), rulerCoeff]
      push_cast
      ring
    rw [hsum]
    have h := ruler_convolution (n + 1)
    have h' : ((n + 1 : ℕ) : ℚ) * (thueMorseSign (n + 1) : ℚ)
        = -((∑ k ∈ Icc 1 (n + 1),
            (((2 : ℤ) ^ (padicValNat 2 k + 1) - 1) * thueMorseSign (n + 1 - k) : ℤ) : ℤ) : ℚ) := by
      rw [← Int.cast_neg, ← h]
      push_cast
      ring
    push_cast at h' ⊢
    linear_combination h'

/-- The candidate logarithmic coefficient `-a_k/k` (`0` at `k = 0`). -/
noncomputable def rulerLogCoefficient (k : ℕ) : ℚ :=
  if k = 0 then 0 else -((rulerCoeff k : ℚ) / k)

/-- The zeroth candidate logarithmic coefficient is zero. -/
@[simp] theorem rulerLogCoefficient_zero : rulerLogCoefficient 0 = 0 := by
  simp [rulerLogCoefficient]

/-- `X · Λ' = -A` for the candidate `Λ = ∑ (-a_k/k) X^k`. -/
theorem X_mul_derivative_rulerLog :
    (X : PowerSeries ℚ) * d⁄dX ℚ (mk rulerLogCoefficient) = -rulerSeriesRat := by
  ext n
  rcases n with _ | n
  · simp [coeff_zero_X_mul, rulerSeriesRat]
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_mk, map_neg]
    simp only [rulerSeriesRat, coeff_mk, rulerLogCoefficient, Nat.succ_ne_zero, if_false]
    have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast
    field_simp

/-- **`p1:eq:log-E` as a formal logarithm**: the recursively defined formal
logarithm of the Thue–Morse series `E(z) = ∑ ε_n z^n` has coefficients
`-a_k/k` for `k ≥ 1`, with `a_k = 2^{ν₂(k)+1} - 1` the ruler coefficient. -/
theorem logCoeff_thueMorseSign (k : ℕ) :
    logCoeff (fun n => (thueMorseSign n : ℚ)) k = rulerLogCoefficient k := by
  have hzero : constantCoeff (mk rulerLogCoefficient : PowerSeries ℚ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp
  have ha0 : (fun n => (thueMorseSign n : ℚ)) 0 = 1 := by
    simp [thueMorseSign, binaryWeight]
  have hderiv : massSeries (fun n => (thueMorseSign n : ℚ)) * d⁄dX ℚ (mk rulerLogCoefficient)
      = d⁄dX ℚ (massSeries fun n => (thueMorseSign n : ℚ)) := by
    have h1 := X_mul_derivative_rulerLog
    have h2 := X_mul_derivative_thueMorseSeriesRat
    have h : (X : PowerSeries ℚ) * (massSeries (fun n => (thueMorseSign n : ℚ)) *
        d⁄dX ℚ (mk rulerLogCoefficient))
        = X * d⁄dX ℚ (massSeries fun n => (thueMorseSign n : ℚ)) := by
      unfold thueMorseSeriesRat at h2
      linear_combination (massSeries fun n => (thueMorseSign n : ℚ)) * h1 - h2
    exact mul_left_cancel₀ X_ne_zero h
  have h := coeff_eq_logCoeff_of_derivative_mul_eq _ ha0 hderiv hzero k
  rw [coeff_mk] at h
  exact h.symm

/-- The explicit form: for `k ≥ 1`, `logCoeff ε k = -(2^{ν₂(k)+1} - 1)/k`. -/
theorem logCoeff_thueMorseSign_of_pos {k : ℕ} (hk : 0 < k) :
    logCoeff (fun n => (thueMorseSign n : ℚ)) k
      = -(((2 : ℚ) ^ (padicValNat 2 k + 1) - 1) / k) := by
  rw [logCoeff_thueMorseSign, rulerLogCoefficient, if_neg hk.ne', rulerCoeff]
  push_cast
  rfl

end Fabius
