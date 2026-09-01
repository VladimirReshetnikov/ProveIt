import FabiusFunction.QPochhammerInfinite
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# q-Pochhammer symbols of complex order

For `‖q‖ < 1` the infinite product defines the symbol of arbitrary complex
order `α` by

`(a;q)_α = (a;q)_∞ / (aq^α;q)_∞`,  `q^α = exp(α log q)` (principal branch),

whenever the denominator is nonzero.  The definition is forced by the
concatenation law: the identities

* `(a;q)_{α+β} = (a;q)_α (aq^α;q)_β`,
* `(a;q)_{α+1} = (1 - aq^α)(a;q)_α`,
* `(a;q)_n = (a;q)_∞/(aq^n;q)_∞` for natural `n`,

are all immediate from the tail factorization `(a;q)_∞ = (a;q)_n (aq^n;q)_∞`
and `q^{α+β} = q^α q^β`.  Because Lean's division by zero is zero, each
identity carries the nonvanishing hypothesis that makes the symbols on its
right-hand side defined.

## Main declarations

* `qPochhammerC`: the symbol of complex order.
* `qPochhammerC_natCast`: agreement with the finite symbol.
* `qPochhammerC_add`: complex concatenation.
* `qPochhammerC_add_one`: the shift.
-/

set_option autoImplicit false

namespace Fabius

/-- The `q`-Pochhammer symbol of complex order `α`: `(a;q)_α = (a;q)_∞ / (aq^α;q)_∞`,
with the principal branch of `q^α`. -/
noncomputable def qPochhammerC (a q α : ℂ) : ℂ :=
  qPochhammerInfIn a q / qPochhammerInfIn (a * q ^ α) q

/-- `(a;q)_0 = 1` whenever `(a;q)_∞ ≠ 0`. -/
theorem qPochhammerC_zero {a q : ℂ} (ha : qPochhammerInfIn a q ≠ 0) : qPochhammerC a q 0 = 1 := by
  rw [qPochhammerC, Complex.cpow_zero, mul_one, div_self ha]

/-- **Agreement with the finite symbol**: `(a;q)_n = (a;q)_∞/(aq^n;q)_∞` for natural `n`,
whenever the denominator is nonzero. -/
theorem qPochhammerC_natCast {a q : ℂ} (hq : ‖q‖ < 1) (n : ℕ)
    (h : qPochhammerInfIn (a * q ^ n) q ≠ 0) :
    qPochhammerC a q n = finiteQPochhammerIn a q n := by
  rw [qPochhammerC, Complex.cpow_natCast, qPochhammerInfIn_eq_finite_mul_shift a hq n,
    mul_div_cancel_right₀ _ h]

/-- **Complex concatenation**: `(a;q)_{α+β} = (a;q)_α (aq^α;q)_β` for `q ≠ 0`, whenever
`(aq^α;q)_∞ ≠ 0`. -/
theorem qPochhammerC_add {a q : ℂ} (hq0 : q ≠ 0) (α β : ℂ)
    (h : qPochhammerInfIn (a * q ^ α) q ≠ 0) :
    qPochhammerC a q (α + β) = qPochhammerC a q α * qPochhammerC (a * q ^ α) q β := by
  rw [qPochhammerC, qPochhammerC, qPochhammerC, Complex.cpow_add _ _ hq0, ← mul_assoc,
    div_mul_div_comm,
    mul_comm (qPochhammerInfIn (a * q ^ α) q) (qPochhammerInfIn (a * q ^ α * q ^ β) q),
    mul_div_mul_right _ _ h]

/-- **The shift** `(a;q)_{α+1} = (1 - aq^α)(a;q)_α` for `‖q‖ < 1`, `q ≠ 0`, whenever
`1 - aq^α ≠ 0`. -/
theorem qPochhammerC_add_one {a q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (α : ℂ)
    (h : 1 - a * q ^ α ≠ 0) :
    qPochhammerC a q (α + 1) = (1 - a * q ^ α) * qPochhammerC a q α := by
  have hshift : qPochhammerInfIn (a * q ^ α) q =
      (1 - a * q ^ α) * qPochhammerInfIn (a * q ^ (α + 1)) q := by
    rw [Complex.cpow_add _ _ hq0, Complex.cpow_one, ← mul_assoc]
    exact qPochhammerInfIn_succ_shift (a * q ^ α) hq
  rw [qPochhammerC, qPochhammerC, hshift, mul_div_assoc', mul_div_mul_left _ _ h]

end Fabius
