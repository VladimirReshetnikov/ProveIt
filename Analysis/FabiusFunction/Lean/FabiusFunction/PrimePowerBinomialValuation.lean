import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Prime-power binomial valuations

For a prime `p`, the `p`-adic valuation of an entry in the Pascal row
indexed by `p ^ m` is determined exactly by the valuation of its column:

`vₚ ((p ^ m).choose j) + vₚ(j) = m`.

The two preceding rows supply companion identities.  Every entry in row
`p ^ m - 1` is a `p`-adic unit, and for `0 < j < p ^ m` one has

`vₚ ((p ^ m - 2).choose (j - 1)) = vₚ(j)`.

Mathlib proves the corresponding statement for `Nat.factorization`.  This
module exposes both the truncation-free additive form and its subtraction
form directly through `padicValNat`, then specializes to `p = 2` in the
strict interior range used by the dyadic-comb barycentric weights.

The row-`p ^ m` results include the right endpoint `j = p ^ m` and the
boundary `m = 0`.  Only `j = 0` is excluded there, since `padicValNat` is
totalized at zero.  The companion row-`p ^ m - 2` identity uses the strict
interior range; its upper bound is essential at `j = p ^ m`.
-/

set_option autoImplicit false

namespace Fabius

/-- In a prime-power Pascal row, the valuations of the row entry and its
positive column index add to the row exponent.

This additive form avoids truncated natural subtraction and is usually the
most convenient interface for arithmetic consequences. -/
theorem primePowerChoose_padicValNat_add {p m j : ℕ}
    (hp : p.Prime) (hj : j ≤ p ^ m) (hj0 : j ≠ 0) :
    padicValNat p ((p ^ m).choose j) + padicValNat p j = m := by
  rw [← Nat.factorization_def ((p ^ m).choose j) hp,
    ← Nat.factorization_def j hp]
  exact Nat.factorization_choose_prime_pow_add_factorization hp hj hj0

/-- Subtraction form of the prime-power Pascal-row valuation identity. -/
theorem primePowerChoose_padicValNat {p m j : ℕ}
    (hp : p.Prime) (hj : j ≤ p ^ m) (hj0 : j ≠ 0) :
    padicValNat p ((p ^ m).choose j) = m - padicValNat p j := by
  rw [← Nat.factorization_def ((p ^ m).choose j) hp,
    ← Nat.factorization_def j hp]
  exact Nat.factorization_choose_prime_pow hp hj hj0

/-- Every entry of the Pascal row indexed by `p ^ m - 1` is a `p`-adic unit.

The range `j < p ^ m` is exactly the full range of columns in that row and
also covers the boundary case `m = 0`. -/
theorem primePowerSubOneChoose_padicValNat {p m j : ℕ}
    (hp : p.Prime) (hj : j < p ^ m) :
    padicValNat p ((p ^ m - 1).choose j) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpPowPos : 0 < p ^ m := pow_pos hp.pos m
  have hjSucc : j + 1 ≤ p ^ m := by omega
  have hjRow : j ≤ p ^ m - 1 := by omega
  have hIdentity := Nat.add_one_mul_choose_eq (p ^ m - 1) j
  rw [Nat.sub_add_cancel hpPowPos] at hIdentity
  have hValuation := congrArg (padicValNat p) hIdentity
  rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) (Nat.choose_ne_zero hjRow),
    padicValNat.mul (Nat.choose_ne_zero hjSucc) (Nat.succ_ne_zero j),
    padicValNat.prime_pow] at hValuation
  simp only [Nat.succ_eq_add_one] at hValuation
  have hPrimePower :=
    primePowerChoose_padicValNat_add hp hjSucc (Nat.succ_ne_zero j)
  omega

/-- **Companion prime-power binomial valuation.**  For `0 < j < p ^ m`,
the valuation of column `j - 1` in row `p ^ m - 2` is exactly the valuation
of `j`:

`vₚ ((p ^ m - 2).choose (j - 1)) = vₚ(j)`.

The strict upper bound prevents the exceptional endpoint `j = p ^ m`, where
the binomial coefficient is zero after natural-number truncation. -/
theorem primePowerSubTwoChoose_padicValNat {p m j : ℕ}
    (hp : p.Prime) (hj0 : 0 < j) (hj : j < p ^ m) :
    padicValNat p ((p ^ m - 2).choose (j - 1)) = padicValNat p j := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpPowTwo : 2 ≤ p ^ m := by omega
  have hjLow : j - 1 ≤ p ^ m - 2 := by omega
  have hjHigh : j ≤ p ^ m - 1 := by omega
  have hPredValuation : padicValNat p (p ^ m - 1) = 0 := by
    simpa only [Nat.choose_one_right] using
      (primePowerSubOneChoose_padicValNat (p := p) (m := m) (j := 1) hp (by omega))
  have hRowValuation := primePowerSubOneChoose_padicValNat hp hj
  have hIdentity := Nat.add_one_mul_choose_eq (p ^ m - 2) (j - 1)
  have hLeftIndex : p ^ m - 2 + 1 = p ^ m - 1 := by omega
  have hRightIndex : j - 1 + 1 = j := Nat.sub_add_cancel hj0
  rw [hLeftIndex, hRightIndex] at hIdentity
  have hValuation := congrArg (padicValNat p) hIdentity
  rw [padicValNat.mul (by omega) (Nat.choose_ne_zero hjLow),
    padicValNat.mul (Nat.choose_ne_zero hjHigh) hj0.ne'] at hValuation
  omega

/-- **Two-adic valuation of the dyadic-comb barycentric weights.**
For every strict interior index of row `2 ^ m`,
`v₂ ((2 ^ m).choose j) = m - v₂(j)`. -/
theorem twoPowChoose_padicValNat (m j : ℕ)
    (hj0 : 0 < j) (hjM : j < 2 ^ m) :
    padicValNat 2 ((2 ^ m).choose j) = m - padicValNat 2 j :=
  primePowerChoose_padicValNat Nat.prime_two hjM.le hj0.ne'

/-- Exact two-adic companion-row identity for the dyadic-comb coefficients. -/
theorem twoPowSubTwoChoose_padicValNat (m j : ℕ)
    (hj0 : 0 < j) (hjM : j < 2 ^ m) :
    padicValNat 2 ((2 ^ m - 2).choose (j - 1)) = padicValNat 2 j :=
  primePowerSubTwoChoose_padicValNat Nat.prime_two hj0 hjM

end Fabius
