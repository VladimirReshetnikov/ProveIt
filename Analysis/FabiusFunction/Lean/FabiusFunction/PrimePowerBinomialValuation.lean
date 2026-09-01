import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Prime-power binomial valuations

For a prime `p`, the `p`-adic valuation of an entry in the Pascal row
indexed by `p ^ m` is determined exactly by the valuation of its column:

`vₚ ((p ^ m).choose j) + vₚ(j) = m`.

Mathlib proves the corresponding statement for `Nat.factorization`.  This
module exposes both the truncation-free additive form and its subtraction
form directly through `padicValNat`, then specializes to `p = 2` in the
strict interior range used by the dyadic-comb barycentric weights.

The generic results include the right endpoint `j = p ^ m` and the boundary
`m = 0`.  Only `j = 0` is excluded, since `padicValNat` is totalized there.
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

/-- **Two-adic valuation of the dyadic-comb barycentric weights.**
For every strict interior index of row `2 ^ m`,
`v₂ ((2 ^ m).choose j) = m - v₂(j)`. -/
theorem twoPowChoose_padicValNat (m j : ℕ)
    (hj0 : 0 < j) (hjM : j < 2 ^ m) :
    padicValNat 2 ((2 ^ m).choose j) = m - padicValNat 2 j :=
  primePowerChoose_padicValNat Nat.prime_two hjM.le hj0.ne'

end Fabius
