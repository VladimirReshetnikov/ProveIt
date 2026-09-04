import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat

/-!
# The divisor transform and the disturbance coefficients

The transseries volume's `p1:def:divisor` and `p1:lem:R-coefficients`: for a
sequence `a`,

`b_m = ∑_{d ∣ m} d a_d`,   `ϱ_r = (1/r) ∑_{d ∣ r, d < r} d a_d = (b_r - r a_r)/r`.

The identity between the two forms of `ϱ_r` is pure `Finset` arithmetic — the
divisors of `r` are its proper divisors together with `r` itself, and the term
contributed by `r` is exactly `r a_r` — so it is proved here for an arbitrary
commutative ring, with no reference to rooted trees.

Two further clauses of the lemma get formal counterparts of their own.

*Locality.*  The volume observes that `ϱ_r` depends only on `a_d` with
`d ≤ r/2`.  Formally that is `disturbanceCoeff_congr`: two sequences agreeing at
every `d` with `2d ≤ r` give the same `ϱ_r`.  The arithmetic behind it is
`two_mul_le_of_mem_properDivisors`, that a proper divisor is at most half.

*The prime values.*  The volume lists `ϱ_2 = 1/2`, `ϱ_3 = 1/3`, `ϱ_5 = 1/5` and
`ϱ_7 = 1/7` among its seven numerical values.  These are not four facts but one:
a prime has `{1}` for its proper divisors, so `ϱ_p = a_1/p` for every prime `p`,
which is `disturbanceCoeff_prime`.  The remaining listed values — `ϱ_4 = 3/4`,
`ϱ_6 = 3/2`, `ϱ_8 = 19/8` — depend on the tree numbers themselves and are not
formalized here, this module carrying no particular sequence.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {R : Type*} [CommRing R]

/-- **`p1:eq:divisor`.**  The divisor transform `b_m = ∑_{d ∣ m} d a_d`. -/
def divisorTransform (a : ℕ → R) (m : ℕ) : R := ∑ d ∈ m.divisors, (d : R) * a d

/-- `b_0 = 0`: zero has no divisors in Mathlib's convention. -/
@[simp] theorem divisorTransform_zero (a : ℕ → R) : divisorTransform a 0 = 0 := by
  simp [divisorTransform]

/-- Splitting off the top divisor: `b_m = m a_m + ∑_{d ∣ m, d < m} d a_d`. -/
theorem divisorTransform_eq_add_properDivisors (a : ℕ → R) {m : ℕ} (hm : m ≠ 0) :
    divisorTransform a m = (m : R) * a m + ∑ d ∈ m.properDivisors, (d : R) * a d := by
  rw [divisorTransform, ← Nat.insert_self_properDivisors hm,
    Finset.sum_insert Nat.self_notMem_properDivisors]

/-- **`p1:eq:varrho`, the numerator.**  `b_r - r a_r` is the sum over the proper
divisors. -/
theorem divisorTransform_sub (a : ℕ → R) {m : ℕ} (hm : m ≠ 0) :
    divisorTransform a m - (m : R) * a m = ∑ d ∈ m.properDivisors, (d : R) * a d := by
  rw [divisorTransform_eq_add_properDivisors a hm]
  ring

/-- A proper divisor is at most half: `d ∣ m` and `d < m` force `2d ≤ m`. -/
theorem two_mul_le_of_mem_properDivisors {m d : ℕ} (h : d ∈ m.properDivisors) :
    2 * d ≤ m := by
  have hdvd := (Nat.mem_properDivisors.mp h).1
  have hq : 2 ≤ m / d := Nat.one_lt_div_of_mem_properDivisors h
  calc 2 * d ≤ (m / d) * d := Nat.mul_le_mul hq (le_refl d)
    _ = m := Nat.div_mul_cancel hdvd

/-! ### The disturbance coefficients -/

variable {K : Type*} [Field K] [CharZero K]

/-- **`p1:eq:varrho`.**  `ϱ_r = (1/r) ∑_{d ∣ r, d < r} d a_d`. -/
def disturbanceCoeff (a : ℕ → K) (r : ℕ) : K :=
  (∑ d ∈ r.properDivisors, (d : K) * a d) / r

/-- The second form of `p1:eq:varrho`: `ϱ_r = (b_r - r a_r)/r`. -/
theorem disturbanceCoeff_eq_divisorTransform (a : ℕ → K) {r : ℕ} (hr : r ≠ 0) :
    disturbanceCoeff a r = (divisorTransform a r - (r : K) * a r) / r := by
  rw [disturbanceCoeff, divisorTransform_sub a hr]

/-- `ϱ_r` vanishes for `r ≤ 1`: there are no proper divisors to sum. -/
@[simp] theorem disturbanceCoeff_one (a : ℕ → K) : disturbanceCoeff a 1 = 0 := by
  simp [disturbanceCoeff]

/-- **Locality.**  `ϱ_r` sees only the values `a_d` with `2d ≤ r`, which is the
volume's "depends only on `a_d` with `d ≤ r/2`". -/
theorem disturbanceCoeff_congr {a a' : ℕ → K} {r : ℕ}
    (h : ∀ d, 2 * d ≤ r → a d = a' d) : disturbanceCoeff a r = disturbanceCoeff a' r := by
  rw [disturbanceCoeff, disturbanceCoeff]
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [h d (two_mul_le_of_mem_properDivisors hd)]

/-- **The prime values in one statement.**  For a prime `p`, the only proper
divisor is `1`, so `ϱ_p = a_1 / p`.  With `a_1 = 1` this is the volume's
`ϱ_2 = 1/2`, `ϱ_3 = 1/3`, `ϱ_5 = 1/5`, `ϱ_7 = 1/7` at once. -/
theorem disturbanceCoeff_prime (a : ℕ → K) {p : ℕ} (hp : p.Prime) :
    disturbanceCoeff a p = a 1 / p := by
  rw [disturbanceCoeff, hp.properDivisors]
  simp

/-- Nonnegativity, when the sequence is nonnegative: `ϱ_r ≥ 0`, the volume's
`ϱ_r ∈ ℚ_{≥0}`. -/
theorem disturbanceCoeff_nonneg {a : ℕ → ℚ} (ha : ∀ n, 0 ≤ a n) (r : ℕ) :
    0 ≤ disturbanceCoeff a r := by
  rw [disturbanceCoeff]
  refine div_nonneg ?_ (Nat.cast_nonneg r)
  exact Finset.sum_nonneg fun d _ => mul_nonneg (Nat.cast_nonneg d) (ha d)

end Fabius
