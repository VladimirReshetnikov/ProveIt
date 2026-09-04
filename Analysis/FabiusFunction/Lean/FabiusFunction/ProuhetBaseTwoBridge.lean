import FabiusFunction.BaseDigitProuhet
import FabiusFunction.ThueMorsePrefix

/-!
# The Thue–Morse power sums are the base-two case of Prouhet in base `q`

`BaseDigitProuhet` proves the general theorem: for `q ≥ 2` and a
nontrivial `q`-th root of unity `ζ`, the digit-weighted power sums
`P_d(m) = ∑_{n<q^m} ζ^(s_q n) n^d` vanish for `d < m` and satisfy the
sharp moment `(ζ-1)^m·P_m(m) = m!·q^(0+1+⋯+m)`.  `ThueMorsePrefix`
proves the classical base-two statements about
`∑_{n<2^m} ε(n)·n^d`.  Nothing connected the two, although the second is
exactly the first at `q = 2`, `ζ = -1`: the Thue–Morse sign
`ε(n) = (-1)^(w n)` **is** `ζ^(s_q n)` there, because `w` is by
definition the base-two digit sum.

This leaf records the identification and reads each theory in the
other's terms.  In particular it gives the general sharp moment at
`q = 2` in **closed, division-free form** — the general module states it
only as `(ζ-1)^m·P_m(m) = m!·q^(…)`, and dividing by `(ζ-1)^m = (-2)^m`
requires the ring to be a field there.

* `thueMorseSign_cast_eq_neg_one_pow_digits_sum` — `ε(n) = (-1)^(s₂ n)`
  in any commutative ring.
* `digitPowerSum_neg_one_two` — **the identification**
  `P_d(m) = ∑_{n<2^m} ε(n)·n^d` at `ζ = -1`, `q = 2`.
* `digitPowerSum_neg_one_two_eq_zero_of_lt` — base-two Prouhet
  cancellation, obtained from the general machine.
* `digitPowerSum_neg_one_two_self` — the general sharp moment at `q = 2`
  in closed form `(-1)^m·2^(m choose 2)·m!`, over any commutative ring.
* `sub_one_pow_mul_thueMorsePowerSumRing_self` — the same identity read
  back on the Thue–Morse side, division-free.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {R : Type*} [CommRing R]

/-- The Thue–Morse sign is the `(-1)`-power of the base-two digit sum,
in any commutative ring: `w` is *defined* as `(Nat.digits 2 n).sum`. -/
theorem thueMorseSign_cast_eq_neg_one_pow_digits_sum (n : ℕ) :
    ((thueMorseSign n : ℤ) : R) = (-1 : R) ^ (Nat.digits 2 n).sum := by
  rw [thueMorseSign]
  push_cast
  rfl

/-- **The identification.**  The general digit-weighted power sum at
`q = 2` and `ζ = -1` is the Thue–Morse block power sum. -/
theorem digitPowerSum_neg_one_two (m d : ℕ) :
    digitPowerSum (-1 : R) 2 m d = thueMorsePowerSumRing R m d := by
  rw [digitPowerSum, thueMorsePowerSumRing,
    Fin.sum_univ_eq_sum_range
      (fun n : ℕ => ((thueMorseSign n : ℤ) : R) * (n : R) ^ d) (2 ^ m)]
  exact Finset.sum_congr rfl fun n _ => by
    rw [thueMorseSign_cast_eq_neg_one_pow_digits_sum]

/-- `∑_{r<2} (-1)^r = 0` in any commutative ring: the two-term geometric
sum of the nontrivial square root of unity. -/
theorem sum_range_two_neg_one_pow : ∑ r ∈ range 2, (-1 : R) ^ r = 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- **Base-two Prouhet cancellation from the general machine**: for
`d < m` the Thue–Morse block power sum vanishes.  This is
`digitPowerSum_eq_zero_of_lt` at `q = 2`, `ζ = -1`, and it reproves
`thueMorsePowerSumRing_eq_zero_of_lt` through a different route. -/
theorem digitPowerSum_neg_one_two_eq_zero_of_lt {m d : ℕ} (hd : d < m) :
    digitPowerSum (-1 : R) 2 m d = 0 :=
  digitPowerSum_eq_zero_of_lt (by norm_num)
    (sum_range_two_neg_one_pow (R := R)) m d hd

/-- **The general sharp moment at `q = 2`, in closed division-free
form**: `P_m(m) = (-1)^m·2^(m choose 2)·m!` over any commutative ring.
The general statement carries the factor `(ζ-1)^m = (-2)^m` on the left
and can only be divided out in a field; here the Thue–Morse evaluation
supplies the closed value directly. -/
theorem digitPowerSum_neg_one_two_self (m : ℕ) :
    digitPowerSum (-1 : R) 2 m m =
      (-1 : R) ^ m * 2 ^ m.choose 2 * m.factorial := by
  rw [digitPowerSum_neg_one_two]
  exact thueMorsePowerSumRing_self m

/-- The general division-free sharp moment, read on the Thue–Morse side:
`(-2)^m·∑_{n<2^m} ε(n)·n^m = m!·2^(0+1+⋯+m)`.  Together with
`thueMorsePowerSumRing_self` this is the exponent identity
`m + (m choose 2) = 0+1+⋯+m`. -/
theorem sub_one_pow_mul_thueMorsePowerSumRing_self (m : ℕ) :
    ((-1 : R) - 1) ^ m * thueMorsePowerSumRing R m m =
      (m.factorial : R) * (2 : R) ^ (∑ i ∈ range (m + 1), i) := by
  rw [← digitPowerSum_neg_one_two]
  exact sub_one_pow_mul_digitPowerSum_self (by norm_num) (by norm_num)
    (sum_range_two_neg_one_pow (R := R)) m

end Fabius
