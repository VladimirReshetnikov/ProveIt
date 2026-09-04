import FabiusFunction.DyadicClosedForm
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The sparse Thue–Morse binomial identity

The diagonal-polynomial draft's central identity: a Thue–Morse-signed
binomial sum over *all* offsets collapses to a sum over *even* offsets
only, with the polynomial argument dropped by one,

`∑_{a≤q} εₐ·C(r+q−a, q−a) = ∑_{2j≤q} εⱼ·C(r+q−2j−1, q−2j)`,

where `C` is the polynomial binomial coefficient `Ring.choose`.  The
draft states it for `r = 2x` with `x` an indeterminate; nothing depends
on that, so it is proved for an arbitrary element `r` of an arbitrary
binomial ring — integers, rationals, and polynomial rings alike.

Pairing an even-length range is `DyadicClosedForm.sum_range_two_mul`.
The mechanism is the halving law of the Thue–Morse sign, `ε_{2j} = εⱼ`
and `ε_{2j+1} = −εⱼ`: pairing the offsets `2j` and `2j+1` turns each
pair into a Pascal difference `C(m+1, k+1) − C(m, k) = C(m, k+1)`.  For
even `q` the unpaired last offset `a = q` contributes `ε_{q/2}·C(r,0) =
ε_{q/2}`, which is the last sparse term `ε_{q/2}·C(r−1, 0)`.

* `thueMorse_choose_pair` — one Pascal pair.
* `thueMorse_choose_dense_eq_sparse` — **the identity**.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]

/-- The halving law in the form the pairing needs. -/
theorem thueMorseSign_two_mul_add_one' (j : ℕ) :
    thueMorseSign (2 * j + 1) = -thueMorseSign j :=
  thueMorseSign_two_mul_add_one j

/-- **One Pascal pair**: the offsets `2j` and `2j+1` combine into a
single binomial with the argument dropped by one. -/
theorem thueMorse_choose_pair (r : R) (j k : ℕ) :
    ((thueMorseSign (2 * j) : ℤ) : R) * Ring.choose (r + (k + 1 : ℕ)) (k + 1) +
      ((thueMorseSign (2 * j + 1) : ℤ) : R) * Ring.choose (r + (k : ℕ)) k =
    ((thueMorseSign j : ℤ) : R) * Ring.choose (r + (k : ℕ)) (k + 1) := by
  rw [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one']
  have hp : Ring.choose (r + (k + 1 : ℕ)) (k + 1) =
      Ring.choose (r + (k : ℕ)) k + Ring.choose (r + (k : ℕ)) (k + 1) := by
    rw [show r + (k + 1 : ℕ) = (r + (k : ℕ)) + 1 by push_cast; ring]
    exact Ring.choose_succ_succ _ k
  rw [hp]
  push_cast
  ring

/-- **The sparse Thue–Morse binomial identity**, for every element `r`
of every binomial ring. -/
theorem thueMorse_choose_dense_eq_sparse (r : R) (q : ℕ) :
    ∑ a ∈ Finset.range (q + 1),
        ((thueMorseSign a : ℤ) : R) * Ring.choose (r + ((q - a : ℕ) : R)) (q - a) =
      ∑ j ∈ Finset.range (q / 2 + 1),
        ((thueMorseSign j : ℤ) : R) *
          Ring.choose (r + ((q - 2 * j : ℕ) : R) - 1) (q - 2 * j) := by
  -- the paired term, written with the explicit drop `k = q - 2j - 1`
  have hpair : ∀ j : ℕ, 2 * j + 1 ≤ q →
      ((thueMorseSign (2 * j) : ℤ) : R) *
          Ring.choose (r + ((q - 2 * j : ℕ) : R)) (q - 2 * j) +
        ((thueMorseSign (2 * j + 1) : ℤ) : R) *
          Ring.choose (r + ((q - (2 * j + 1) : ℕ) : R)) (q - (2 * j + 1)) =
      ((thueMorseSign j : ℤ) : R) *
        Ring.choose (r + ((q - 2 * j : ℕ) : R) - 1) (q - 2 * j) := by
    intro j hj
    set k : ℕ := q - (2 * j + 1) with hk
    have h1 : q - 2 * j = k + 1 := by omega
    have h3 : r + ((k + 1 : ℕ) : R) - 1 = r + (k : ℕ) := by push_cast; ring
    rw [h1, h3]
    exact thueMorse_choose_pair r j k
  rcases Nat.even_or_odd' q with ⟨m, hq | hq⟩
  · -- even `q = 2m`: pairs `j < m`, plus the unpaired last offset `a = 2m`
    subst hq
    have hdiv : 2 * m / 2 = m := by omega
    rw [hdiv, Finset.sum_range_succ, sum_range_two_mul, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      exact hpair j (by have := Finset.mem_range.mp hj; omega)
    · simp [thueMorseSign_two_mul]
  · -- odd `q = 2m+1`: every offset is paired
    subst hq
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, sum_range_two_mul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    exact hpair j (by have := Finset.mem_range.mp hj; omega)

end Fabius
