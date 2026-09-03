import FabiusFunction.ThueMorseBitSupport
import FabiusFunction.ThueMorseBooleanCube

/-!
# The finite Thue--Morse product identity and the subset-sum polynomial

The classical finite identity
`∏_{r<n} (1 - z^{2^r}) = ∑_{j<2^n} (-1)^{w(j)} z^j`, over any
commutative ring: expanding the product over the Boolean cube
(`Finset.prod_add`) and reindexing subsets of `range n` by their
encoded integers turns each subset's sign into the binary-weight sign
of its code.

Multiplying by the duplicated smallest factor `1-z` takes first
differences of the sign word — the subset-sum polynomial `B_n` of the
exact-spline layer, whose coefficients weight the knots of the finite
box splines converging to the up function.  Evaluation at `z = 1`
recovers the balance of the level-`n` sign word.
-/

set_option autoImplicit false

open Finset

namespace Fabius

variable {R : Type*} [CommRing R]

/-- **The finite Thue--Morse product identity**: over any commutative
ring, `∏_{r<n} (1 - z^{2^r}) = ∑_{j<2^n} (-1)^{w(j)} z^j`. -/
theorem prod_one_sub_pow_two_pow (z : R) (n : ℕ) :
    ∏ r ∈ range n, (1 - z ^ 2 ^ r) =
      ∑ j ∈ range (2 ^ n), (thueMorseSign j : R) * z ^ j :=
  prod_one_sub_pow_eq_sum_thueMorseSign z n

/-- The first difference `Δτ_n(j) = τ_n(j) - τ_n(j-1)` of the
level-`n` Thue--Morse sign word padded by zero outside `[0, 2^n)` —
the coefficient word of the subset-sum polynomial `B_n`. -/
def thueMorseWordDelta (n j : ℕ) : ℤ :=
  (if j < 2 ^ n then thueMorseSign j else 0) -
    (if 1 ≤ j ∧ j ≤ 2 ^ n then thueMorseSign (j - 1) else 0)

/-- **The subset-sum polynomial**: multiplying the Thue--Morse product
by the duplicated smallest factor takes first differences of the sign
word, `(1-z)·∏_{r<n}(1-z^{2^r}) = ∑_{j≤2^n} Δτ_n(j)·z^j` — the knot
weights of the exact finite box splines. -/
theorem one_sub_mul_prod_one_sub_pow_two_pow (z : R) (n : ℕ) :
    (1 - z) * ∏ r ∈ range n, (1 - z ^ 2 ^ r) =
      ∑ j ∈ range (2 ^ n + 1), (thueMorseWordDelta n j : R) * z ^ j := by
  rw [prod_one_sub_pow_two_pow]
  have hpad : ∑ j ∈ range (2 ^ n), (thueMorseSign j : R) * z ^ j =
      ∑ j ∈ range (2 ^ n + 1),
        ((if j < 2 ^ n then thueMorseSign j else 0 : ℤ) : R) * z ^ j := by
    rw [sum_range_succ, if_neg (lt_irrefl (2 ^ n)), Int.cast_zero,
      zero_mul, add_zero]
    exact sum_congr rfl fun j hj => by rw [if_pos (mem_range.mp hj)]
  have hshift : z * ∑ j ∈ range (2 ^ n), (thueMorseSign j : R) * z ^ j =
      ∑ j ∈ range (2 ^ n + 1),
        ((if 1 ≤ j ∧ j ≤ 2 ^ n then thueMorseSign (j - 1) else 0 :
          ℤ) : R) * z ^ j := by
    rw [Finset.mul_sum, sum_range_succ']
    have h0 : ((if 1 ≤ 0 ∧ 0 ≤ 2 ^ n then thueMorseSign (0 - 1) else 0 :
        ℤ) : R) * z ^ 0 = 0 := by
      rw [if_neg (by omega), Int.cast_zero, zero_mul]
    rw [h0, add_zero]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.mp hj
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
    ring
  calc (1 - z) * ∑ j ∈ range (2 ^ n), (thueMorseSign j : R) * z ^ j
      = (∑ j ∈ range (2 ^ n), (thueMorseSign j : R) * z ^ j) -
          z * ∑ j ∈ range (2 ^ n), (thueMorseSign j : R) * z ^ j := by
        ring
    _ = (∑ j ∈ range (2 ^ n + 1),
          ((if j < 2 ^ n then thueMorseSign j else 0 : ℤ) : R) * z ^ j) -
        ∑ j ∈ range (2 ^ n + 1),
          ((if 1 ≤ j ∧ j ≤ 2 ^ n then thueMorseSign (j - 1) else 0 :
            ℤ) : R) * z ^ j := by
        rw [hshift, hpad]
    _ = ∑ j ∈ range (2 ^ n + 1),
          (((if j < 2 ^ n then thueMorseSign j else 0 : ℤ) : R) * z ^ j -
           ((if 1 ≤ j ∧ j ≤ 2 ^ n then thueMorseSign (j - 1) else 0 :
             ℤ) : R) * z ^ j) := by
        rw [← sum_sub_distrib]
    _ = ∑ j ∈ range (2 ^ n + 1),
          (thueMorseWordDelta n j : R) * z ^ j := by
        refine sum_congr rfl fun j _ => ?_
        unfold thueMorseWordDelta
        rw [Int.cast_sub, sub_mul]

/-- **The duplicated smallest factor**: the subset-sum polynomial is
`B_n(z) = (1-z)²·∏_{r=1}^{n-1}(1-z^{2^r})` — the doubled uniform
interval of half-width `2^{-n}` in the finite box-spline
convolution. -/
theorem one_sub_mul_prod_eq_sq_mul (z : R) (n : ℕ) :
    (1 - z) * ∏ r ∈ range (n + 1), (1 - z ^ 2 ^ r) =
      (1 - z) ^ 2 * ∏ r ∈ range n, (1 - z ^ 2 ^ (r + 1)) := by
  rw [prod_range_succ']
  simp only [pow_zero, pow_one]
  ring

/-- **The balanced sign word**: evaluation of the product identity at
`z = 1` — the level-`n` Thue--Morse block sums to zero for `n ≥ 1`. -/
theorem sum_thueMorseSign_two_pow {n : ℕ} (hn : n ≠ 0) :
    ∑ j ∈ range (2 ^ n), thueMorseSign j = 0 := by
  have h := prod_one_sub_pow_two_pow (1 : ℤ) n
  rw [prod_eq_zero (mem_range.mpr (Nat.pos_of_ne_zero hn))
    (by norm_num)] at h
  simp only [one_pow, mul_one, Int.cast_id] at h
  exact h.symm

end Fabius
