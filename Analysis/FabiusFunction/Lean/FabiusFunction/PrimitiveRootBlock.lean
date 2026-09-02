import FabiusFunction.CyclotomicFactorization
import FabiusFunction.GaussianBinomialPalindromic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Gaussian coefficients at a primitive root of unity, and the complete root block

Let `ζ` be a primitive `d`-th root of unity in an integral domain.  Since
`Φ_d(ζ) = 0` and `Φ_d` divides `[d,k]_X` for `0 < k < d` (its exponent
`e_d(d,k) = 1 - 0 - 0` in the cyclotomic factorization), the Gaussian
coefficients `[d,k]_ζ` vanish for `0 < k < d`.  In the finite `q`-binomial
theorem at `q = ζ` only the extreme terms survive, which gives the
**complete root-of-unity block**

`∏_{j=0}^{d-1} (1 - y ζ^j) = 1 - y^d`,

after the phase `(-1)^d ζ^{\binom d2} = -1` is evaluated (for even `d`,
`ζ^{d/2} = -1`).

## Main declarations

* `gaussianBinomial_isPrimitiveRoot_eq_zero`: `[d,k]_ζ = 0` for `0 < k < d`.
* `neg_one_pow_mul_pow_choose_two`: the phase `(-1)^d ζ^{\binom d2} = -1`.
* `finiteQPochhammerIn_isPrimitiveRoot`: the complete root block.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

variable {R : Type*} [CommRing R] [IsDomain R]

/-- At a primitive `d`-th root of unity, `[d,k]_ζ = 0` for `0 < k < d`. -/
theorem gaussianBinomial_isPrimitiveRoot_eq_zero {ζ : R} {d : ℕ} (hζ : IsPrimitiveRoot ζ d)
    {k : ℕ} (hk0 : 0 < k) (hkd : k < d) : gaussianBinomial ζ d k = 0 := by
  have hd : 0 < d := hk0.trans hkd
  have h := map_gaussianBinomial (evalRingHom ζ) (X : R[X]) d k
  rw [coe_evalRingHom, eval_X] at h
  rw [← h, gaussianBinomial_X_eq_prod_cyclotomic hkd.le, eval_prod]
  refine Finset.prod_eq_zero (i := d) (Finset.mem_Icc.mpr ⟨hd, le_rfl⟩) ?_
  rw [eval_pow, show d / d - k / d - (d - k) / d = 1 by
    rw [Nat.div_self hd, Nat.div_eq_of_lt hkd, Nat.div_eq_of_lt (by omega)], pow_one]
  exact hζ.isRoot_cyclotomic hd

/-- The phase of the top term of the root block: `(-1)^d ζ^{\binom d2} = -1` for a
primitive `d`-th root of unity, `d ≥ 1`. -/
theorem neg_one_pow_mul_pow_choose_two {ζ : R} {d : ℕ} (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d) :
    (-1 : R) ^ d * ζ ^ d.choose 2 = -1 := by
  rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- d = m + m, so ζ^m = -1 and C(d,2) = m (m + m - 1) is m times an odd number
    have hm0 : 0 < m := by omega
    have hζm : ζ ^ m = -1 := by
      have h2 : IsPrimitiveRoot (ζ ^ m) 2 := hζ.pow hd (by omega : d = m * 2)
      exact h2.eq_neg_one_of_two_right
    have hc : d.choose 2 = m * (m + m - 1) := by
      rw [Nat.choose_two_right, hm, show (m + m) * (m + m - 1) = 2 * (m * (m + m - 1)) by ring,
        Nat.mul_div_cancel_left _ two_pos]
    rw [hc, pow_mul, hζm, hm, Even.neg_one_pow ⟨m, rfl⟩, one_mul,
      Odd.neg_one_pow ⟨m - 1, by omega⟩]
  · -- d = 2m + 1, so C(d,2) = m d and ζ^{md} = 1
    have hc : d.choose 2 = m * d := by
      rw [Nat.choose_two_right, hm, show (2 * m + 1) * (2 * m + 1 - 1) = 2 * (m * (2 * m + 1)) by
        rw [Nat.add_sub_cancel]; ring, Nat.mul_div_cancel_left _ two_pos]
    rw [hc, mul_comm m d, pow_mul, hζ.pow_eq_one, one_pow, mul_one, hm,
      Odd.neg_one_pow ⟨m, rfl⟩]

/-- **A complete root-of-unity block**: `∏_{j<d} (1 - y ζ^j) = 1 - y^d` for a primitive
`d`-th root of unity `ζ`. -/
theorem finiteQPochhammerIn_isPrimitiveRoot {ζ : R} {d : ℕ} (hd : 0 < d)
    (hζ : IsPrimitiveRoot ζ d) (y : R) : finiteQPochhammerIn y ζ d = 1 - y ^ d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [← finite_qBinomial_theorem ζ y (e + 1), Finset.sum_range_succ, Finset.sum_range_succ',
    Finset.sum_eq_zero fun k hk => ?_]
  · rw [gaussianBinomial_diag', mul_one, gaussianBinomial_zero_right]
    simp only [Nat.choose_zero_succ, pow_zero, mul_one, zero_add]
    rw [neg_one_pow_mul_pow_choose_two hd hζ, neg_one_mul, sub_eq_add_neg]
  · rw [gaussianBinomial_isPrimitiveRoot_eq_zero hζ (Nat.succ_pos k)
      (by simpa using Finset.mem_range.mp hk), mul_zero, zero_mul]

end Fabius
