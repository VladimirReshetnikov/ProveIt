import FabiusFunction.FabiusQBinomialFormula
import FabiusFunction.QBinomialReciprocity
import FabiusFunction.QPochhammerElementaryIdentities

/-!
# The dyadic Fabius formula in Gaussian-binomial form

The q-binomial--Thue--Morse formula of `FabiusQBinomialFormula` computes the
exact rational value `F(2^{-n})` as

`F(2^{-n}) = 1 / (2^{n^2} (1/2; 1/2)_n)
    * ∑_{k ≤ n} QBinomial[n, k, 1/2] / (4^{C(k,2)} (n+k)!) * T_k(n+k)`,

where `T_k(m) = ∑_{r < 2^k} ε(r) (r - 2^k)^m` is the centered Thue--Morse
block sum.  Both the prefactor and the summand are written with a *quotient*
q-binomial at the base `1/2`, and neither is identified with anything else.

This module removes the base `1/2` entirely.  Two independent
normalizations are carried out and then combined.

**The prefactor is a falling `2`-product.**  Over an arbitrary commutative
ring, `prod_pow_sub_pow_self_eq` records

`∏_{i<n} (q^n - q^i) = q^{C(n,2)} ∏_{j<n} (q^{j+1} - 1)`,

with no hypothesis on `q`; it is the diagonal case `N = k = n` of the
existing `prod_pow_sub_pow_eq_finiteQPochhammerIn`.  Combined with the
Mersenne normalization `two_pow_nat_sq_mul_halfQPochhammer` of
`HalfQBinomial`, this turns the prefactor into

`2^{n^2} (1/2; 1/2)_n = ∏_{i<n} (2^n - 2^i)`.

The right-hand side is the order of `GL_n(𝔽_2)`; that identification needs
finite-field counting and is made separately in
`FabiusGeneralLinearDenominator`, which imports this module.

**The two powers of two in the summand collapse.**  Gaussian reciprocity
(`gaussianBinomial_reciprocity`) turns the quotient q-binomial at `1/2` into
the polynomial Gaussian binomial at `2`, at the cost of `2^{k(n-k)}`; the
existing `four_pow_choose_two` rewrites `4^{C(k,2)}` as `2^{k(k-1)}`.  The
two exponents merge, because for `k ≤ n`

`k(n-k) + k(k-1) + k = kn`  (`exponent_collapse`),

so the whole summand denominator is the single power `2^{kn}`:

`QBinomial[n,k,1/2] / 4^{C(k,2)} = [n choose k]_2 · 2^k / 2^{kn}`.

The resulting form of the identity,
`fabiusAtInverseTwoPow_eq_gaussian_div_prod`, has no q-Pochhammer quotient,
no `4^{C(k,2)}` and no `2^{n^2}`; its only q-object is the *integer*
Gaussian binomial `[n choose k]_2`, which counts the `k`-dimensional
subspaces of `𝔽_2^n`.

## Main results

* `prod_pow_sub_pow_self_eq` — the denominator-free falling-product
  identity over any commutative ring.
* `two_pow_nat_sq_mul_halfQPochhammer_eq_prod` and
  `two_pow_nat_sq_mul_qPochhammer_half_eq_prod` — the formula's prefactor
  as `∏_{i<n} (2^n - 2^i)`.
* `exponent_collapse` — the natural-number exponent identity behind the
  merge of `2^{k(n-k)}` and `4^{C(k,2)}`.
* `gaussianThueMorseNumerator` and `gaussianThueMorseNumerator_eq` — the
  numerator rewritten over the polynomial Gaussian binomials at base `2`.
* `fabiusAtInverseTwoPow_eq_gaussian_div_prod` and
  `fabiusAtInverseTwoPow_eq_gaussian_sum` — the dyadic identity in Gaussian
  form, the second with both finite sums displayed literally.
* `fabius_inverse_two_pow_eq_gaussian_div_prod` — the real-valued form for
  the canonical Fabius function.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-! ## The falling product of powers -/

/-- Reversing the sign of every Mersenne factor.  Stated separately from
`prod_pow_sub_pow_self_eq` because the induction is cleaner than any
rewrite of `Finset.prod_const` through the two occurrences of `n`. -/
private theorem prod_pow_succ_sub_one_eq (R : Type*) [CommRing R] (q : R) (m : ℕ) :
    ∏ j ∈ Finset.range m, (q ^ (j + 1) - 1) =
      (-1 : R) ^ m * ∏ j ∈ Finset.range m, (1 - q * q ^ j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
      ring

/-- **The falling product of powers, denominator-free.**  Over every
commutative ring and for every `q`,

`∏_{i<n} (q^n - q^i) = q^{C(n,2)} · ∏_{j<n} (q^{j+1} - 1)`.

No hypothesis on `q` is used, so the identity holds at roots of unity, in
positive characteristic, and in the presence of zero divisors.  It is the
diagonal case `N = k = n` of `prod_pow_sub_pow_eq_finiteQPochhammerIn`,
after the alternating sign is absorbed into the Mersenne factors.

For a prime power `q` the left-hand side is the order of `GL_n` over the
field with `q` elements; see `FabiusGeneralLinearDenominator`. -/
theorem prod_pow_sub_pow_self_eq {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∏ i ∈ Finset.range n, (q ^ n - q ^ i) =
      q ^ n.choose 2 * ∏ j ∈ Finset.range n, (q ^ (j + 1) - 1) := by
  have h := prod_pow_sub_pow_eq_finiteQPochhammerIn q (le_refl n)
  rw [Nat.sub_self] at h
  simp only [Nat.zero_add, pow_one] at h
  rw [h, prod_pow_succ_sub_one_eq R q n, finiteQPochhammerIn]
  ring

/-! ## The prefactor -/

/-- **The formula's prefactor is a falling `2`-product.**  The denominator
`2^{n^2} (1/2; 1/2)_n` of the q-binomial--Thue--Morse formula equals
`∏_{i<n} (2^n - 2^i)`. -/
theorem two_pow_nat_sq_mul_halfQPochhammer_eq_prod (n : ℕ) :
    (2 : ℚ) ^ (n ^ 2) * halfQPochhammer n =
      ∏ i ∈ Finset.range n, ((2 : ℚ) ^ n - 2 ^ i) := by
  rw [two_pow_nat_sq_mul_halfQPochhammer, prod_pow_sub_pow_self_eq (2 : ℚ) n,
    halfMersenneProduct]

/-- The prefactor identity in the literal q-Pochhammer notation used by
`qBinomialThueMorseFormula`. -/
theorem two_pow_nat_sq_mul_qPochhammer_half_eq_prod (n : ℕ) :
    (2 : ℚ) ^ (n ^ 2) * qPochhammer (1 / 2) (1 / 2) n =
      ∏ i ∈ Finset.range n, ((2 : ℚ) ^ n - 2 ^ i) := by
  rw [qPochhammer_half_eq, two_pow_nat_sq_mul_halfQPochhammer_eq_prod]

/-! ## The summand -/

/-- **The exponent collapse.**  For `k ≤ n`,
`k(n-k) + k(k-1) + k = kn`, with `Nat` truncated subtraction throughout.
This is why the reciprocity factor `2^{k(n-k)}` and the formula's
`4^{C(k,2)} = 2^{k(k-1)}` merge into the single power `2^{kn}`. -/
theorem exponent_collapse {n k : ℕ} (hk : k ≤ n) :
    k * (n - k) + k * (k - 1) + k = k * n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]
  cases k with
  | zero => simp
  | succ j =>
      simp only [Nat.add_sub_cancel]
      ring

/-- The quotient q-binomial at base `1/2` is the polynomial Gaussian
binomial at base `2`, divided by the reciprocity monomial.  This is
`gaussianBinomial_reciprocity` at `q = 2`, oriented for rewriting. -/
theorem gaussianBinomial_half_eq_div (n k : ℕ) :
    gaussianBinomial (1 / 2 : ℚ) n k =
      gaussianBinomial (2 : ℚ) n k / 2 ^ (k * (n - k)) := by
  have h := gaussianBinomial_reciprocity (2 : ℚ) two_ne_zero n k
  rw [show ((2 : ℚ))⁻¹ = 1 / 2 by norm_num] at h
  rw [eq_div_iff (by positivity), mul_comm]
  exact h

/-- The outer numerator of the dyadic formula, written over the polynomial
Gaussian binomials at base `2`.  Compare `qBinomialThueMorseNumerator`,
which uses the quotient q-binomial at base `1/2` and the denominator
`4^{C(k,2)}`. -/
noncomputable def gaussianThueMorseNumerator (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    gaussianBinomial (2 : ℚ) n k * 2 ^ k /
        ((2 : ℚ) ^ (k * n) * ((n + k).factorial : ℚ)) *
      thueMorseCenteredPowerSum k (n + k)

/-- **Normalization of the numerator.**  Term by term,

`QBinomial[n,k,1/2] / (4^{C(k,2)} (n+k)!)
    = [n choose k]_2 · 2^k / (2^{kn} (n+k)!)`,

so the two numerators agree. -/
theorem gaussianThueMorseNumerator_eq (n : ℕ) :
    gaussianThueMorseNumerator n = qBinomialThueMorseNumerator n := by
  rw [gaussianThueMorseNumerator, qBinomialThueMorseNumerator]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  congr 1
  rw [qBinomial_half_eq, ← gaussianBinomial_half_eq_halfQBinomial,
    gaussianBinomial_half_eq_div, four_pow_choose_two]
  have hF : ((n + k).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpow : (2 : ℚ) ^ (k * n) =
      2 ^ (k * (n - k)) * 2 ^ (k * (k - 1)) * 2 ^ k := by
    rw [← pow_add, ← pow_add, exponent_collapse hkn]
  rw [hpow, div_div]
  refine div_eq_div_iff ?_ ?_ |>.mpr ?_
  · exact mul_ne_zero (by positivity) hF
  · exact mul_ne_zero (by positivity) (mul_ne_zero (by positivity) hF)
  · ring

/-! ## The identity in Gaussian form -/

/-- **The dyadic Fabius value in Gaussian-binomial form.**  For every `n`,

`F(2^{-n}) = (∏_{i<n} (2^n - 2^i))^{-1}
    · ∑_{k ≤ n} [n choose k]_2 · 2^k / (2^{kn} (n+k)!) · T_k(n+k)`.

Neither side mentions the base `1/2`: the prefactor is a falling
`2`-product and every Gaussian binomial `[n choose k]_2` is an integer. -/
theorem fabiusAtInverseTwoPow_eq_gaussian_div_prod (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (∏ i ∈ Finset.range n, ((2 : ℚ) ^ n - 2 ^ i))⁻¹ *
        gaussianThueMorseNumerator n := by
  rw [fabiusAtInverseTwoPow_eq_qBinomialThueMorseFormula,
    qBinomialThueMorseFormula, ← gaussianThueMorseNumerator_eq,
    two_pow_nat_sq_mul_qPochhammer_half_eq_prod, one_div]

/-- The Gaussian form with both finite sums displayed literally. -/
theorem fabiusAtInverseTwoPow_eq_gaussian_sum (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (∏ i ∈ Finset.range n, ((2 : ℚ) ^ n - 2 ^ i))⁻¹ *
        ∑ k ∈ Finset.range (n + 1),
          gaussianBinomial (2 : ℚ) n k * 2 ^ k /
              ((2 : ℚ) ^ (k * n) * ((n + k).factorial : ℚ)) *
            ∑ r ∈ Finset.range (2 ^ k),
              (thueMorseSign r : ℚ) *
                ((r : ℚ) - (2 : ℚ) ^ k) ^ (n + k) := by
  rw [fabiusAtInverseTwoPow_eq_gaussian_div_prod, gaussianThueMorseNumerator]
  simp only [thueMorseCenteredPowerSum_eq_sum_range]

/-- Real-valued Gaussian form for any bounded function satisfying the
Fabius characterization. -/
theorem fabiusFunction_inverse_two_pow_eq_gaussian_div_prod
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      (((∏ i ∈ Finset.range n, ((2 : ℚ) ^ n - 2 ^ i))⁻¹ *
        gaussianThueMorseNumerator n : ℚ) : ℝ) := by
  rw [fabiusFunction_inverse_two_pow_eq_qBinomialThueMorseFormula F hF n,
    qBinomialThueMorseFormula, ← gaussianThueMorseNumerator_eq,
    two_pow_nat_sq_mul_qPochhammer_half_eq_prod, one_div]

/-- The real-valued Gaussian form for the canonical Fabius function. -/
theorem fabius_inverse_two_pow_eq_gaussian_div_prod (n : ℕ) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      (((∏ i ∈ Finset.range n, ((2 : ℚ) ^ n - 2 ^ i))⁻¹ *
        gaussianThueMorseNumerator n : ℚ) : ℝ) :=
  fabiusFunction_inverse_two_pow_eq_gaussian_div_prod fabius fabius_spec n

end Fabius
