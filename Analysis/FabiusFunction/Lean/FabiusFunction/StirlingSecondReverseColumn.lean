import FabiusFunction.StirlingFirstReverse
import FabiusFunction.BinomialInversionEGF

/-!
# The reverse column recurrence of the second kind

`(n-k) S(n,k) = ∑_{j=2}^{n-k+1} (-1)^j C(n,j) S(n-j+1,k)`
(`second_reverse_column`), one of the two reverse recurrences the source states for the
second-kind numbers.

The argument is the one already used for the first kind in `StirlingFirstReverse`, with a
different kernel and a different differential equation.  The right-hand side is a binomial
convolution of the kernel `j ↦ (-1)^j` (restricted to `j ≥ 2`) with the shifted column
`m ↦ S(m+1,k)`, so its exponential generating function is the product of

`∑_{j ≥ 2} (-1)^j x^j/j! = e^{-x} - 1 + x`   (`egfA_altKernel`)

with `F_k'`, while the left-hand side has `x F_k' - k F_k`.  The two agree because

`(1 - e^{-x}) F_k' = k F_k`   (`one_sub_altSeries_mul_derivative_egfA_stirlingSecond`),

which is immediate from `F_k = (e^x-1)^k/k!` once `e^{-x} e^{x} = 1` is available; that is
`exp_mul_altSeries` from `BinomialInversionEGF`, where `e^{-x}` is the exponential generating
function of `(-1)^n`.

The differential equation is where the two kinds differ.  The first-kind column satisfies
`(1-x) log(1-x) F' = -k F`, whose kernel involves a logarithm; the second-kind column
satisfies the equation above, whose kernel is elementary.  That is why this module needs no
counterpart of `negLogOneSub`.

## Main results

* `egfA_stirlingSecond`, `one_sub_altSeries_mul_derivative_egfA_stirlingSecond`.
* `egfA_altKernel`, `egfA_second_reverse_column`.
* `second_reverse_column`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section SecondColumn

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- `F_k = ∑_n S(n,k) x^n/n! = (1/k!) (e^x - 1)^k`, as an `egfA`. -/
theorem egfA_stirlingSecond (k : ℕ) :
    egfA A (fun n => (Nat.stirlingSecond n k : A)) =
      PowerSeries.C (algebraMap ℚ A (1 / k.factorial)) * (exp A - 1) ^ k := by
  rw [← smul_eq_C_mul, ← egf_stirlingSecond, ← egfA_algebraMap]
  congr 1
  funext n
  rw [map_natCast]

/-- **The column differential equation:** `(1 - e^{-x}) F_{k+1}' = (k+1) F_{k+1}`. -/
theorem one_sub_altSeries_mul_derivative_egfA_stirlingSecond (k : ℕ) :
    (1 - altSeries A) * d⁄dX A (egfA A fun n => (Nat.stirlingSecond n (k + 1) : A)) =
      ((k + 1 : ℕ) : A⟦X⟧) * egfA A fun n => (Nat.stirlingSecond n (k + 1) : A) := by
  rw [egfA_stirlingSecond, Derivation.leibniz, derivative_C, smul_zero, add_zero,
    Derivation.leibniz_pow, Nat.add_sub_cancel, map_sub, Derivation.map_one_eq_zero, sub_zero,
    PowerSeries.derivative_exp]
  simp only [smul_eq_mul, nsmul_eq_mul]
  have hinv : altSeries A * exp A = 1 := by
    rw [mul_comm]
    exact exp_mul_altSeries A
  linear_combination (-(((k + 1 : ℕ) : A⟦X⟧) *
    PowerSeries.C (algebraMap ℚ A (1 / (k + 1).factorial)) * (exp A - 1) ^ k)) * hinv

/-- The kernel `∑_{j ≥ 2} (-1)^j x^j/j! = e^{-x} - 1 + x`. -/
theorem egfA_altKernel :
    egfA A (fun j => if 2 ≤ j then (-1 : A) ^ j else 0) = altSeries A - 1 + X := by
  ext n
  rw [coeff_egfA, map_add, map_sub, altSeries, coeff_egfA, PowerSeries.coeff_X]
  rcases n with _ | _ | m
  · rw [if_neg (by omega), mul_zero, coeff_one, if_pos rfl, if_neg (by omega), pow_zero,
      mul_one, Nat.factorial_zero, Nat.cast_one, div_one, map_one]
    ring
  · rw [if_neg (by omega), mul_zero, coeff_one, if_neg (by omega), if_pos rfl, pow_one]
    have h : algebraMap ℚ A (1 / (1 : ℕ).factorial) = 1 := by
      rw [Nat.factorial_one, Nat.cast_one, div_one, map_one]
    rw [h]
    ring
  · rw [if_pos (by omega), coeff_one, if_neg (by omega), if_neg (by omega)]
    ring

/-- The exponential generating function of the right-hand side. -/
theorem egfA_second_reverse_column_rhs (k : ℕ) :
    egfA A (Bell.binomialConv (fun j => if 2 ≤ j then (-1 : A) ^ j else 0)
        (fun m => (Nat.stirlingSecond (m + 1) k : A))) =
      (altSeries A - 1 + X) * d⁄dX A (egfA A fun n => (Nat.stirlingSecond n k : A)) := by
  rw [← egfA_mul, egfA_altKernel, derivative_egfA]
  rfl

/-- **The column identity, as exponential generating functions.** -/
theorem egfA_second_reverse_column (k : ℕ) :
    egfA A (fun n => ((n : A) - ((k + 1 : ℕ) : A)) * (Nat.stirlingSecond n (k + 1) : A)) =
      egfA A (Bell.binomialConv (fun j => if 2 ≤ j then (-1 : A) ^ j else 0)
        (fun m => (Nat.stirlingSecond (m + 1) (k + 1) : A))) := by
  rw [egfA_second_reverse_column_rhs]
  have hkey : (altSeries A - 1 + X) *
      d⁄dX A (egfA A fun n => (Nat.stirlingSecond n (k + 1) : A))
      = X * d⁄dX A (egfA A fun n => (Nat.stirlingSecond n (k + 1) : A))
        - ((k + 1 : ℕ) : A⟦X⟧) * egfA A fun n => (Nat.stirlingSecond n (k + 1) : A) := by
    have h := one_sub_altSeries_mul_derivative_egfA_stirlingSecond A k
    linear_combination -h
  rw [hkey, X_mul_derivative_egfA, natCast_mul_egfA, egfA_sub]
  congr 1
  funext n
  rw [Pi.sub_apply]
  ring

/-- **Reverse column recurrence of the second kind:**
`(n - k) S(n,k) = ∑_j (-1)^j C(n,j) S(n-j+1, k)`, where the terms with `j < 2` are dropped by
the kernel and those with `j > n-k+1` vanish because `S(n-j+1,k) = 0`. -/
theorem second_reverse_column (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n : ℚ) - k) * Nat.stirlingSecond n k =
      ∑ j ∈ range (n + 1), (n.choose j : ℚ) *
        ((if 2 ≤ j then (-1 : ℚ) ^ j else 0) * Nat.stirlingSecond (n - j + 1) k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h := congrFun (seq_eq_of_egfA_eq ℚ (egfA_second_reverse_column ℚ m)) n
  simp only [Bell.binomialConv_eq_sum_range] at h
  push_cast at h ⊢
  linear_combination h

end SecondColumn

end Fabius
