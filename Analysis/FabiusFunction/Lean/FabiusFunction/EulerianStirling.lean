import FabiusFunction.EulerianGeneratingFunctions
import FabiusFunction.StirlingBasisChange

/-!
# Eulerian polynomials through Stirling numbers of the second kind

`A_n(t) = ∑_{k ≤ n} S(n,k) k! (t - 1)^{n-k}`.

The rational generating function `∑_m (m+1)^n t^m = A_n(t)/(1-t)^{n+1}` is
combined with the rising-factorial expansion
`x^n = ∑_k (-1)^{n-k} S(n,k) x^{\overline k}` and
`∑_m (m+1)^{\overline k} t^m = k!/(1-t)^{k+1}`.

## Main results

* `succ_pow_eq_sum_stirlingSecond_mul_choose`, `succPowSeries_eq_sum_stirlingSecond`.
* `sum_eulerianNumber_mul_X_pow_eq_sum_stirlingSecond`: the identity in `R⟦X⟧`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

variable (R : Type*) [CommRing R]

/-- `(m+1)^n = ∑_{k ≤ n} (-1)^{n-k} S(n,k) · k! · C(m+k, k)`: the rising-factorial
expansion evaluated at `m + 1`. -/
theorem succ_pow_eq_sum_stirlingSecond_mul_choose (n m : ℕ) :
    ((m + 1 : ℕ) : R) ^ n = ∑ k ∈ Finset.range (n + 1),
      (-1 : R) ^ (n - k) * (Nat.stirlingSecond n k : R) *
        ((k.factorial * (m + k).choose k : ℕ) : R) := by
  have h := congrArg (Polynomial.eval ((m + 1 : ℕ) : R))
    (X_pow_eq_sum_stirlingSecond_mul_ascPochhammer R n)
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_natCast,
    ascPochhammer_nat_eq_natCast_ascFactorial, Nat.ascFactorial_eq_factorial_mul_choose] at h
  exact h

/-- `∑_m (m+1)^n X^m = ∑_{k ≤ n} (-1)^{n-k} S(n,k) k! · (1 - X)^{-(k+1)}`. -/
theorem succPowSeries_eq_sum_stirlingSecond (n : ℕ) :
    succPowSeries R n = ∑ k ∈ Finset.range (n + 1),
      PowerSeries.C ((-1 : R) ^ (n - k) * ((Nat.stirlingSecond n k * k.factorial : ℕ) : R)) *
        PowerSeries.mk 1 ^ (k + 1) := by
  ext m
  rw [succPowSeries, coeff_mk, map_sum]
  have h := succ_pow_eq_sum_stirlingSecond_mul_choose R n m
  rw [Nat.cast_add_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul, mk_one_pow_eq_mk_choose_add, coeff_mk, Nat.add_comm k m]
  push_cast
  ring

/-- **Eulerian polynomials through Stirling numbers:**
`A_n(t) = ∑_{k ≤ n} S(n,k) k! (t - 1)^{n-k}`, as an identity in `R⟦X⟧` with
`A_n(X) = ∑_k A(n,k) X^k`. -/
theorem sum_eulerianNumber_mul_X_pow_eq_sum_stirlingSecond (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (eulerianNumber n k : R⟦X⟧) * X ^ k =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.C ((Nat.stirlingSecond n k * k.factorial : ℕ) : R) * (X - 1) ^ (n - k) := by
  rw [← one_sub_X_pow_mul_succPowSeries, succPowSeries_eq_sum_stirlingSecond, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsplit : ((1 : R⟦X⟧) - X) ^ (n + 1) = (1 - X) ^ (n - k) * (1 - X) ^ (k + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hunit : ((1 : R⟦X⟧) - X) ^ (k + 1) * PowerSeries.mk 1 ^ (k + 1) = 1 := by
    rw [← mul_pow, mul_comm, mk_one_mul_one_sub_eq_one, one_pow]
  have hsign : ((X : R⟦X⟧) - 1) ^ (n - k) = (-1) ^ (n - k) * (1 - X) ^ (n - k) := by
    rw [← neg_sub, neg_pow]
  rw [hsign, map_mul, map_pow, map_neg, map_one]
  calc (1 - X) ^ (n + 1) * ((-1) ^ (n - k) *
          PowerSeries.C ((Nat.stirlingSecond n k * k.factorial : ℕ) : R) * PowerSeries.mk 1 ^ (k + 1))
      = PowerSeries.C ((Nat.stirlingSecond n k * k.factorial : ℕ) : R) *
          ((-1) ^ (n - k) * (1 - X) ^ (n - k)) *
          ((1 - X) ^ (k + 1) * PowerSeries.mk 1 ^ (k + 1)) := by rw [hsplit]; ring
    _ = _ := by rw [hunit, mul_one]

end Fabius
