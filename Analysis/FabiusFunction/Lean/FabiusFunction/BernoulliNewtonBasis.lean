import FabiusFunction.BernoulliStirling
import FabiusFunction.StirlingGeneratingFunctions
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Bernoulli polynomials in the Newton basis

The Gregory composition `t/(e^t - 1) = ∑_k (-1)^k/(k+1) (e^t - 1)^k`, multiplied by `e^{xt}` and
read off coefficientwise, expresses the Bernoulli polynomials through iterated forward differences:

`β_n(x) = ∑_{k ≤ n} (-1)^k/(k+1) Δ^k x^n`,  `Δ^k x^n = ∑_{j ≤ k} (-1)^{k-j} C(k,j) (x+j)^n`.

The infinite composition is only ever used modulo `t^{n+1}`, where it is a finite sum
(`X_pow_dvd_bernoulliPowerSeries_sub_gregory`); the coefficients of that truncation are compared
through the Bernoulli–Stirling formula `bernoulli_eq_sum_stirlingSecond`.

## Main results

* `gregoryTrunc`, `coeff_gregoryTrunc`, `X_pow_dvd_bernoulliPowerSeries_sub_gregory`.
* `bernoulliPolySeries`, `bernoulliPolySeries_eq`, `rescale_exp_mul_exp_sub_one_pow`.
* `bernoulli_eq_sum_fwdDiff`, `bernoulli_eq_sum_fwdDiff_zero`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Gregory

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The truncated Gregory series `∑_{k ≤ n} (-1)^k/(k+1) (e^t - 1)^k`. -/
noncomputable def gregoryTrunc (n : ℕ) : A⟦X⟧ :=
  ∑ k ∈ range (n + 1),
    PowerSeries.C (algebraMap ℚ A ((-1) ^ k / (k + 1))) * (exp A - 1) ^ k

/-- The coefficients of the truncated Gregory series through Stirling numbers. -/
theorem coeff_gregoryTrunc (n m : ℕ) :
    coeff m (gregoryTrunc A n) =
      algebraMap ℚ A (∑ k ∈ range (n + 1),
        (-1) ^ k / (k + 1) * (k.factorial * Nat.stirlingSecond m k / m.factorial)) := by
  rw [gregoryTrunc, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul, exp_sub_one_pow, coeff_egf, ← map_mul]

/-- **The Gregory composition, truncated:** `t/(e^t-1) ≡ ∑_{k ≤ n} (-1)^k/(k+1) (e^t-1)^k`
modulo `t^{n+1}`. -/
theorem X_pow_dvd_bernoulliPowerSeries_sub_gregory (n : ℕ) :
    (X : A⟦X⟧) ^ (n + 1) ∣ bernoulliPowerSeries A - gregoryTrunc A n := by
  rw [X_pow_dvd_iff]
  intro m hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp hm
  have hq : (bernoulli m / m.factorial : ℚ) =
      ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k / ((k : ℚ) + 1) *
        ((k.factorial : ℚ) * (Nat.stirlingSecond m k : ℚ) / (m.factorial : ℚ)) := by
    have hzero : ∀ k ∈ range (n + 1), k ∉ range (m + 1) →
        (-1 : ℚ) ^ k / ((k : ℚ) + 1) *
          ((k.factorial : ℚ) * (Nat.stirlingSecond m k : ℚ) / (m.factorial : ℚ)) = 0 := by
      intro k _ hk
      rw [Finset.mem_range, not_lt] at hk
      rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, zero_div,
        mul_zero]
    rw [← Finset.sum_subset
        (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)) hzero,
      bernoulli_eq_sum_stirlingSecond, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [map_sub, bernoulliPowerSeries, coeff_mk, coeff_gregoryTrunc, hq, sub_self]

end Gregory

section Poly

/-- `∑_n β_n(x) t^n/n!` as a power series over `ℚ[x]`. -/
noncomputable def bernoulliPolySeries : (Polynomial ℚ)⟦X⟧ :=
  PowerSeries.mk fun n => (1 / n.factorial : ℚ) • Polynomial.bernoulli n

/-- The `n`th coefficient of `bernoulliPolySeries` is `bernoulli n / n!`. -/
theorem coeff_bernoulliPolySeries (n : ℕ) :
    coeff n bernoulliPolySeries = (1 / n.factorial : ℚ) • Polynomial.bernoulli n :=
  coeff_mk _ _

/-- `∑_n β_n(x) t^n/n! = e^{xt} · t/(e^t - 1)`. -/
theorem bernoulliPolySeries_eq :
    bernoulliPolySeries =
      rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ)) *
        bernoulliPowerSeries (Polynomial ℚ) := by
  have h1 := Polynomial.bernoulli_generating_function (Polynomial.X : Polynomial ℚ)
  simp only [Polynomial.aeval_X_left_apply] at h1
  change bernoulliPolySeries * _ = _ at h1
  have h2 := bernoulliPowerSeries_mul_exp_sub_one (Polynomial ℚ)
  have h3 : (exp (Polynomial ℚ) - 1) * (bernoulliPolySeries -
      rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ)) *
        bernoulliPowerSeries (Polynomial ℚ)) = 0 := by
    linear_combination h1 - rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ)) * h2
  rw [← X_mul_expSubOneDiv, mul_assoc] at h3
  have h4 := eq_zero_of_X_mul_eq_zero (Polynomial ℚ) h3
  rw [(isUnit_expSubOneDiv (Polynomial ℚ)).mul_right_eq_zero] at h4
  exact sub_eq_zero.mp h4

/-- `e^{xt} (e^t - 1)^k = ∑_j (-1)^{k-j} C(k,j) e^{(x+j)t}`. -/
theorem rescale_exp_mul_exp_sub_one_pow (k : ℕ) :
    rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ)) * (exp (Polynomial ℚ) - 1) ^ k =
      ∑ j ∈ range (k + 1),
        PowerSeries.C (Polynomial.C ((-1 : ℚ) ^ (k - j) * k.choose j)) *
          rescale (Polynomial.X + (j : Polynomial ℚ)) (exp (Polynomial ℚ)) := by
  rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : ((-1 : (Polynomial ℚ)⟦X⟧) ^ (k - j) * (k.choose j : (Polynomial ℚ)⟦X⟧)) =
      PowerSeries.C (Polynomial.C ((-1 : ℚ) ^ (k - j) * k.choose j)) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [exp_pow_eq_rescale_exp, ← hc, mul_assoc, mul_assoc, ← mul_assoc _ (rescale _ _),
    exp_mul_exp_eq_exp_add]
  ring

/-- **Bernoulli polynomials in the Newton basis:**
`β_n(x) = ∑_{k ≤ n} (-1)^k/(k+1) Δ^k x^n` with `Δ^k x^n = ∑_{j ≤ k} (-1)^{k-j} C(k,j) (x+j)^n`. -/
theorem bernoulli_eq_sum_fwdDiff (n : ℕ) :
    Polynomial.bernoulli n =
      ∑ k ∈ range (n + 1), Polynomial.C ((-1 : ℚ) ^ k / (k + 1)) *
        ∑ j ∈ range (k + 1), Polynomial.C ((-1 : ℚ) ^ (k - j) * k.choose j) *
          (Polynomial.X + (j : Polynomial ℚ)) ^ n := by
  have hdvd := X_pow_dvd_bernoulliPowerSeries_sub_gregory (Polynomial ℚ) n
  have hcoeff : coeff n bernoulliPolySeries =
      coeff n (rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ)) *
        gregoryTrunc (Polynomial ℚ) n) := by
    have h0 := (X_pow_dvd_iff.mp (dvd_mul_of_dvd_right hdvd
      (rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ))))) n (Nat.lt_succ_self n)
    rw [bernoulliPolySeries_eq, ← sub_eq_zero, ← map_sub, ← mul_sub]
    exact h0
  have hterm : ∀ k : ℕ, coeff n (rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ)) *
      (PowerSeries.C (algebraMap ℚ (Polynomial ℚ) ((-1) ^ k / (k + 1))) *
        (exp (Polynomial ℚ) - 1) ^ k)) =
      Polynomial.C ((-1 : ℚ) ^ k / (k + 1)) * ∑ j ∈ range (k + 1),
        Polynomial.C ((-1 : ℚ) ^ (k - j) * k.choose j) *
          ((Polynomial.X + (j : Polynomial ℚ)) ^ n * Polynomial.C (1 / n.factorial : ℚ)) := by
    intro k
    rw [mul_left_comm, coeff_C_mul, rescale_exp_mul_exp_sub_one_pow, map_sum,
      Polynomial.algebraMap_eq]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_C_mul, coeff_rescale, coeff_exp, Polynomial.algebraMap_eq]
  rw [coeff_bernoulliPolySeries, gregoryTrunc, Finset.mul_sum, map_sum] at hcoeff
  simp only [hterm] at hcoeff
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have key : Polynomial.C (1 / n.factorial : ℚ) * Polynomial.bernoulli n =
      Polynomial.C (1 / n.factorial : ℚ) *
        ∑ k ∈ range (n + 1), Polynomial.C ((-1 : ℚ) ^ k / (k + 1)) *
          ∑ j ∈ range (k + 1), Polynomial.C ((-1 : ℚ) ^ (k - j) * k.choose j) *
            (Polynomial.X + (j : Polynomial ℚ)) ^ n := by
    rw [← Polynomial.smul_eq_C_mul, hcoeff]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  exact mul_left_cancel₀ (Polynomial.C_ne_zero.mpr (one_div_ne_zero hn)) key

/-- **The value at `x = 0`:** `B_n = ∑_{k ≤ n} (-1)^k/(k+1) Δ^k 0^n`. -/
theorem bernoulli_eq_sum_fwdDiff_zero (n : ℕ) :
    bernoulli n = ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k / (k + 1) *
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ (k - j) * k.choose j * (j : ℚ) ^ n := by
  have h := congrArg (Polynomial.eval (0 : ℚ)) (bernoulli_eq_sum_fwdDiff n)
  rw [Polynomial.bernoulli_eval_zero] at h
  rw [h]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast,
    zero_add]

end Poly

end Fabius
