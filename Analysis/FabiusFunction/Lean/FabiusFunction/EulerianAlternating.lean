import FabiusFunction.EulerianEGF
import FabiusFunction.BernoulliStirling

/-!
# The alternating row sums of the Eulerian numbers

`∑_k (-1)^k A(n,k) = A_n(-1) = 2^{n+1} (2^{n+1} - 1) B_{n+1}/(n+1)` for `n ≥ 1`.

Evaluating the Eulerian exponential generating function at `t = -1` gives
`E(x) (1 + e^{-2x}) = 2` for `E(x) = ∑_n A_n(-1) x^n/n!`, i.e. `E = 1 + tanh x`,
and `x tanh x = x - (B(2x) - B(4x))` with `B(t) = t/(e^t - 1)` the Bernoulli
generating function; comparing coefficients gives the formula.

## Main results

* `egfA_eulerianPolynomial_eval_neg_one_mul`: `E(x) (1 + e^{-2x}) = 2`.
* `X_mul_egfA_eulerianPolynomial_eval_neg_one`: `x E(x) = 2x - B(2x) + B(4x)`.
* `sum_neg_one_pow_mul_eulerianNumber`: the alternating row sum.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- `rescale a (e^t) = e^{at}`. -/
theorem rescale_exp_eq_expSeries (a : ℚ) : rescale a (exp ℚ) = expSeries ℚ a := by
  ext n
  rw [coeff_rescale, coeff_exp, expSeries, coeff_egfA]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- `e^{at}` has constant term one, hence is a unit. -/
theorem isUnit_expSeries (a : ℚ) : IsUnit (expSeries ℚ a) := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, expSeries, coeff_egfA]
  simp

/-- The Eulerian generating function evaluated at `t = -1`:
`(∑_n A_n(-1) x^n/n!) (1 + e^{-2x}) = 2`. -/
theorem egfA_eulerianPolynomial_eval_neg_one_mul :
    egfA ℚ (fun n => (eulerianPolynomial ℚ n).eval (-1)) * (1 + expSeries ℚ (-2)) = 2 := by
  have h := congrArg (PowerSeries.map (Polynomial.evalRingHom (-1 : ℚ)))
    egfA_eulerianPolynomial_mul
  rw [map_mul, map_sub, PowerSeries.map_C, PowerSeries.map_C] at h
  have hE : PowerSeries.map (Polynomial.evalRingHom (-1 : ℚ))
      (egfA (Polynomial ℚ) fun n => eulerianPolynomial ℚ n)
      = egfA ℚ (fun n => (eulerianPolynomial ℚ n).eval (-1)) := by
    ext n
    rw [coeff_map, coeff_egfA, coeff_egfA, Polynomial.coe_evalRingHom, Polynomial.eval_mul,
      Polynomial.algebraMap_eq, Polynomial.eval_C, Algebra.algebraMap_self, RingHom.id_apply]
  have hexp : PowerSeries.map (Polynomial.evalRingHom (-1 : ℚ))
      (expSeries (Polynomial ℚ) (Polynomial.X - 1)) = expSeries ℚ (-2) := by
    ext n
    rw [coeff_map, expSeries, expSeries, coeff_egfA, coeff_egfA, Polynomial.coe_evalRingHom,
      Polynomial.eval_mul, Polynomial.algebraMap_eq, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, Algebra.algebraMap_self,
      RingHom.id_apply]
    norm_num
  rw [hE, hexp, Polynomial.coe_evalRingHom, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one] at h
  have h' : egfA ℚ (fun n => (eulerianPolynomial ℚ n).eval (-1)) * (1 + expSeries ℚ (-2))
      = -(egfA ℚ (fun n => (eulerianPolynomial ℚ n).eval (-1)) *
          (PowerSeries.C (-1 : ℚ) - expSeries ℚ (-2))) := by
    rw [map_neg, map_one]
    ring
  rw [h', h, show (-1 : ℚ) - 1 = -2 by norm_num, map_neg, map_ofNat, neg_neg]

/-- `B(4t)(e^{2t} + 1) = 2 B(2t)`, from `B(4t)(e^{4t} - 1) = 4t` and `B(2t)(e^{2t} - 1) = 2t`. -/
theorem rescale_four_bernoulli_mul :
    rescale (4 : ℚ) (bernoulliPowerSeries ℚ) * (expSeries ℚ 2 + 1) =
      2 * rescale (2 : ℚ) (bernoulliPowerSeries ℚ) := by
  have h1 := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h2 : rescale (2 : ℚ) (bernoulliPowerSeries ℚ) * (expSeries ℚ 2 - 1) = 2 * X := by
    have h := congrArg (rescale (2 : ℚ)) h1
    rw [map_mul, map_sub, map_one, rescale_X, rescale_exp_eq_expSeries, map_ofNat] at h
    exact h
  have h4 : rescale (4 : ℚ) (bernoulliPowerSeries ℚ) * (expSeries ℚ 4 - 1) = 4 * X := by
    have h := congrArg (rescale (4 : ℚ)) h1
    rw [map_mul, map_sub, map_one, rescale_X, rescale_exp_eq_expSeries, map_ofNat] at h
    exact h
  have he4 : expSeries ℚ 4 = expSeries ℚ 2 * expSeries ℚ 2 := by
    rw [expSeries_mul]
    norm_num
  -- `(e^{2t} - 1) = 2t · u` with `u` a unit
  have hu : X * (2 * rescale (2 : ℚ) (expSubOneDiv ℚ)) = expSeries ℚ 2 - 1 := by
    have h := congrArg (rescale (2 : ℚ)) (X_mul_expSubOneDiv ℚ)
    rw [map_mul, map_sub, map_one, rescale_X, rescale_exp_eq_expSeries, map_ofNat] at h
    rw [← h]
    ring
  have hunit : IsUnit (2 * rescale (2 : ℚ) (expSubOneDiv ℚ)) := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, ← map_ofNat
      (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2, coeff_C_mul, coeff_rescale, expSubOneDiv, coeff_mk]
    norm_num
  have h0 : (rescale (4 : ℚ) (bernoulliPowerSeries ℚ) * (expSeries ℚ 2 + 1) -
      2 * rescale (2 : ℚ) (bernoulliPowerSeries ℚ)) * (expSeries ℚ 2 - 1) = 0 := by
    rw [he4] at h4
    linear_combination h4 - 2 * h2
  rw [← hu, show (rescale (4 : ℚ) (bernoulliPowerSeries ℚ) * (expSeries ℚ 2 + 1) -
      2 * rescale (2 : ℚ) (bernoulliPowerSeries ℚ)) * (X * (2 * rescale (2 : ℚ) (expSubOneDiv ℚ)))
      = X * ((rescale (4 : ℚ) (bernoulliPowerSeries ℚ) * (expSeries ℚ 2 + 1) -
          2 * rescale (2 : ℚ) (bernoulliPowerSeries ℚ)) * (2 * rescale (2 : ℚ) (expSubOneDiv ℚ)))
      by ring] at h0
  have h5 := eq_zero_of_X_mul_eq_zero ℚ h0
  rw [hunit.mul_left_eq_zero] at h5
  exact sub_eq_zero.mp h5

/-- `x E(x) = 2x - B(2x) + B(4x)`, i.e. `x tanh x = x - B(2x) + B(4x)`. -/
theorem X_mul_egfA_eulerianPolynomial_eval_neg_one :
    X * egfA ℚ (fun n => (eulerianPolynomial ℚ n).eval (-1)) =
      2 * X - rescale (2 : ℚ) (bernoulliPowerSeries ℚ) + rescale (4 : ℚ) (bernoulliPowerSeries ℚ) := by
  have hE := egfA_eulerianPolynomial_eval_neg_one_mul
  have hK := rescale_four_bernoulli_mul
  have h2 : rescale (2 : ℚ) (bernoulliPowerSeries ℚ) * (expSeries ℚ 2 - 1) = 2 * X := by
    have h := congrArg (rescale (2 : ℚ)) (bernoulliPowerSeries_mul_exp_sub_one ℚ)
    rw [map_mul, map_sub, map_one, rescale_X, rescale_exp_eq_expSeries, map_ofNat] at h
    exact h
  have hee : expSeries ℚ (-2) * expSeries ℚ 2 = 1 := by
    rw [expSeries_mul, show (-2 : ℚ) + 2 = 0 by norm_num, expSeries_zero]
  -- `(2x - B(2x) + B(4x)) (1 + e^{-2x}) e^{2x} = 2x e^{2x}`
  have hM : (2 * X - rescale (2 : ℚ) (bernoulliPowerSeries ℚ) +
      rescale (4 : ℚ) (bernoulliPowerSeries ℚ)) * (1 + expSeries ℚ (-2)) * expSeries ℚ 2
      = 2 * X * expSeries ℚ 2 := by
    linear_combination (2 * X - rescale (2 : ℚ) (bernoulliPowerSeries ℚ) +
      rescale (4 : ℚ) (bernoulliPowerSeries ℚ)) * hee + hK - h2
  have hunit2 := isUnit_expSeries 2
  have hM' : (2 * X - rescale (2 : ℚ) (bernoulliPowerSeries ℚ) +
      rescale (4 : ℚ) (bernoulliPowerSeries ℚ)) * (1 + expSeries ℚ (-2)) = 2 * X :=
    hunit2.mul_right_cancel hM
  have hunit1 : IsUnit (1 + expSeries ℚ (-2)) := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, map_add,
      PowerSeries.coeff_one, expSeries, coeff_egfA]
    simp
  apply hunit1.mul_right_cancel
  rw [hM', mul_assoc, hE, mul_comm]

/-- **The alternating row sums of the Eulerian numbers:**
`∑_k (-1)^k A(n,k) = 2^{n+1} (2^{n+1} - 1) B_{n+1}/(n+1)` for `n ≥ 1`. -/
theorem sum_neg_one_pow_mul_eulerianNumber (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * eulerianNumber n k =
      2 ^ (n + 1) * (2 ^ (n + 1) - 1) * bernoulli (n + 1) / (n + 1) := by
  have h := congrArg (coeff (n + 1)) X_mul_egfA_eulerianPolynomial_eval_neg_one
  rw [coeff_succ_X_mul, coeff_egfA, map_add, map_sub, coeff_rescale, coeff_rescale,
    bernoulliPowerSeries, coeff_mk, ← map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2, coeff_C_mul,
    coeff_X, if_neg (by omega), mul_zero, zero_sub] at h
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  have heval : (eulerianPolynomial ℚ n).eval (-1) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * eulerianNumber n k := by
    rw [eulerianPolynomial, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X,
      mul_comm]
  rw [heval] at h
  have hn' : (n.factorial : ℚ) ≠ 0 := by positivity
  have hn1 : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
  have hfac : ((n + 1).factorial : ℚ) = (n + 1) * n.factorial := by
    push_cast [Nat.factorial_succ]
    ring
  rw [hfac] at h
  have h4 : (4 : ℚ) ^ (n + 1) = 2 ^ (n + 1) * 2 ^ (n + 1) := by
    rw [← mul_pow]
    norm_num
  rw [eq_div_iff (by positivity : ((n : ℚ) + 1) ≠ 0)]
  field_simp at h
  rw [h4] at h
  linear_combination h
end Fabius
