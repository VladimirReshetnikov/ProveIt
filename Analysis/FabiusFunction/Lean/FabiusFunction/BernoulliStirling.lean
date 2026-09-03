import Mathlib.NumberTheory.Bernoulli
import FabiusFunction.BellComposition

/-!
# Bernoulli numbers through Stirling numbers of the second kind

The generating function `t/(e^t - 1)` of the Bernoulli numbers equals
`log(1+u)/u` evaluated at `u = e^t - 1`, because `log(1 + (e^t - 1)) = t`.
Since `log(1+u)/u = ∑_k (-1)^k u^k/(k+1)` and `(e^t-1)^k/k!` is the column
generating function of the Stirling numbers of the second kind, the
exponential composition theorem gives the classical formula

`B_n = ∑_{k ≤ n} (-1)^k k!/(k+1) · S(n,k)`,

for Mathlib's Bernoulli numbers `bernoulli` (with `B_1 = -1/2`).

## Main results

* `expSubOneDiv`, `X_mul_expSubOneDiv`, `isUnit_expSubOneDiv`: the unit
  `(e^t - 1)/t`.
* `logDivSeries`, `X_mul_logDivSeries`: the series `log(1+u)/u`.
* `bernoulliPowerSeries_eq_logDivSeries_subst`: the Bernoulli generating
  function is `log(1+u)/u` at `u = e^t - 1`.
* `partialBell_one_cast`, `bernoulli_eq_sum_stirlingSecond`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The series `(e^t - 1)/t = ∑_n t^n/(n+1)!`. -/
noncomputable def expSubOneDiv : A⟦X⟧ :=
  PowerSeries.mk fun n => algebraMap ℚ A (1 / (n + 1).factorial)

/-- `t · (e^t - 1)/t = e^t - 1`. -/
theorem X_mul_expSubOneDiv : X * expSubOneDiv A = exp A - 1 := by
  ext n
  rw [map_sub, coeff_exp, coeff_one]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, expSubOneDiv, coeff_mk, if_neg (Nat.succ_ne_zero n), sub_zero]

/-- `(e^t - 1)/t` is a unit (its constant term is one). -/
theorem isUnit_expSubOneDiv : IsUnit (expSubOneDiv A) := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, expSubOneDiv, coeff_mk]
  simp

/-- The series `log(1+u)/u = ∑_k (-1)^k u^k/(k+1)`, written as an exponential
generating function with coefficients `(-1)^k k!/(k+1)`. -/
noncomputable def logDivSeries : A⟦X⟧ :=
  egfA A fun k => algebraMap ℚ A ((-1 : ℚ) ^ k * k.factorial / (k + 1))

/-- `u · log(1+u)/u = log(1+u)`. -/
theorem X_mul_logDivSeries : X * logDivSeries A = log A := by
  ext n
  rw [coeff_log]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, logDivSeries, coeff_egfA, if_neg (Nat.succ_ne_zero n), ← map_mul]
    congr 1
    push_cast
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    ring

/-- `X · f = 0` forces `f = 0` in a power-series ring. -/
theorem eq_zero_of_X_mul_eq_zero {f : A⟦X⟧} (h : X * f = 0) : f = 0 := by
  ext n
  have := congrArg (coeff (n + 1)) h
  rwa [coeff_succ_X_mul, map_zero] at this

/-- **The Bernoulli generating function is `log(1+u)/u` at `u = e^t - 1`.** -/
theorem bernoulliPowerSeries_eq_logDivSeries_subst :
    bernoulliPowerSeries A = (logDivSeries A).subst (exp A - 1) := by
  have hE : HasSubst (exp A - 1) := HasSubst.exp_sub_one
  have h1 : (exp A - 1) * (logDivSeries A).subst (exp A - 1) = X := by
    have h := log_subst_exp_sub_one A
    rw [← X_mul_logDivSeries, subst_mul hE, subst_X hE] at h
    exact h
  have h2 : (exp A - 1) * bernoulliPowerSeries A = X := by
    rw [mul_comm]
    exact bernoulliPowerSeries_mul_exp_sub_one A
  have h3 : X * (expSubOneDiv A * (bernoulliPowerSeries A - (logDivSeries A).subst (exp A - 1)))
      = 0 := by
    rw [← mul_assoc, X_mul_expSubOneDiv, mul_sub, h1, h2, sub_self]
  have h4 := eq_zero_of_X_mul_eq_zero A h3
  rw [(isUnit_expSubOneDiv A).mul_right_eq_zero] at h4
  exact sub_eq_zero.mp h4

end

/-- `B_{n,k}(1,1,…) = S(n,k)` in every commutative semiring. -/
theorem partialBell_one_cast (R : Type*) [CommSemiring R] (n k : ℕ) :
    partialBell (fun _ => (1 : R)) n k = Nat.stirlingSecond n k := by
  have h := map_partialBell (Nat.castRingHom R) (fun _ => (1 : ℕ)) n k
  simp only [Nat.coe_castRingHom, Nat.cast_one] at h
  rw [← h, partialBell_one]

/-- **Bernoulli numbers through Stirling numbers of the second kind:**
`B_n = ∑_{k ≤ n} (-1)^k k!/(k+1) · S(n,k)`. -/
theorem bernoulli_eq_sum_stirlingSecond (n : ℕ) :
    bernoulli n = ∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * k.factorial / (k + 1) * Nat.stirlingSecond n k := by
  have h := congrArg (coeff n) (bernoulliPowerSeries_eq_logDivSeries_subst ℚ)
  rw [bernoulliPowerSeries, coeff_mk, logDivSeries, ← bellWeightSeries_one,
    egfA_subst_bellWeightSeries, coeff_egfA] at h
  simp only [Algebra.algebraMap_self, RingHom.id_apply, partialBell_one_cast] at h
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have e1 : (n.factorial : ℚ) * (bernoulli n / n.factorial) = bernoulli n := by
    field_simp
  calc bernoulli n = (n.factorial : ℚ) * (bernoulli n / n.factorial) := e1.symm
    _ = (n.factorial : ℚ) * (1 / (n.factorial : ℚ) *
          ∑ k ∈ Finset.range (n + 1),
            (-1 : ℚ) ^ k * k.factorial / (k + 1) * Nat.stirlingSecond n k) := by rw [h]
    _ = _ := by rw [← mul_assoc, mul_one_div_cancel hn, one_mul]

end Fabius
