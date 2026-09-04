import FabiusFunction.NorlundPolynomials
import FabiusFunction.StirlingBasisChange
import FabiusFunction.ExponentialRescaling

/-!
# The Nörlund diagonal

The generating function `B = t/(e^t - 1)` satisfies the Riccati-type equation
`t B' = B - B² - t B` (`X_mul_derivative_bernoulliPowerSeries`), which turns into a one-step
relation between Nörlund polynomials of consecutive order,

`(a+1) β_{n+1}^{(a+2)}(x+1) = (a-n) β_{n+1}^{(a+1)}(x) + (n+1) x β_n^{(a+1)}(x)`

(`norlund_step`).  On the diagonal `a = n` the first term drops out, leaving
`β_{n+1}^{(n+2)}(x+1) = x β_n^{(n+1)}(x)` (`norlund_diagonal_step`), and induction gives the
closed form

`β_n^{(n+1)}(x) = (x-1)(x-2)⋯(x-n)`  (`norlund_diagonal`),

with the two numerical corollaries `β_n^{(n+1)}(0) = (-1)^n n!` (`norlund_eval_zero_diagonal`)
and `[t^n] (t/(e^t-1))^{n+1} = (-1)^n` (`coeff_bernoulliPowerSeries_pow_succ`).

## Main results

* `derivative_rescale_exp`, `rescale_zero_exp`, `rescale_exp_add_one`,
  `X_mul_derivative_bernoulliPowerSeries`.
* `ascPochhammer_eval_one`, `descPochhammer_eval_neg_one`.
* `norlund_series_step`, `norlund_step`, `norlund_diagonal_step`.
* `norlund_diagonal`, `norlund_eval_zero_diagonal`, `coeff_bernoulliPowerSeries_pow_succ`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-! ### Two small evaluations -/

/-- `1 · 2 ⋯ k = k!`. -/
theorem ascPochhammer_eval_one (k : ℕ) : (ascPochhammer ℚ k).eval 1 = k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, ih, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_natCast, Nat.factorial_succ]
    push_cast
    ring

/-- `(-1)(-2)⋯(-n) = (-1)^n n!`. -/
theorem descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer ℚ n).eval (-1) = (-1) ^ n * n.factorial := by
  have h := congrArg (fun p : Polynomial ℚ => p.eval 1) (descPochhammer_comp_neg_X (R := ℚ) n)
  simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_one] at h
  rw [h, ascPochhammer_eval_one]

/-! ### The exponential and the Bernoulli generating function -/

/-- **The Riccati equation for `B = t/(e^t-1)`:** `t B' = B - B² - t B`. -/
theorem X_mul_derivative_bernoulliPowerSeries :
    X * d⁄dX ℚ (bernoulliPowerSeries ℚ) =
      bernoulliPowerSeries ℚ - bernoulliPowerSeries ℚ ^ 2 - X * bernoulliPowerSeries ℚ := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hd := congrArg (d⁄dX ℚ) hB
  rw [Derivation.leibniz, map_sub, PowerSeries.derivative_exp, Derivation.map_one_eq_zero,
    sub_zero, smul_eq_mul, smul_eq_mul, derivative_X] at hd
  linear_combination (bernoulliPowerSeries ℚ) * hd -
    (d⁄dX ℚ (bernoulliPowerSeries ℚ) + bernoulliPowerSeries ℚ) * hB

/-! ### Order lowering and the diagonal -/

/-- The generating-function form of the order-lowering relation. -/
theorem norlund_series_step (a : ℕ) (x : ℚ) :
    PowerSeries.C ((a : ℚ) + 1) * (bernoulliPowerSeries ℚ ^ (a + 2) * rescale (x + 1) (exp ℚ)) =
      PowerSeries.C ((a : ℚ) + 1) * (bernoulliPowerSeries ℚ ^ (a + 1) * rescale x (exp ℚ))
        - X * d⁄dX ℚ (bernoulliPowerSeries ℚ ^ (a + 1) * rescale x (exp ℚ))
        + PowerSeries.C x * (X * (bernoulliPowerSeries ℚ ^ (a + 1) * rescale x (exp ℚ))) := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hR := X_mul_derivative_bernoulliPowerSeries
  have hE := derivative_rescale_exp x
  have hA := rescale_exp_add_one x
  have hL : d⁄dX ℚ (bernoulliPowerSeries ℚ ^ (a + 1) * rescale x (exp ℚ)) =
      bernoulliPowerSeries ℚ ^ (a + 1) * d⁄dX ℚ (rescale x (exp ℚ)) +
        rescale x (exp ℚ) * (PowerSeries.C ((a : ℚ) + 1) *
          (bernoulliPowerSeries ℚ ^ a * d⁄dX ℚ (bernoulliPowerSeries ℚ))) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel]
    simp only [smul_eq_mul, nsmul_eq_mul]
    rw [← map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) (a + 1)]
    push_cast
    ring
  rw [hL, hE, hA, pow_succ (bernoulliPowerSeries ℚ) (a + 1), pow_succ (bernoulliPowerSeries ℚ) a]
  linear_combination (PowerSeries.C ((a : ℚ) + 1) * bernoulliPowerSeries ℚ ^ a *
      bernoulliPowerSeries ℚ * rescale x (exp ℚ)) * hB +
    (PowerSeries.C ((a : ℚ) + 1) * bernoulliPowerSeries ℚ ^ a * rescale x (exp ℚ)) * hR

/-- The Nörlund polynomial as a scaled coefficient. -/
theorem norlund_eval_eq_factorial_mul_coeff (b m : ℕ) (y : ℚ) :
    (norlund b m).eval y =
      (m.factorial : ℚ) * coeff m (bernoulliPowerSeries ℚ ^ b * rescale y (exp ℚ)) := by
  have h := congrArg (coeff m) (egfA_norlund_eval b y)
  rw [coeff_egfA, Algebra.algebraMap_self, RingHom.id_apply] at h
  have hf : (m.factorial : ℚ) ≠ 0 := by positivity
  rw [← h]
  field_simp

/-- **Order lowering:**
`(a+1) β_{n+1}^{(a+2)}(x+1) = (a-n) β_{n+1}^{(a+1)}(x) + (n+1) x β_n^{(a+1)}(x)`. -/
theorem norlund_step (a n : ℕ) (x : ℚ) :
    ((a : ℚ) + 1) * (norlund (a + 2) (n + 1)).eval (x + 1) =
      ((a : ℚ) - n) * (norlund (a + 1) (n + 1)).eval x +
        ((n : ℚ) + 1) * x * (norlund (a + 1) n).eval x := by
  have hS := congrArg (coeff (n + 1)) (norlund_series_step a x)
  rw [coeff_C_mul, map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_derivative,
    coeff_C_mul, coeff_succ_X_mul] at hS
  rw [norlund_eval_eq_factorial_mul_coeff, norlund_eval_eq_factorial_mul_coeff,
    norlund_eval_eq_factorial_mul_coeff, Nat.factorial_succ]
  push_cast
  linear_combination (((n : ℚ) + 1) * (n.factorial : ℚ)) * hS

/-- **The diagonal step:** `β_{n+1}^{(n+2)}(x+1) = x β_n^{(n+1)}(x)`. -/
theorem norlund_diagonal_step (n : ℕ) (x : ℚ) :
    (norlund (n + 2) (n + 1)).eval (x + 1) = x * (norlund (n + 1) n).eval x := by
  have h := norlund_step n n x
  rw [sub_self, zero_mul, zero_add] at h
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  rw [h]
  ring

/-- **The Nörlund diagonal:** `β_n^{(n+1)}(x) = (x-1)(x-2)⋯(x-n)`. -/
theorem norlund_diagonal (n : ℕ) (x : ℚ) :
    (norlund (n + 1) n).eval x = (descPochhammer ℚ n).eval (x - 1) := by
  induction n generalizing x with
  | zero => simp [norlund_one, Polynomial.bernoulli_zero]
  | succ n ih =>
    have hstep := norlund_diagonal_step n (x - 1)
    rw [sub_add_cancel] at hstep
    rw [hstep, ih (x - 1), descPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]

/-- `β_n^{(n+1)}(0) = (-1)^n n!`. -/
theorem norlund_eval_zero_diagonal (n : ℕ) :
    (norlund (n + 1) n).eval 0 = (-1) ^ n * n.factorial := by
  rw [norlund_diagonal, zero_sub, descPochhammer_eval_neg_one]

/-- `[t^n] (t/(e^t-1))^{n+1} = (-1)^n`. -/
theorem coeff_bernoulliPowerSeries_pow_succ (n : ℕ) :
    coeff n (bernoulliPowerSeries ℚ ^ (n + 1)) = (-1) ^ n := by
  have h := norlund_eval_eq_factorial_mul_coeff (n + 1) n 0
  rw [norlund_eval_zero_diagonal, rescale_zero_exp, mul_one] at h
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp at h
  linarith [h]

end Fabius
