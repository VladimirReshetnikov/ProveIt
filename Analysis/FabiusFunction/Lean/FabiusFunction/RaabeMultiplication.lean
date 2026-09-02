import FabiusFunction.EulerReflection
import FabiusFunction.BernoulliStirling
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Raabe's multiplication theorem for Bernoulli polynomials

`∑_{r < q} β_n(x + r/q) = q^{1-n} β_n(qx)` for `q ≥ 1`, and in particular
`β_n(1/2) = (2^{1-n} - 1) B_n`.

Both sides are read off from generating functions in `(ℚ[x])⟦t⟧`.  With
`B(a; t) = ∑_n β_n(a) t^n/n!` Mathlib gives `B(a;t)(e^t - 1) = t e^{at}`.  Summing
over `a = x + r/q` and using the geometric sum `∑_{r<q} e^{rt/q} = (e^t-1)/(e^{t/q}-1)`
gives `G(t)(e^{t/q} - 1) = t e^{xt}` for the left side `G`; rescaling `B(qx; t)` by
`t ↦ t/q` gives the same identity for the right side; and `e^{t/q} - 1 = (t/q)·(unit)`
is cancelled.

## Main results

* `expSeries_pow`, `rescale_expSeries`, `sum_pow_mul_sub_one`.
* `bernoulliPolySeries`, `bernoulliPolySeries_mul_exp_sub_one`, `coeff_bernoulliPolySeries_eval`.
* `raabe`: the multiplication theorem; `bernoulli_eval_half`: `β_n(1/2) = (2^{1-n}-1) B_n`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

section

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- `e^{at}` to the power `k` is `e^{kat}`. -/
theorem expSeries_pow (a : A) (k : ℕ) : expSeries A a ^ k = expSeries A (k * a) := by
  induction k with
  | zero => simp [expSeries_zero]
  | succ k ih =>
    rw [pow_succ, ih, expSeries_mul]
    push_cast
    ring_nf

/-- Rescaling `e^{at}` by `c` gives `e^{cat}`. -/
theorem rescale_expSeries (c a : A) :
    PowerSeries.rescale c (expSeries A a) = expSeries A (c * a) := by
  ext n
  rw [PowerSeries.coeff_rescale, expSeries, expSeries, coeff_egfA, coeff_egfA, mul_pow]
  ring

/-- The finite geometric sum `(∑_{r<q} y^r)(y - 1) = y^q - 1`. -/
theorem sum_pow_mul_sub_one (y : PowerSeries A) (q : ℕ) :
    (∑ r ∈ Finset.range q, y ^ r) * (y - 1) = y ^ q - 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

end

/-! ### Bernoulli polynomial generating functions with polynomial argument -/

/-- `B(a; t) = ∑_n β_n(a) t^n/n!` for a polynomial argument `a ∈ ℚ[x]`. -/
noncomputable def bernoulliPolySeries (a : ℚ[X]) : PowerSeries ℚ[X] :=
  PowerSeries.mk fun n => aeval a ((1 / n.factorial : ℚ) • Polynomial.bernoulli n)

/-- Mathlib's generating function: `B(a;t)(e^t - 1) = t e^{at}`. -/
theorem bernoulliPolySeries_mul_exp_sub_one (a : ℚ[X]) :
    bernoulliPolySeries a * (PowerSeries.exp ℚ[X] - 1) = PowerSeries.X * expSeries ℚ[X] a := by
  rw [bernoulliPolySeries, Polynomial.bernoulli_generating_function, rescale_exp_eq_expSeries']

/-- The coefficients of `B(a; t)`, evaluated at `x`. -/
theorem coeff_bernoulliPolySeries_eval (a : ℚ[X]) (n : ℕ) (x : ℚ) :
    (PowerSeries.coeff n (bernoulliPolySeries a)).eval x =
      (1 / n.factorial : ℚ) * (Polynomial.bernoulli n).eval (a.eval x) := by
  rw [bernoulliPolySeries, PowerSeries.coeff_mk, ← comp_eq_aeval, smul_comp, eval_smul,
    eval_comp, smul_eq_mul]

/-- `e^{t/q}` raised to the `q`-th power is `e^t`. -/
theorem expSeries_C_inv_pow (q : ℕ) (hq : 0 < q) :
    expSeries ℚ[X] (C (1 / (q : ℚ))) ^ q = expSeries ℚ[X] 1 := by
  rw [expSeries_pow]
  congr 1
  rw [← map_natCast (C : ℚ →+* ℚ[X]) q, ← map_mul, mul_one_div_cancel (by positivity), map_one]

/-- **Raabe's multiplication theorem:**
`∑_{r<q} β_n(x + r/q) = q · (1/q)^n · β_n(q x)` for `q ≥ 1`. -/
theorem raabe (n q : ℕ) (hq : 0 < q) (x : ℚ) :
    ∑ r ∈ Finset.range q, (Polynomial.bernoulli n).eval (x + r / q) =
      (q : ℚ) * (1 / (q : ℚ)) ^ n * (Polynomial.bernoulli n).eval (q * x) := by
  have hqQ : ((q : ℚ)) ≠ 0 := by positivity
  -- notation
  set c : ℚ[X] := C (1 / (q : ℚ)) with hc_def
  set y : PowerSeries ℚ[X] := expSeries ℚ[X] c with hy
  set G : PowerSeries ℚ[X] :=
    ∑ r ∈ Finset.range q, bernoulliPolySeries (X + C ((r : ℚ) / q)) with hG
  set H : PowerSeries ℚ[X] :=
    PowerSeries.C (C (q : ℚ)) * PowerSeries.rescale c (bernoulliPolySeries (C (q : ℚ) * X)) with hH
  -- `e^t - 1 = t · u` with `u` a unit, and `y - 1 = t · (unit)`
  have hu := X_mul_expSubOneDiv ℚ[X]
  have hunit := isUnit_expSubOneDiv ℚ[X]
  have hy1 : y - 1 = PowerSeries.rescale c (PowerSeries.exp ℚ[X] - 1) := by
    rw [map_sub, map_one, rescale_exp_eq_expSeries', hy]
  have hy2 : y - 1 = PowerSeries.X * (PowerSeries.C c * PowerSeries.rescale c (expSubOneDiv ℚ[X])) := by
    rw [hy1, ← hu, map_mul, PowerSeries.rescale_X]
    ring
  have hunit' : IsUnit (PowerSeries.C c * PowerSeries.rescale c (expSubOneDiv ℚ[X])) := by
    refine IsUnit.mul ?_ ?_
    · rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C, hc_def,
        Polynomial.isUnit_C]
      exact isUnit_iff_ne_zero.mpr (one_div_ne_zero hqQ)
    · rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_rescale, expSubOneDiv, PowerSeries.coeff_mk]
      simp
  -- the left side: `G (e^t - 1) = t e^{xt} ∑_r y^r`
  have hGsum : G * (PowerSeries.exp ℚ[X] - 1) =
      PowerSeries.X * expSeries ℚ[X] X * ∑ r ∈ Finset.range q, y ^ r := by
    rw [hG, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [bernoulliPolySeries_mul_exp_sub_one, ← expSeries_mul, hy, expSeries_pow,
      show ((r : ℚ) / q) = (r : ℚ) * (1 / q) by ring, map_mul, map_natCast]
    ring
  -- hence `G (y - 1) = t e^{xt}`
  have hG1 : G * (y - 1) = PowerSeries.X * expSeries ℚ[X] X := by
    have h1 : (G * (y - 1) - PowerSeries.X * expSeries ℚ[X] X) * (PowerSeries.exp ℚ[X] - 1) = 0 := by
      have hgeom := sum_pow_mul_sub_one ℚ[X] y q
      rw [hy, expSeries_C_inv_pow q hq, ← hy, ← exp_eq_expSeries_one] at hgeom
      linear_combination (y - 1) * hGsum + PowerSeries.X * expSeries ℚ[X] X * hgeom
    rw [← hu, show (G * (y - 1) - PowerSeries.X * expSeries ℚ[X] X) * (PowerSeries.X * expSubOneDiv ℚ[X])
        = PowerSeries.X * ((G * (y - 1) - PowerSeries.X * expSeries ℚ[X] X) * expSubOneDiv ℚ[X])
        by ring] at h1
    have h2 := eq_zero_of_X_mul_eq_zero ℚ[X] h1
    rw [hunit.mul_left_eq_zero] at h2
    exact sub_eq_zero.mp h2
  -- the right side: `H (y - 1) = t e^{xt}` as well
  have hH1 : H * (y - 1) = PowerSeries.X * expSeries ℚ[X] X := by
    have h := congrArg (PowerSeries.rescale c) (bernoulliPolySeries_mul_exp_sub_one (C (q : ℚ) * X))
    rw [map_mul, map_mul, map_sub, map_one, PowerSeries.rescale_X, rescale_expSeries,
      rescale_exp_eq_expSeries', ← hy,
      show c * (C (q : ℚ) * X) = X by
        rw [hc_def, ← mul_assoc, ← map_mul, one_div_mul_cancel hqQ, map_one, one_mul]] at h
    calc H * (y - 1)
        = PowerSeries.C (C (q : ℚ)) * (PowerSeries.rescale c (bernoulliPolySeries (C (q : ℚ) * X)) *
            (y - 1)) := by rw [hH]; ring
      _ = PowerSeries.C (C (q : ℚ)) * (PowerSeries.C c * PowerSeries.X * expSeries ℚ[X] X) := by
          rw [h]
      _ = PowerSeries.X * expSeries ℚ[X] X := by
          rw [← mul_assoc, ← mul_assoc, ← map_mul, hc_def, ← map_mul, mul_one_div_cancel hqQ,
            map_one, map_one, one_mul]
  -- cancel the unit factor of `y - 1`
  have hGH : G = H := by
    have h1 : (G - H) * (PowerSeries.X * (PowerSeries.C c *
        PowerSeries.rescale c (expSubOneDiv ℚ[X]))) = 0 := by
      rw [← hy2]
      linear_combination hG1 - hH1
    rw [show (G - H) * (PowerSeries.X * (PowerSeries.C c * PowerSeries.rescale c (expSubOneDiv ℚ[X])))
        = PowerSeries.X * ((G - H) * (PowerSeries.C c * PowerSeries.rescale c (expSubOneDiv ℚ[X])))
        by ring] at h1
    have h2 := eq_zero_of_X_mul_eq_zero ℚ[X] h1
    rw [hunit'.mul_left_eq_zero] at h2
    exact sub_eq_zero.mp h2
  -- compare the coefficients of `t^n` and evaluate at `x`
  have hc := congrArg (fun φ : PowerSeries ℚ[X] => (PowerSeries.coeff n φ).eval x) hGH
  simp only [hG, hH, hc_def, map_sum, eval_finsetSum, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, eval_mul, eval_C, eval_pow, coeff_bernoulliPolySeries_eval, eval_add,
    eval_X] at hc
  have hn : (1 / (n.factorial : ℚ)) ≠ 0 := one_div_ne_zero (by positivity)
  have hc' : (1 / (n.factorial : ℚ)) * ∑ r ∈ Finset.range q, (Polynomial.bernoulli n).eval (x + r / q)
      = (1 / (n.factorial : ℚ)) *
        ((q : ℚ) * (1 / (q : ℚ)) ^ n * (Polynomial.bernoulli n).eval (q * x)) := by
    rw [Finset.mul_sum, hc]
    ring
  exact mul_left_cancel₀ hn hc'

/-- `β_n(1/2) = (2 (1/2)^n - 1) B_n`, i.e. `β_n(1/2) = (2^{1-n} - 1) B_n`. -/
theorem bernoulli_eval_half (n : ℕ) :
    (Polynomial.bernoulli n).eval (1 / 2 : ℚ) = (2 * (1 / 2 : ℚ) ^ n - 1) * _root_.bernoulli n := by
  have h := raabe n 2 (by norm_num) 0
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  norm_num [Polynomial.bernoulli_eval_zero] at h
  linear_combination h

end Fabius
