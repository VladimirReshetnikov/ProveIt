import FabiusFunction.BernoulliNewtonBasis
import FabiusFunction.StirlingFirstReverse

/-!
# Nörlund's generalized Bernoulli polynomials of natural order

For `a ∈ ℕ` the Nörlund polynomials `β_n^{(a)}(x)` are defined by

`(t/(e^t - 1))^a e^{xt} = ∑_n β_n^{(a)}(x) t^n/n!`

(`norlundSeries`, `norlund`).  They interpolate `β_n^{(0)} = x^n` and `β_n^{(1)} = β_n`
(`norlund_zero`, `norlund_one`) and satisfy the Appell property
`(β_{n+1}^{(a)})' = (n+1) β_n^{(a)}` (`derivative_norlund_succ`), the convolution law
`β_n^{(a+c)}(x+y) = ∑_k C(n,k) β_k^{(a)}(x) β_{n-k}^{(c)}(y)` (`norlund_add_eval_add`) with its
special case the translation formula (`norlund_eval_add`), and the difference equation
`β_{n+1}^{(a+1)}(x+1) - β_{n+1}^{(a+1)}(x) = (n+1) β_n^{(a)}(x)` (`norlund_succ_eval_add_one_sub`).

## Main results

* `norlundSeries`, `norlund`, `coeff_norlundSeries`, `norlund_zero`, `norlund_one`.
* `derivative_coeff_succ_map_C_mul_rescale_exp`, `derivative_norlund_succ`.
* `egfA_norlund_eval`, `norlund_add_eval_add`, `norlund_eval_add`,
  `norlund_succ_eval_add_one_sub`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- The generating function `(t/(e^t-1))^a e^{xt}` of the Nörlund polynomials of order `a`. -/
noncomputable def norlundSeries (a : ℕ) : (Polynomial ℚ)⟦X⟧ :=
  PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) (bernoulliPowerSeries ℚ) ^ a *
    rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ))

/-- The Nörlund polynomial `β_n^{(a)}(x) = n! [t^n] (t/(e^t-1))^a e^{xt}`. -/
noncomputable def norlund (a n : ℕ) : Polynomial ℚ :=
  (n.factorial : ℚ) • coeff n (norlundSeries a)

theorem coeff_norlundSeries (a n : ℕ) :
    coeff n (norlundSeries a) = (1 / n.factorial : ℚ) • norlund a n := by
  rw [norlund, smul_smul, one_div_mul_cancel (by positivity), one_smul]

/-- `β_n^{(0)}(x) = x^n`. -/
theorem norlund_zero (n : ℕ) : norlund 0 n = Polynomial.X ^ n := by
  rw [norlund, norlundSeries, pow_zero, one_mul, coeff_rescale, coeff_exp, Polynomial.algebraMap_eq,
    Polynomial.smul_eq_C_mul, mul_comm (Polynomial.X ^ n), ← mul_assoc, ← Polynomial.C_mul,
    mul_one_div_cancel (by positivity), Polynomial.C_1, one_mul]

/-- The Bernoulli generating function over `ℚ` mapped into `ℚ[x]`. -/
theorem map_C_bernoulliPowerSeries :
    PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) (bernoulliPowerSeries ℚ) =
      bernoulliPowerSeries (Polynomial ℚ) := by
  ext n
  rw [coeff_map, bernoulliPowerSeries, bernoulliPowerSeries, coeff_mk, coeff_mk,
    Algebra.algebraMap_self, RingHom.id_apply, Polynomial.algebraMap_eq]

/-- `β_n^{(1)}(x) = β_n(x)`. -/
theorem norlund_one (n : ℕ) : norlund 1 n = Polynomial.bernoulli n := by
  rw [norlund, norlundSeries, pow_one, map_C_bernoulliPowerSeries, mul_comm,
    ← bernoulliPolySeries_eq, coeff_bernoulliPolySeries, smul_smul,
    mul_one_div_cancel (by positivity), one_smul]

/-! ### The Appell property -/

/-- For a series `G` with constant coefficients, `d/dx [t^{n+1}](G e^{xt}) = [t^n](G e^{xt})`. -/
theorem derivative_coeff_succ_map_C_mul_rescale_exp (G : ℚ⟦X⟧) (n : ℕ) :
    Polynomial.derivative (coeff (n + 1)
      (PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) G *
        rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ)))) =
      coeff n (PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) G *
        rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ))) := by
  rw [coeff_mul, coeff_mul, Finset.Nat.sum_antidiagonal_succ', map_add, coeff_rescale, pow_zero,
    one_mul, coeff_exp, Polynomial.algebraMap_eq, coeff_map, ← Polynomial.C_mul,
    Polynomial.derivative_C, zero_add, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  show Polynomial.derivative (Polynomial.C (coeff p.1 G) *
      coeff (p.2 + 1) (rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ)))) =
    Polynomial.C (coeff p.1 G) * coeff p.2 (rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ)))
  rw [coeff_rescale, coeff_rescale, coeff_exp, coeff_exp,
    Polynomial.algebraMap_eq, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, mul_zero, add_zero, Polynomial.derivative_X_pow, Nat.add_sub_cancel]
  have hc : Polynomial.C ((p.2 + 1 : ℕ) : ℚ) * Polynomial.C (1 / (p.2 + 1).factorial : ℚ) =
      Polynomial.C (1 / p.2.factorial : ℚ) := by
    rw [← Polynomial.C_mul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    have h1 : (p.2.factorial : ℚ) ≠ 0 := by positivity
    field_simp
  calc Polynomial.C (coeff p.1 G) *
        (Polynomial.C ((p.2 + 1 : ℕ) : ℚ) * Polynomial.X ^ p.2 *
          Polynomial.C (1 / (p.2 + 1).factorial : ℚ))
      = Polynomial.C (coeff p.1 G) * (Polynomial.X ^ p.2 *
          (Polynomial.C ((p.2 + 1 : ℕ) : ℚ) * Polynomial.C (1 / (p.2 + 1).factorial : ℚ))) := by
        ring
    _ = _ := by rw [hc]

/-- **The Appell property:** `(β_{n+1}^{(a)})' = (n+1) β_n^{(a)}`. -/
theorem derivative_norlund_succ (a n : ℕ) :
    Polynomial.derivative (norlund a (n + 1)) = ((n + 1 : ℕ) : Polynomial ℚ) * norlund a n := by
  rw [norlund, norlund, Polynomial.derivative_smul, norlundSeries, ← map_pow,
    derivative_coeff_succ_map_C_mul_rescale_exp, Nat.factorial_succ, Nat.cast_mul, mul_smul,
    Polynomial.smul_eq_C_mul, map_natCast]

/-! ### Evaluation generating functions, convolution and translation -/

/-- The EGF of `n ↦ β_n^{(a)}(x)` at a point `x : ℚ` is `(t/(e^t-1))^a e^{xt}`. -/
theorem egfA_norlund_eval (a : ℕ) (x : ℚ) :
    egfA ℚ (fun n => (norlund a n).eval x) = bernoulliPowerSeries ℚ ^ a * rescale x (exp ℚ) := by
  have h1 : PowerSeries.map (Polynomial.evalRingHom x)
      (PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ) (bernoulliPowerSeries ℚ)) =
        bernoulliPowerSeries ℚ := by
    ext n
    rw [coeff_map, coeff_map, Polynomial.coe_evalRingHom, Polynomial.eval_C]
  have h2 : PowerSeries.map (Polynomial.evalRingHom x)
      (rescale (Polynomial.X : Polynomial ℚ) (exp (Polynomial ℚ))) = rescale x (exp ℚ) := by
    ext n
    rw [coeff_map, coeff_rescale, coeff_rescale, coeff_exp, coeff_exp, Polynomial.coe_evalRingHom,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.algebraMap_eq,
      Polynomial.eval_C, Algebra.algebraMap_self, RingHom.id_apply]
  have h3 : PowerSeries.map (Polynomial.evalRingHom x) (norlundSeries a) =
      bernoulliPowerSeries ℚ ^ a * rescale x (exp ℚ) := by
    rw [norlundSeries, map_mul, map_pow, h1, h2]
  rw [← h3]
  ext n
  rw [coeff_egfA, coeff_map, coeff_norlundSeries, Polynomial.coe_evalRingHom,
    Polynomial.eval_smul, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]

/-- **Convolution:** `β_n^{(a+c)}(x+y) = ∑_k C(n,k) β_k^{(a)}(x) β_{n-k}^{(c)}(y)`. -/
theorem norlund_add_eval_add (a c n : ℕ) (x y : ℚ) :
    (norlund (a + c) n).eval (x + y) =
      ∑ k ∈ range (n + 1),
        (n.choose k : ℚ) * ((norlund a k).eval x * (norlund c (n - k)).eval y) := by
  have h : egfA ℚ (fun n => (norlund (a + c) n).eval (x + y)) =
      egfA ℚ (Bell.binomialConv (fun k => (norlund a k).eval x) (fun k => (norlund c k).eval y)) := by
    rw [← egfA_mul, egfA_norlund_eval, egfA_norlund_eval, egfA_norlund_eval, pow_add,
      ← exp_mul_exp_eq_exp_add]
    ring
  have h' := congrFun (seq_eq_of_egfA_eq ℚ h) n
  rw [Bell.binomialConv_eq_sum_range] at h'
  exact h'

/-- **Translation:** `β_n^{(a)}(x+y) = ∑_k C(n,k) β_k^{(a)}(x) y^{n-k}`. -/
theorem norlund_eval_add (a n : ℕ) (x y : ℚ) :
    (norlund a n).eval (x + y) =
      ∑ k ∈ range (n + 1), (n.choose k : ℚ) * ((norlund a k).eval x * y ^ (n - k)) := by
  have h := norlund_add_eval_add a 0 n x y
  rw [Nat.add_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norlund_zero, Polynomial.eval_pow, Polynomial.eval_X]

/-- **The difference equation:** `β_{n+1}^{(a+1)}(x+1) - β_{n+1}^{(a+1)}(x) = (n+1) β_n^{(a)}(x)`. -/
theorem norlund_succ_eval_add_one_sub (a n : ℕ) (x : ℚ) :
    (norlund (a + 1) (n + 1)).eval (x + 1) - (norlund (a + 1) (n + 1)).eval x =
      (n + 1) * (norlund a n).eval x := by
  have h : egfA ℚ (fun m => (norlund (a + 1) m).eval (x + 1)) -
      egfA ℚ (fun m => (norlund (a + 1) m).eval x) =
        X * egfA ℚ (fun m => (norlund a m).eval x) := by
    rw [egfA_norlund_eval, egfA_norlund_eval, egfA_norlund_eval, ← exp_mul_exp_eq_exp_add,
      rescale_one, RingHom.id_apply, pow_succ]
    have hB := bernoulliPowerSeries_mul_exp_sub_one ℚ
    linear_combination (bernoulliPowerSeries ℚ ^ a * rescale x (exp ℚ)) * hB
  have hc := congrArg (coeff (n + 1)) h
  rw [map_sub, coeff_egfA, coeff_egfA, coeff_succ_X_mul, coeff_egfA, Algebra.algebraMap_self,
    RingHom.id_apply, RingHom.id_apply, ← mul_sub] at hc
  have hn : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
  have hn' : (n.factorial : ℚ) ≠ 0 := by positivity
  calc (norlund (a + 1) (n + 1)).eval (x + 1) - (norlund (a + 1) (n + 1)).eval x
      = ((n + 1).factorial : ℚ) * (1 / (n + 1).factorial *
          ((norlund (a + 1) (n + 1)).eval (x + 1) - (norlund (a + 1) (n + 1)).eval x)) := by
        field_simp
    _ = ((n + 1).factorial : ℚ) * (1 / n.factorial * (norlund a n).eval x) := by rw [hc]
    _ = (n + 1) * (norlund a n).eval x := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp

end Fabius
