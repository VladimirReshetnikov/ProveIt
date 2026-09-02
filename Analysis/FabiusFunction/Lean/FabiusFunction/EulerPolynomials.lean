import FabiusFunction.GenocchiNumbers
import FabiusFunction.BellShiftEGF
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Euler polynomials

The Euler polynomials are defined by the exponential generating function
`2 e^{xt}/(e^t + 1) = ∑_n E_n(x) t^n/n!`.  We take `e_n = E_n(0) = n! [t^n] 2/(e^t+1)`
and `E_n(x) = ∑_k C(n,k) e_k x^{n-k}` (an Appell sequence by construction), and prove

* the derivative identity `E_n' = n E_{n-1}`,
* the translation formula `E_n(x+y) = ∑_k C(n,k) E_k(x) y^{n-k}` (via a general
  Appell lemma `appell_eval_add`),
* the difference identity `E_n(x+1) + E_n(x) = 2 x^n`,
* the relation `G_{n+1} = (n+1) E_n(0)` with the Genocchi numbers,
* the alternating power sums `∑_{j<N} (-1)^j (x+j)^n = (E_n(x) - (-1)^N E_n(x+N))/2`.

## Main results

* `eulerZeroSeries`, `eulerNumberZero`, `egfA_eulerNumberZero`, `sum_choose_eulerNumberZero_add`.
* `eulerPolynomial`, `eulerPolynomial_eval`, `derivative_eulerPolynomial`,
  `natDegree_eulerPolynomial_le`.
* `appell_eval_add`, `eulerPolynomial_eval_add`.
* `egfA_eulerPolynomial`, `sum_choose_mul_eulerPolynomial_add`, `eulerPolynomial_eval_add_one_add`.
* `genocchi_succ_eq`, `sum_neg_one_pow_mul_pow_eq_eulerPolynomial`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-! ### The values at zero -/

/-- The series `2/(e^t + 1)`. -/
noncomputable def eulerZeroSeries : PowerSeries ℚ := 2 * (PowerSeries.exp ℚ + 1)⁻¹

/-- `e^t + 1` has constant term `2`. -/
theorem constantCoeff_exp_add_one_ne_zero :
    PowerSeries.constantCoeff (PowerSeries.exp ℚ + 1) ≠ 0 := by
  rw [map_add, PowerSeries.constantCoeff_exp, map_one]
  norm_num

/-- `2/(e^t+1) · (e^t + 1) = 2`. -/
theorem eulerZeroSeries_mul_exp_add_one : eulerZeroSeries * (PowerSeries.exp ℚ + 1) = 2 := by
  rw [eulerZeroSeries, mul_assoc, PowerSeries.inv_mul_cancel _ constantCoeff_exp_add_one_ne_zero,
    mul_one]

/-- `e_n = E_n(0) = n! [t^n] 2/(e^t+1)`. -/
noncomputable def eulerNumberZero (n : ℕ) : ℚ := n.factorial * PowerSeries.coeff n eulerZeroSeries

/-- `∑_n e_n t^n/n! = 2/(e^t+1)`. -/
theorem egfA_eulerNumberZero : egfA ℚ eulerNumberZero = eulerZeroSeries := by
  ext n
  rw [coeff_egfA, eulerNumberZero, Algebra.algebraMap_self, RingHom.id_apply]
  have : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- `∑_{k ≤ n} C(n,k) e_k + e_n = 2 δ_{n,0}`. -/
theorem sum_choose_eulerNumberZero_add (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * eulerNumberZero k + eulerNumberZero n =
      if n = 0 then 2 else 0 := by
  have h := congrArg (PowerSeries.coeff n) eulerZeroSeries_mul_exp_add_one
  rw [← egfA_eulerNumberZero, mul_add, mul_one, exp_eq_expSeries_one, expSeries, egfA_mul,
    map_add, coeff_egfA, coeff_egfA, Bell.binomialConv_eq_sum_range,
    ← map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2, PowerSeries.coeff_C] at h
  simp only [Algebra.algebraMap_self, RingHom.id_apply, one_pow, mul_one] at h
  have h' : (1 / (n.factorial : ℚ)) *
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * eulerNumberZero k + eulerNumberZero n)
      = if n = 0 then 2 else 0 := by
    rw [mul_add, Finset.mul_sum]
    rw [Finset.mul_sum] at h
    exact h
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa using h'
  · rw [if_neg (by omega)] at h' ⊢
    have hn : (1 / (n.factorial : ℚ)) ≠ 0 := one_div_ne_zero (by positivity)
    exact (mul_eq_zero.mp h').resolve_left hn

/-! ### The polynomials -/

/-- The Euler polynomial `E_n(x) = ∑_{k ≤ n} C(n,k) e_k x^{n-k}`. -/
noncomputable def eulerPolynomial (n : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℚ[X]) * (C (eulerNumberZero i) * X ^ (n - i))

/-- Evaluation of the Euler polynomial. -/
theorem eulerPolynomial_eval (n : ℕ) (x : ℚ) :
    (eulerPolynomial n).eval x =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℚ) * (eulerNumberZero i * x ^ (n - i)) := by
  rw [eulerPolynomial, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_natCast, eval_mul, eval_C, eval_pow, eval_X]

/-- `E_n(0) = e_n`. -/
theorem eulerPolynomial_eval_zero (n : ℕ) : (eulerPolynomial n).eval 0 = eulerNumberZero n := by
  rw [eulerPolynomial_eval, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one,
    Nat.choose_self, Nat.cast_one, one_mul]
  rw [Finset.sum_eq_zero fun i hi => ?_, zero_add]
  have hin : i < n := Finset.mem_range.mp hi
  rw [zero_pow (by omega), mul_zero, mul_zero]

/-- `deg E_n ≤ n`. -/
theorem natDegree_eulerPolynomial_le (n : ℕ) : (eulerPolynomial n).natDegree ≤ n := by
  rw [eulerPolynomial]
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  calc ((n.choose i : ℚ[X]) * (C (eulerNumberZero i) * X ^ (n - i))).natDegree
      ≤ (n.choose i : ℚ[X]).natDegree + (C (eulerNumberZero i) * X ^ (n - i)).natDegree :=
        natDegree_mul_le
    _ ≤ 0 + (n - i) := by
        rw [natDegree_natCast]
        exact Nat.add_le_add_left (natDegree_C_mul_X_pow_le _ _) 0
    _ ≤ n := by omega

/-- **The Appell property:** `E_{n+1}' = (n+1) E_n`. -/
theorem derivative_eulerPolynomial (n : ℕ) :
    derivative (eulerPolynomial (n + 1)) = ((n + 1 : ℕ) : ℚ[X]) * eulerPolynomial n := by
  rw [eulerPolynomial, eulerPolynomial, derivative_sum, Finset.mul_sum,
    Finset.sum_range_succ (fun i => derivative
      (((n + 1).choose i : ℚ[X]) * (C (eulerNumberZero i) * X ^ (n + 1 - i)))) (n + 1),
    Nat.sub_self, pow_zero, mul_one, derivative_mul, derivative_natCast, zero_mul, zero_add,
    derivative_C, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [derivative_mul, derivative_natCast, zero_mul, zero_add, derivative_C_mul_X_pow,
    show n + 1 - i - 1 = n - i by omega, map_mul, map_natCast]
  have hc : (((n + 1).choose i : ℕ) : ℚ[X]) * ((n + 1 - i : ℕ) : ℚ[X])
      = ((n + 1 : ℕ) : ℚ[X]) * (n.choose i : ℚ[X]) := by
    have := Nat.choose_mul_succ_eq n i
    exact_mod_cast (by rw [mul_comm] at this; exact this.symm)
  linear_combination (C (eulerNumberZero i) * X ^ (n - i)) * hc

/-! ### The Appell translation formula -/

/-- Iterated derivatives of an Appell sequence. -/
theorem appell_iterate_derivative (p : ℕ → ℚ[X])
    (hd : ∀ n, derivative (p (n + 1)) = ((n + 1 : ℕ) : ℚ[X]) * p n)
    (hdeg : ∀ n, (p n).natDegree ≤ n) (n k : ℕ) :
    (derivative : ℚ[X] → ℚ[X])^[k] (p n) = (n.descFactorial k : ℚ[X]) * p (n - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_mul, derivative_natCast, zero_mul, zero_add,
      Nat.descFactorial_succ]
    rcases Nat.lt_or_ge k n with hkn | hkn
    · obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
      rw [hm, hd m, show n - (k + 1) = m by omega]
      push_cast
      ring
    · have h0 : p (n - k) = C ((p (n - k)).coeff 0) := by
        apply eq_C_of_natDegree_le_zero
        have := hdeg (n - k)
        rw [Nat.sub_eq_zero_of_le hkn] at this ⊢
        exact this
      rw [h0, derivative_C, mul_zero, Nat.sub_eq_zero_of_le hkn, zero_mul, Nat.cast_zero,
        zero_mul]

/-- **Translation formula for Appell sequences:** if `p_{n+1}' = (n+1) p_n` and
`deg p_n ≤ n` then `p_n(x + y) = ∑_{k ≤ n} C(n,k) p_k(x) y^{n-k}`. -/
theorem appell_eval_add (p : ℕ → ℚ[X])
    (hd : ∀ n, derivative (p (n + 1)) = ((n + 1 : ℕ) : ℚ[X]) * p n)
    (hdeg : ∀ n, (p n).natDegree ≤ n) (n : ℕ) (x y : ℚ) :
    (p n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (p k).eval x * y ^ (n - k) := by
  have hhasse : ∀ k, hasseDeriv k (p n) = (n.choose k : ℚ[X]) * p (n - k) := by
    intro k
    have h := congrFun (factorial_smul_hasseDeriv (R := ℚ) (k := k)) (p n)
    rw [LinearMap.smul_apply, appell_iterate_derivative p hd hdeg,
      Nat.descFactorial_eq_factorial_mul_choose, nsmul_eq_mul] at h
    have hk : ((k.factorial : ℕ) : ℚ[X]) ≠ 0 := by
      rw [ne_eq, Nat.cast_eq_zero]
      exact Nat.factorial_ne_zero k
    apply mul_left_cancel₀ hk
    rw [h]
    push_cast
    ring
  rw [add_comm, ← taylor_eval x (p n) y,
    eval_eq_sum_range' (n := n + 1) (by rw [natDegree_taylor]; exact Nat.lt_succ_of_le (hdeg n)),
    ← Finset.sum_range_reflect
      (fun k => (n.choose k : ℚ) * (p k).eval x * y ^ (n - k)) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [taylor_coeff, hhasse, eval_mul, eval_natCast, Nat.add_sub_cancel, Nat.sub_sub_self hkn,
    Nat.choose_symm hkn]

/-- **The translation formula for Euler polynomials:**
`E_n(x + y) = ∑_{k ≤ n} C(n,k) E_k(x) y^{n-k}`. -/
theorem eulerPolynomial_eval_add (n : ℕ) (x y : ℚ) :
    (eulerPolynomial n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (eulerPolynomial k).eval x * y ^ (n - k) :=
  appell_eval_add eulerPolynomial derivative_eulerPolynomial natDegree_eulerPolynomial_le n x y

/-! ### The generating function and the difference identity -/

/-- `∑_n E_n(x) t^n/n! = (2/(e^t+1)) e^{xt}` in `(ℚ[x])⟦t⟧`. -/
theorem egfA_eulerPolynomial :
    egfA ℚ[X] eulerPolynomial =
      egfA ℚ[X] (fun j => C (eulerNumberZero j)) * expSeries ℚ[X] X := by
  rw [expSeries, egfA_mul]
  try rfl

/-- `(∑_n e_n t^n/n!) (e^t + 1) = 2` in `(ℚ[x])⟦t⟧`. -/
theorem egfA_C_eulerNumberZero_mul :
    egfA ℚ[X] (fun j => C (eulerNumberZero j)) * (PowerSeries.exp ℚ[X] + 1) = 2 := by
  have h := congrArg (PowerSeries.map (C : ℚ →+* ℚ[X])) eulerZeroSeries_mul_exp_add_one
  rw [map_mul, map_add, PowerSeries.map_exp, map_one, map_ofNat, ← egfA_eulerNumberZero] at h
  have hE : PowerSeries.map (C : ℚ →+* ℚ[X]) (egfA ℚ eulerNumberZero)
      = egfA ℚ[X] (fun j => C (eulerNumberZero j)) := by
    ext n
    rw [PowerSeries.coeff_map, coeff_egfA, coeff_egfA, map_mul, Algebra.algebraMap_self,
      RingHom.id_apply, Polynomial.algebraMap_eq]
  rwa [hE] at h

/-- **The difference identity, polynomial form:**
`∑_{k ≤ n} C(n,k) E_k + E_n = 2 x^n`. -/
theorem sum_choose_mul_eulerPolynomial_add (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ[X]) * eulerPolynomial k + eulerPolynomial n =
      2 * X ^ n := by
  have h : egfA ℚ[X] eulerPolynomial * (PowerSeries.exp ℚ[X] + 1) = 2 * expSeries ℚ[X] X := by
    rw [egfA_eulerPolynomial, mul_right_comm, egfA_C_eulerNumberZero_mul]
  have hexp : PowerSeries.exp ℚ[X] = egfA ℚ[X] (fun _ => (1 : ℚ[X])) := by
    ext m
    rw [PowerSeries.coeff_exp, coeff_egfA, mul_one]
  have hc := congrArg (PowerSeries.coeff n) h
  rw [mul_add, mul_one, hexp, egfA_mul, map_add, coeff_egfA, coeff_egfA,
    Bell.binomialConv_eq_sum_range, ← map_ofNat (PowerSeries.C : ℚ[X] →+* PowerSeries ℚ[X]) 2,
    PowerSeries.coeff_C_mul, expSeries, coeff_egfA, Polynomial.algebraMap_eq] at hc
  simp only [mul_one] at hc
  have hC : (C (1 / (n.factorial : ℚ)) : ℚ[X]) ≠ 0 := by
    rw [ne_eq, C_eq_zero]
    exact one_div_ne_zero (by positivity)
  apply mul_left_cancel₀ hC
  calc C (1 / (n.factorial : ℚ)) *
        (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ[X]) * eulerPolynomial k + eulerPolynomial n)
      = C (1 / (n.factorial : ℚ)) * ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℚ[X]) * eulerPolynomial k + C (1 / (n.factorial : ℚ)) * eulerPolynomial n := by
        ring
    _ = 2 * (C (1 / (n.factorial : ℚ)) * X ^ n) := hc
    _ = _ := by ring

/-- **The difference identity:** `E_n(x + 1) + E_n(x) = 2 x^n`. -/
theorem eulerPolynomial_eval_add_one_add (n : ℕ) (x : ℚ) :
    (eulerPolynomial n).eval (x + 1) + (eulerPolynomial n).eval x = 2 * x ^ n := by
  have h := congrArg (Polynomial.eval x) (sum_choose_mul_eulerPolynomial_add n)
  rw [eval_add, eval_finsetSum, eval_mul, eval_pow, eval_X, eval_ofNat] at h
  rw [eulerPolynomial_eval_add, ← h]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_natCast, one_pow, mul_one]

/-! ### Genocchi numbers and alternating power sums -/

/-- `G_{n+1} = (n+1) E_n(0)`. -/
theorem genocchi_succ_eq (n : ℕ) : genocchi (n + 1) = (n + 1) * eulerNumberZero n := by
  have hunit : IsUnit (PowerSeries.exp ℚ + 1) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr constantCoeff_exp_add_one_ne_zero
  have h : egf ℚ genocchi = PowerSeries.X * eulerZeroSeries := by
    apply hunit.mul_right_cancel
    rw [egf_genocchi_mul_exp_add_one, mul_assoc, eulerZeroSeries_mul_exp_add_one, mul_comm]
  have hc := congrArg (PowerSeries.coeff (n + 1)) h
  rw [coeff_egf, PowerSeries.coeff_succ_X_mul, Algebra.algebraMap_self, RingHom.id_apply] at hc
  rw [eulerNumberZero, ← hc]
  have hn : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
  have hfac : ((n + 1).factorial : ℚ) = (n + 1) * n.factorial := by
    push_cast [Nat.factorial_succ]
    ring
  rw [hfac]
  field_simp

/-- **Alternating power sums:**
`∑_{j < N} (-1)^j (x+j)^n = (E_n(x) - (-1)^N E_n(x+N)) / 2`. -/
theorem sum_neg_one_pow_mul_pow_eq_eulerPolynomial (n N : ℕ) (x : ℚ) :
    ∑ j ∈ Finset.range N, (-1 : ℚ) ^ j * (x + j) ^ n =
      ((eulerPolynomial n).eval x - (-1) ^ N * (eulerPolynomial n).eval (x + N)) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hd := eulerPolynomial_eval_add_one_add n (x + N)
    rw [add_assoc, show ((N : ℚ) + 1) = ((N + 1 : ℕ) : ℚ) by push_cast; ring] at hd
    rw [pow_succ]
    linear_combination (-((-1 : ℚ) ^ N) / 2) * hd

end Fabius
