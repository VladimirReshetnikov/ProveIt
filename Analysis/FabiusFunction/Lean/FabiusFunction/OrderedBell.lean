import FabiusFunction.BernoulliStirling

/-!
# Ordered Bell (Fubini) numbers

The Fubini number `F_n = ∑_{k ≤ n} k! S(n,k)` counts ordered set partitions of
an `n`-set.  Its exponential generating function is `1/(2 - e^t)`: the
substitution of `u = e^t - 1` into the geometric series `1/(1-u)`, by the
exponential composition theorem with block weights `k!`.  Reading the
identity `1/(1-u) = 1 + u/(1-u)` at `u = e^t - 1` coefficientwise gives the
recurrence `F_{n+1} = ∑_{i ≤ n} C(n+1, i+1) F_{n-i}`.

## Main results

* `fubini`, `egfA_factorial`, `egfA_fubini`.
* `two_sub_exp_mul_egfA_fubini`: `(2 - e^t) ∑_n F_n t^n/n! = 1`.
* `fubini_succ`: the first-block recurrence.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- The ordered Bell (Fubini) numbers `F_n = ∑_{k ≤ n} k! S(n,k)`. -/
def fubini (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), k.factorial * Nat.stirlingSecond n k

section

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The exponential generating function of `k ↦ k!` is the geometric series. -/
theorem egfA_factorial : egfA A (fun k => (k.factorial : A)) = (PowerSeries.mk 1 : A⟦X⟧) := by
  ext n
  rw [coeff_egfA, coeff_mk, Pi.one_apply,
    show (n.factorial : A) = algebraMap ℚ A (n.factorial : ℚ) by simp, ← map_mul,
    one_div_mul_cancel (by positivity), map_one]

/-- **The Fubini generating function as a substitution:**
`∑_n F_n t^n/n! = 1/(1-u)` at `u = e^t - 1`. -/
theorem egfA_fubini :
    egfA A (fun n => (fubini n : A)) = (PowerSeries.mk 1 : A⟦X⟧).subst (exp A - 1) := by
  rw [← egfA_factorial, ← bellWeightSeries_one, egfA_subst_bellWeightSeries]
  congr 1
  funext n
  rw [fubini, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [partialBell_one_cast, Nat.cast_mul]

/-- **The Fubini generating function:** `(2 - e^t) · ∑_n F_n t^n/n! = 1`, i.e.
`∑_n F_n t^n/n! = 1/(2 - e^t)`. -/
theorem two_sub_exp_mul_egfA_fubini :
    (2 - exp A) * egfA A (fun n => (fubini n : A)) = 1 := by
  have hE : HasSubst (exp A - 1) := HasSubst.exp_sub_one
  have h := congrArg (substAlgHom hE) (mk_one_mul_one_sub_eq_one A)
  rw [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom] at h
  rw [egfA_fubini, show (2 : A⟦X⟧) - exp A = 1 - (exp A - 1) by ring, mul_comm]
  exact h

end

/-- **The first-block recurrence:** `F_{n+1} = ∑_{i ≤ n} C(n+1, i+1) F_{n-i}`
(choose the elements of the first block, then order-partition the rest). -/
theorem fubini_succ (n : ℕ) :
    fubini (n + 1) = ∑ i ∈ Finset.range (n + 1), (n + 1).choose (i + 1) * fubini (n - i) := by
  have hE : HasSubst (exp ℚ - 1) := HasSubst.exp_sub_one
  have h := congrArg (substAlgHom hE) (mkOne_eq_one_add_X_mul ℚ)
  rw [map_add, map_one, map_mul, substAlgHom_X, coe_substAlgHom] at h
  rw [← egfA_fubini, ← bellWeightSeries_one, bellWeightSeries, egfA_mul] at h
  have hc := congrArg (coeff (n + 1)) h
  rw [map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), zero_add, coeff_egfA,
    coeff_egfA, Bell.binomialConv_eq_sum_range] at hc
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hc
  have hne : (1 / ((n + 1).factorial : ℚ)) ≠ 0 := by
    have : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    exact one_div_ne_zero this
  have hc' := mul_left_cancel₀ hne hc
  rw [Finset.sum_range_succ'] at hc'
  simp only [Nat.succ_ne_zero, if_false, if_true, one_mul, mul_zero, zero_mul, add_zero,
    Nat.add_sub_add_right] at hc'
  exact_mod_cast hc'

end Fabius
