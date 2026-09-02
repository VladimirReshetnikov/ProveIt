import FabiusFunction.BellHomogeneity

/-!
# Complementary Bell numbers

The complementary Bell numbers `C_n = ∑_{k ≤ n} (-1)^k S(n,k)` are the
complete Bell polynomials at constant weights `-1`, i.e. the Touchard
polynomials at `-1`.  Consequently

* their exponential generating function is `exp(1 - e^t)` (as the substitution
  `exp(-(e^t - 1))`),
* they satisfy `C_{n+1} = -∑_{k ≤ n} C(n,k) C_k`,
* they are the binomial-convolution inverse of the Bell numbers, and
* they have the Dobiński-type series `C_n = e ∑_m (-1)^m m^n / m!`.

## Main results

* `complementaryBell`, `complementaryBell_eq_bell_complete`.
* `exp_subst_neg_exp_sub_one`: the generating function.
* `complementaryBell_succ`: the recurrence.
* `sum_choose_bell_mul_complementaryBell`: the convolution inverse.
* `complementaryBell_eq_exp_mul_tsum`: the Dobiński-type series.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- The complementary Bell numbers `C_n = ∑_{k ≤ n} (-1)^k S(n,k)`. -/
def complementaryBell (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1) ^ k * Nat.stirlingSecond n k

section

variable {R : Type*} [CommRing R]

/-- `C_n` is the complete Bell polynomial at constant weights `-1`. -/
theorem complementaryBell_eq_bell_complete (n : ℕ) :
    (complementaryBell n : R) = Bell.complete (fun _ => (-1 : R)) n := by
  rw [bell_complete_const, complementaryBell, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- `C_n` is the complete Bell polynomial at constant weights `-1`, in `ℤ`. -/
theorem complementaryBell_eq_bell_complete_int (n : ℕ) :
    complementaryBell n = Bell.complete (fun _ => (-1 : ℤ)) n := by
  have h := complementaryBell_eq_bell_complete (R := ℤ) n
  rwa [Int.cast_id] at h

/-- **The recurrence** `C_{n+1} = -∑_{k ≤ n} C(n,k) C_k`. -/
theorem complementaryBell_succ (n : ℕ) :
    complementaryBell (n + 1) = -∑ k ∈ Finset.range (n + 1), n.choose k * complementaryBell k := by
  rw [complementaryBell_eq_bell_complete_int, Bell.complete_succ, Bell.binomialConv_eq_sum_range,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← complementaryBell_eq_bell_complete_int]
  simp only [Bell.shift_apply]
  ring

/-- The Bell numbers as complete Bell polynomials at constant weights `1`. -/
theorem bell_eq_bell_complete_one (n : ℕ) :
    (Nat.bell n : R) = Bell.complete (fun _ => (1 : R)) n := by
  rw [bell_complete_const, bell_eq_sum_stirlingSecond, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one]

/-- The complete Bell polynomial of the zero weights is `δ_{n,0}`. -/
theorem bell_complete_zero_weights (n : ℕ) :
    Bell.complete (fun _ => (0 : R)) n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Bell.complete_succ, Bell.binomialConv_eq_sum_range, if_neg (Nat.succ_ne_zero n)]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [Bell.shift_apply]

/-- **Convolution inverse of the Bell sequence:**
`∑_{k ≤ n} C(n,k) B_k C_{n-k} = δ_{n,0}`. -/
theorem sum_choose_bell_mul_complementaryBell (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * (Nat.bell k * complementaryBell (n - k)) =
      if n = 0 then 1 else 0 := by
  have h := congrFun (Bell.complete_add (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))) n
  have hz : ((fun _ : ℕ => (1 : ℤ)) + fun _ : ℕ => (-1 : ℤ)) = fun _ : ℕ => (0 : ℤ) := by
    funext _
    simp
  rw [hz, bell_complete_zero_weights, Bell.binomialConv_eq_sum_range] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bell_eq_bell_complete_one, complementaryBell_eq_bell_complete_int]

end

section EGF

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- **The generating function** `∑_n C_n t^n/n! = exp(1 - e^t)`, as the substitution
of `-(e^t - 1)` into the exponential series. -/
theorem exp_subst_neg_exp_sub_one :
    (exp A).subst (-(exp A - 1)) = egfA A fun n => (complementaryBell n : A) := by
  rw [← neg_one_smul A (exp A - 1), exp_subst_smul_exp_sub_one]
  congr 1
  funext n
  rw [complementaryBell, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

end EGF

/-- **Dobiński-type series:** `C_n = e · ∑_m (-1)^m m^n / m!`. -/
theorem complementaryBell_eq_exp_mul_tsum (n : ℕ) :
    (complementaryBell n : ℝ) = Real.exp 1 * ∑' m : ℕ, (-1 : ℝ) ^ m * (m : ℝ) ^ n / m.factorial := by
  have h := tsum_pow_mul_pow_div_factorial (-1) n
  have hterm : ∀ m : ℕ, (m : ℝ) ^ n * (-1 : ℝ) ^ m / m.factorial
      = (-1 : ℝ) ^ m * (m : ℝ) ^ n / m.factorial := fun m => by ring
  simp only [hterm] at h
  rw [h, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul,
    complementaryBell, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

end Fabius
