import FabiusFunction.StirlingBasisChange
import FabiusFunction.BellGeneratingFunctions

/-!
# Reverse recurrences of the unsigned Stirling numbers of the first kind

Two "reverse" recurrences express `(n-k) c(n,k)` through entries further along the row or the
column of the triangle:

* **row form:** `(n-k) c(n,k) = ∑_{j=2}^{n-k+1} C(k+j-1, j) c(n, k+j-1)`, from the coefficient
  of `x^{k}` in `x^{(n+1)} = x · (x+1)^{(n)}` (`first_reverse_row`, on top of
  `stirlingFirst_succ_succ_eq_sum_choose` in `StirlingBasisChange`);
* **column form:** `(n-k) c(n,k) = ∑_{j=2}^{n-k+1} (j-2)! C(n,j) c(n-j+1, k)`, from the
  exponential generating functions `F_k = (-log(1-x))^k/k!`: the right side has EGF
  `(x + (1-x) log(1-x)) F_k'` and the left side `x F_k' - k F_k`, and these agree because
  `-(1-x) log(1-x) F_k' = k F_k` (`egfA_first_reverse_column`, `first_reverse_column`).

## Main results

* `first_reverse_row`.
* `X_mul_derivative_egfA`, `natCast_mul_egfA`, `egfA_sub`, `seq_eq_of_egfA_eq`,
  `egfA_stirlingFirst`, `one_sub_X_mul_negLog_mul_derivative_egfA_stirlingFirst`,
  `egfA_kernel`, `egfA_reverse_column`, `egfA_first_reverse_column`, `first_reverse_column`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### The row form -/

section Row

open Polynomial

/-- **Reverse row recurrence of the first kind:**
`(n - k) c(n,k) = ∑_{j=2}^{n-k+1} C(k+j-1, j) c(n, k+j-1)`, written with `j = i + 2`. -/
theorem first_reverse_row (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n - k) * Nat.stirlingFirst n k =
      ∑ i ∈ range (n - k), (k + i + 1).choose (i + 2) * Nat.stirlingFirst n (k + i + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h : Nat.stirlingFirst (n + 1) (m + 1) =
      ∑ r ∈ range (n + 1), r.choose m * Nat.stirlingFirst n r := by
    rw [stirlingFirst_succ_succ_eq_sum_choose]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  rw [Nat.stirlingFirst_succ_succ, ← Nat.Ico_zero_eq_range,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 2)) (by omega : m + 2 ≤ n + 1),
    Nat.Ico_zero_eq_range, Finset.sum_range_succ, Finset.sum_range_succ, Nat.choose_self,
    Nat.choose_succ_self_right, one_mul,
    Finset.sum_eq_zero (fun r hr => by
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hr), zero_mul]), zero_add] at h
  have hrest : ∑ r ∈ Finset.Ico (m + 2) (n + 1), r.choose m * Nat.stirlingFirst n r =
      ∑ i ∈ range (n - (m + 1)),
        (m + 1 + i + 1).choose (i + 2) * Nat.stirlingFirst n (m + 1 + i + 1) := by
    rw [Finset.sum_Ico_eq_sum_range, show n + 1 - (m + 2) = n - (m + 1) by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (m + 2 + i).choose m * Nat.stirlingFirst n (m + 2 + i) = _
    rw [show m + 2 + i = m + (i + 2) by ring, Nat.choose_symm_add,
      show m + (i + 2) = m + 1 + i + 1 by ring]
  rw [hrest] at h
  have hE : n * Nat.stirlingFirst n (m + 1) = (m + 1) * Nat.stirlingFirst n (m + 1) +
      ∑ i ∈ range (n - (m + 1)),
        (m + 1 + i + 1).choose (i + 2) * Nat.stirlingFirst n (m + 1 + i + 1) := by
    linarith [h]
  rw [Nat.sub_mul, hE, Nat.add_sub_cancel_left]

end Row

/-! ### The column form -/

section Column

open PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- `x · d/dx` multiplies the `n`-th entry of the coefficient sequence by `n`. -/
theorem X_mul_derivative_egfA (a : ℕ → A) :
    X * d⁄dX A (egfA A a) = egfA A fun n => (n : A) * a n := by
  ext n
  cases n with
  | zero => rw [coeff_zero_X_mul, coeff_egfA, Nat.cast_zero, zero_mul, mul_zero]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_egfA, coeff_egfA]
    push_cast
    ring

/-- A natural-number scalar acts on the coefficient sequence. -/
theorem natCast_mul_egfA (k : ℕ) (a : ℕ → A) :
    (k : A⟦X⟧) * egfA A a = egfA A fun n => (k : A) * a n := by
  ext n
  rw [← map_natCast (PowerSeries.C : A →+* A⟦X⟧) k, coeff_C_mul, coeff_egfA, coeff_egfA]
  ring

/-- `egfA` is additive. -/
theorem egfA_sub (a b : ℕ → A) : egfA A a - egfA A b = egfA A (a - b) := by
  ext n
  rw [map_sub, coeff_egfA, coeff_egfA, coeff_egfA, Pi.sub_apply, mul_sub]

/-- A sequence is determined by its exponential generating function. -/
theorem seq_eq_of_egfA_eq {a b : ℕ → A} (h : egfA A a = egfA A b) : a = b := by
  funext n
  have hn := congrArg (coeff n) h
  rw [coeff_egfA, coeff_egfA] at hn
  have hu : algebraMap ℚ A (n.factorial : ℚ) * algebraMap ℚ A (1 / n.factorial) = 1 := by
    rw [← map_mul, mul_one_div_cancel (by positivity), map_one]
  calc a n = (algebraMap ℚ A (n.factorial : ℚ) * algebraMap ℚ A (1 / n.factorial)) * a n := by
        rw [hu, one_mul]
    _ = algebraMap ℚ A (n.factorial : ℚ) * (algebraMap ℚ A (1 / n.factorial) * b n) := by
        rw [mul_assoc, hn]
    _ = b n := by rw [← mul_assoc, hu, one_mul]

/-- `F_k = ∑_n c(n,k) x^n/n! = (1/k!) (-log(1-x))^k`, as an `egfA`. -/
theorem egfA_stirlingFirst (k : ℕ) :
    egfA A (fun n => (Nat.stirlingFirst n k : A)) =
      PowerSeries.C (algebraMap ℚ A (1 / k.factorial)) * negLogOneSub A ^ k := by
  rw [← smul_eq_C_mul, ← egf_stirlingFirst, ← egfA_algebraMap]
  congr 1
  funext n
  rw [map_natCast]

/-- `(1-x)·(-log(1-x))·F_{k+1}' = (k+1) F_{k+1}`. -/
theorem one_sub_X_mul_negLog_mul_derivative_egfA_stirlingFirst (k : ℕ) :
    (1 - X) * negLogOneSub A * d⁄dX A (egfA A fun n => (Nat.stirlingFirst n (k + 1) : A)) =
      ((k + 1 : ℕ) : A⟦X⟧) * egfA A fun n => (Nat.stirlingFirst n (k + 1) : A) := by
  rw [egfA_stirlingFirst, Derivation.leibniz, derivative_C, smul_zero, add_zero,
    Derivation.leibniz_pow, Nat.add_sub_cancel]
  simp only [smul_eq_mul, nsmul_eq_mul]
  have hDL := one_sub_X_mul_derivative_negLogOneSub A
  linear_combination (((k + 1 : ℕ) : A⟦X⟧) * PowerSeries.C (algebraMap ℚ A (1 / (k + 1).factorial)) *
    negLogOneSub A ^ (k + 1)) * hDL

/-- The kernel `∑_{j ≥ 2} (j-2)! x^j/j! = ∑_{j ≥ 2} x^j/(j(j-1)) = x + (1-x) log(1-x)`. -/
theorem egfA_kernel :
    egfA A (fun j => if 2 ≤ j then ((j - 2).factorial : A) else 0) =
      X - (1 - X) * negLogOneSub A := by
  ext n
  rw [coeff_egfA, map_sub, sub_mul, one_mul, map_sub, PowerSeries.coeff_X]
  rcases n with _ | _ | m
  · rw [if_neg (by omega), mul_zero, if_neg (by omega), coeff_zero_X_mul, coeff_negLogOneSub,
      if_pos rfl]
    ring
  · rw [if_neg (by omega), mul_zero, if_pos rfl, coeff_succ_X_mul, coeff_negLogOneSub,
      coeff_negLogOneSub, if_neg (by omega), if_pos rfl]
    simp
  · rw [if_pos (by omega), if_neg (by omega), coeff_succ_X_mul, coeff_negLogOneSub,
      coeff_negLogOneSub, if_neg (by omega), if_neg (by omega), show m + 1 + 1 - 2 = m by omega,
      ← map_natCast (algebraMap ℚ A) m.factorial, ← map_mul, ← map_sub, zero_sub, ← map_neg]
    congr 1
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The EGF of `n ↦ ∑_j C(n,j) (j-2)! c(n+1-j, k)` is `(x + (1-x) log(1-x)) F_k'`. -/
theorem egfA_reverse_column (k : ℕ) :
    egfA A (Bell.binomialConv (fun j => if 2 ≤ j then ((j - 2).factorial : A) else 0)
        (fun m => (Nat.stirlingFirst (m + 1) k : A))) =
      (X - (1 - X) * negLogOneSub A) *
        d⁄dX A (egfA A fun n => (Nat.stirlingFirst n k : A)) := by
  rw [← egfA_mul, egfA_kernel, derivative_egfA]
  rfl

/-- **The column identity, as exponential generating functions:** the sequences
`(n - k) c(n,k)` and `∑_j C(n,j) (j-2)! c(n+1-j, k)` have the same EGF (`k ≥ 1`). -/
theorem egfA_first_reverse_column (k : ℕ) :
    egfA A (fun n => ((n : A) - ((k + 1 : ℕ) : A)) * (Nat.stirlingFirst n (k + 1) : A)) =
      egfA A (Bell.binomialConv (fun j => if 2 ≤ j then ((j - 2).factorial : A) else 0)
        (fun m => (Nat.stirlingFirst (m + 1) (k + 1) : A))) := by
  rw [egfA_reverse_column, sub_mul, one_sub_X_mul_negLog_mul_derivative_egfA_stirlingFirst,
    X_mul_derivative_egfA, natCast_mul_egfA, egfA_sub]
  congr 1
  funext n
  rw [Pi.sub_apply]
  ring

/-- **Reverse column recurrence of the first kind:**
`(n - k) c(n,k) = ∑_{j=2}^{n} C(n,j) (j-2)! c(n-j+1, k)` (the terms with `j < 2` are zero, and
those with `j > n-k+1` vanish because `c(n-j+1,k) = 0`). -/
theorem first_reverse_column (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n - k) * Nat.stirlingFirst n k =
      ∑ j ∈ range (n + 1),
        n.choose j * ((if 2 ≤ j then (j - 2).factorial else 0) * Nat.stirlingFirst (n - j + 1) k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h := congrFun (seq_eq_of_egfA_eq ℚ (egfA_first_reverse_column ℚ m)) n
  simp only [Bell.binomialConv_eq_sum_range] at h
  apply Nat.cast_injective (R := ℚ)
  push_cast [Nat.cast_sub hkn] at h ⊢
  linear_combination h

end Column

end Fabius
