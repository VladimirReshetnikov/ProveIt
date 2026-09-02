import FabiusFunction.BellGeneratingFunctions

/-!
# Composition of exponential generating functions and the Bell transform

The **exponential composition theorem** (the formal Faà di Bruno formula):
if `B(t) = ∑_k b_k t^k/k!` and `X(t) = ∑_{j ≥ 1} x_j t^j/j!`, then

`B(X(t)) = ∑_n (∑_{k ≤ n} b_k B_{n,k}(x)) t^n/n!`,

read off from the partial Bell column theorem, since substitution acts on
coefficients through the powers `X(t)^k`.  Consequences:

* the block-colour convolution
  `(k₁+k₂)! B_{n,k₁+k₂} = k₁! k₂! ∑_i C(n,i) B_{i,k₁} B_{n-i,k₂}`;
* `log(1 + (e^t - 1)) = t` as a substitution of formal power series;
* the **Bell transform inverse**: if `y_n = B_n(x)` are the complete Bell
  polynomials of `x` then `x_n = ∑_{k=1}^{n} (-1)^{k-1} (k-1)! B_{n,k}(y)`,
  because `X(t) = log(1 + Y(t))` and `log(1+u) = ∑_k (-1)^{k-1} (k-1)! u^k/k!`.

Everything is over an arbitrary commutative `ℚ`-algebra.

## Main results

* `coeff_bellWeightSeries_pow`, `egfA_subst_bellWeightSeries`.
* `factorial_mul_partialBell_add`.
* `one_add_X_mul_mk_neg_one_pow`, `log_subst_exp_sub_one`, `log_eq_egfA`.
* `egfA_bell_complete_sub_one`, `bell_transform_inverse`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Composition

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The coefficients of `X(t)^k`: `[t^n/n!] X(t)^k = k! B_{n,k}(x)`. -/
theorem coeff_bellWeightSeries_pow (x : ℕ → A) (k n : ℕ) :
    coeff n (bellWeightSeries A x ^ k) =
      (k.factorial : A) * (algebraMap ℚ A (1 / n.factorial) * partialBell x n k) := by
  rw [bellWeightSeries_pow, coeff_smul, coeff_egfA, smul_eq_mul]

/-- `X(t)^k` has no terms of degree below `k`. -/
theorem coeff_bellWeightSeries_pow_eq_zero_of_lt (x : ℕ → A) {n k : ℕ} (h : n < k) :
    coeff n (bellWeightSeries A x ^ k) = 0 := by
  rw [coeff_bellWeightSeries_pow, partialBell_eq_zero_of_lt x h, mul_zero, mul_zero]

/-- **Exponential composition (formal Faà di Bruno):**
`(∑_k b_k t^k/k!) ∘ X(t) = ∑_n (∑_{k ≤ n} b_k B_{n,k}(x)) t^n/n!`. -/
theorem egfA_subst_bellWeightSeries (b x : ℕ → A) :
    (egfA A b).subst (bellWeightSeries A x) =
      egfA A fun n => ∑ k ∈ Finset.range (n + 1), b k * partialBell x n k := by
  have hW : HasSubst (bellWeightSeries A x) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_bellWeightSeries A x)
  ext n
  have hsupp : Function.support
      (fun d : ℕ => coeff d (egfA A b) • PowerSeries.coeff n (bellWeightSeries A x ^ d)) ⊆
        ↑(Finset.range (n + 1)) := by
    intro k hk
    rw [Function.mem_support] at hk
    by_contra hkn
    apply hk
    rw [Finset.mem_coe, Finset.mem_range, not_lt] at hkn
    rw [coeff_bellWeightSeries_pow_eq_zero_of_lt A x (show n < k by omega), smul_zero]
  rw [coeff_subst' hW, coeff_egfA, finsum_eq_sum_of_support_subset _ hsupp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_egfA, coeff_bellWeightSeries_pow, smul_eq_mul]
  have hk : algebraMap ℚ A (1 / k.factorial) * (k.factorial : A) = 1 := by
    rw [show (k.factorial : A) = algebraMap ℚ A (k.factorial : ℚ) by simp, ← map_mul,
      one_div_mul_cancel (by positivity), map_one]
  calc algebraMap ℚ A (1 / k.factorial) * b k *
        ((k.factorial : A) * (algebraMap ℚ A (1 / n.factorial) * partialBell x n k))
      = (algebraMap ℚ A (1 / k.factorial) * (k.factorial : A)) *
          (algebraMap ℚ A (1 / n.factorial) * (b k * partialBell x n k)) := by ring
    _ = _ := by rw [hk, one_mul]

/-- **Block-colour convolution:**
`(k₁+k₂)! B_{n,k₁+k₂}(x) = k₁! k₂! ∑_{i ≤ n} C(n,i) B_{i,k₁}(x) B_{n-i,k₂}(x)`. -/
theorem factorial_mul_partialBell_add (x : ℕ → A) (k₁ k₂ n : ℕ) :
    ((k₁ + k₂).factorial : A) * partialBell x n (k₁ + k₂) =
      (k₁.factorial : A) * k₂.factorial *
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : A) * (partialBell x i k₁ * partialBell x (n - i) k₂) := by
  have h := congrArg (coeff n) (pow_add (bellWeightSeries A x) k₁ k₂)
  rw [coeff_bellWeightSeries_pow, bellWeightSeries_pow, bellWeightSeries_pow, smul_mul_assoc,
    mul_smul_comm, smul_smul, egfA_mul, coeff_smul, coeff_egfA, smul_eq_mul,
    Bell.binomialConv_eq_sum_range] at h
  have hinv : algebraMap ℚ A (n.factorial) * algebraMap ℚ A (1 / n.factorial) = 1 := by
    rw [← map_mul, mul_one_div_cancel (by positivity), map_one]
  calc ((k₁ + k₂).factorial : A) * partialBell x n (k₁ + k₂)
      = algebraMap ℚ A (n.factorial) *
          (((k₁ + k₂).factorial : A) * (algebraMap ℚ A (1 / n.factorial) * partialBell x n (k₁ + k₂))) := by
        calc ((k₁ + k₂).factorial : A) * partialBell x n (k₁ + k₂)
            = ((k₁ + k₂).factorial : A) * partialBell x n (k₁ + k₂) *
                (algebraMap ℚ A (n.factorial) * algebraMap ℚ A (1 / n.factorial)) := by
              rw [hinv, mul_one]
          _ = _ := by ring
    _ = algebraMap ℚ A (n.factorial) * ((k₁.factorial : A) * k₂.factorial *
          (algebraMap ℚ A (1 / n.factorial) *
            ∑ i ∈ Finset.range (n + 1),
              (n.choose i : A) * (partialBell x i k₁ * partialBell x (n - i) k₂))) := by
        rw [h]
    _ = (k₁.factorial : A) * k₂.factorial *
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i : A) * (partialBell x i k₁ * partialBell x (n - i) k₂)) *
          (algebraMap ℚ A (n.factorial) * algebraMap ℚ A (1 / n.factorial)) := by ring
    _ = _ := by rw [hinv, mul_one]

/-! ### `log(1 + (e^t - 1)) = t` -/

/-- `(1 + t) · ∑_n (-1)^n t^n = 1`. -/
theorem one_add_X_mul_mk_neg_one_pow :
    ((1 : A⟦X⟧) + X) * PowerSeries.mk (fun n => algebraMap ℚ A ((-1 : ℚ) ^ n)) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_mk, coeff_one]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_mk, if_neg (Nat.succ_ne_zero n), pow_succ, map_mul, map_neg,
      map_one, mul_neg, mul_one, neg_add_cancel]

/-- `log(1 + (e^t - 1)) = t`, as a substitution of formal power series. -/
theorem log_subst_exp_sub_one : (log A).subst (exp A - 1) = X := by
  haveI : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  have hE : HasSubst (exp A - 1) := HasSubst.exp_sub_one
  have h1 : (1 : A⟦X⟧).subst (exp A - 1) = 1 := by
    rw [← coe_substAlgHom hE]
    exact map_one _
  apply derivative.ext
  · rw [derivative_subst A hE, deriv_log, derivative_X, map_sub, derivative_exp,
      Derivation.map_one_eq_zero, sub_zero]
    have h := congrArg (fun p : A⟦X⟧ => PowerSeries.subst (exp A - 1) p)
      (one_add_X_mul_mk_neg_one_pow A)
    have hsum : (1 : A⟦X⟧) + (exp A - 1) = exp A := by ring
    rw [subst_mul hE, subst_add hE, subst_X hE, h1, hsum] at h
    rw [mul_comm]
    exact h
  · rw [constantCoeff_subst_of_constantCoeff_eq_zero A (by simp [constantCoeff_exp]),
      constantCoeff_log, constantCoeff_X]

/-- `log(1+t)` as an exponential generating function: its coefficients
`[t^k/k!] log(1+t) = (-1)^{k+1} (k-1)!` for `k ≥ 1`. -/
theorem log_eq_egfA :
    log A = egfA A fun k =>
      if k = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (k + 1) * (k - 1).factorial) := by
  ext k
  rw [coeff_log, coeff_egfA]
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [← map_mul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    have hk : (k.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    try ring

/-- The generating function of the complete Bell polynomials minus one is the
weight series of the sequence of complete Bell polynomials. -/
theorem egfA_bell_complete_sub_one (x : ℕ → A) :
    egfA A (Bell.complete x) - 1 = bellWeightSeries A (Bell.complete x) := by
  ext n
  rw [map_sub, coeff_egfA, coeff_one, bellWeightSeries, coeff_egfA]
  cases n with
  | zero => simp
  | succ n => simp

/-- **The Bell transform inverse:** if `y_n = B_n(x)` (complete Bell
polynomials), then for `n ≥ 1`

`x_n = ∑_{k=1}^{n} (-1)^{k-1} (k-1)! B_{n,k}(y_1, y_2, …)`. -/
theorem bell_transform_inverse (x : ℕ → A) (n : ℕ) (hn : 1 ≤ n) :
    x n = ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (k + 1) * (k - 1).factorial)) *
        partialBell (Bell.complete x) n k := by
  have hW : HasSubst (bellWeightSeries A x) :=
    HasSubst.of_constantCoeff_zero' (constantCoeff_bellWeightSeries A x)
  have hE : HasSubst (exp A - 1) := HasSubst.exp_sub_one
  have h1 : (1 : A⟦X⟧).subst (bellWeightSeries A x) = 1 := by
    rw [← coe_substAlgHom hW]
    exact map_one _
  have key : bellWeightSeries A x = egfA A fun n => ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (k + 1) * (k - 1).factorial)) *
        partialBell (Bell.complete x) n k := by
    calc bellWeightSeries A x
        = PowerSeries.subst (bellWeightSeries A x) (PowerSeries.X : A⟦X⟧) := (subst_X hW).symm
      _ = PowerSeries.subst (bellWeightSeries A x) (PowerSeries.subst (exp A - 1) (log A)) := by
          rw [log_subst_exp_sub_one]
      _ = PowerSeries.subst (PowerSeries.subst (bellWeightSeries A x) (exp A - 1)) (log A) :=
          subst_comp_subst_apply hE hW (log A)
      _ = PowerSeries.subst (bellWeightSeries A (Bell.complete x)) (log A) := by
          rw [subst_sub hW, exp_subst_bellWeightSeries, h1, egfA_bell_complete_sub_one]
      _ = _ := by rw [log_eq_egfA, egfA_subst_bellWeightSeries]
  have hc := congrArg (coeff n) key
  rw [bellWeightSeries, coeff_egfA, coeff_egfA, if_neg (by omega)] at hc
  have hinv : algebraMap ℚ A (n.factorial) * algebraMap ℚ A (1 / n.factorial) = 1 := by
    rw [← map_mul, mul_one_div_cancel (by positivity), map_one]
  calc x n = (algebraMap ℚ A (n.factorial) * algebraMap ℚ A (1 / n.factorial)) * x n := by
        rw [hinv, one_mul]
    _ = algebraMap ℚ A (n.factorial) * (algebraMap ℚ A (1 / n.factorial) * x n) := by ring
    _ = algebraMap ℚ A (n.factorial) * (algebraMap ℚ A (1 / n.factorial) *
          ∑ k ∈ Finset.range (n + 1),
            (if k = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (k + 1) * (k - 1).factorial)) *
              partialBell (Bell.complete x) n k) := by rw [hc]
    _ = (algebraMap ℚ A (n.factorial) * algebraMap ℚ A (1 / n.factorial)) *
          ∑ k ∈ Finset.range (n + 1),
            (if k = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (k + 1) * (k - 1).factorial)) *
              partialBell (Bell.complete x) n k := by ring
    _ = _ := by rw [hinv, one_mul]

end Composition

end Fabius
