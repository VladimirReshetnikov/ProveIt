import FabiusFunction.BernoulliStirling

/-!
# Homogeneity of Bell polynomials and the Touchard polynomials

The partial Bell polynomial `B_{n,k}(x_1, x_2, …)` is homogeneous of degree
`k` in the weights and of weighted degree `n` when `x_j` carries weight `j`:

`B_{n,k}(α β x_1, α β² x_2, …) = α^k β^n B_{n,k}(x_1, x_2, …)`.

Both facts follow by induction from the pointing recurrence, over any
commutative semiring.  Specializing all weights to one scalar `x` gives the
Touchard polynomials: `B_n(x, x, …) = ∑_k S(n,k) x^k = T_n(x)`, whose
exponential generating function is therefore `exp(x (e^t - 1))`.

## Main results

* `partialBell_mul_left`, `partialBell_pow_mul`, `partialBell_bihomogeneous`.
* `bell_complete_const`, `bell_complete_const_eq_touchard_eval`.
* `bellWeightSeries_const`, `exp_subst_smul_exp_sub_one`.
-/

set_option autoImplicit false

open Finset Polynomial PowerSeries

namespace Fabius

section Homogeneity

variable {R : Type*} [CommSemiring R]

/-- Degree homogeneity: `B_{n,k}(c x_1, c x_2, …) = c^k B_{n,k}(x)`. -/
theorem partialBell_mul_left (c : R) (x : ℕ → R) (n k : ℕ) :
    partialBell (fun j => c * x j) n k = c ^ k * partialBell x n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      cases k with
      | zero => simp
      | succ k => simp
    | succ n =>
      cases k with
      | zero => simp
      | succ k =>
        rw [partialBell_succ_succ, partialBell_succ_succ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [ih (n - i) (by omega) k]
        ring

/-- Weighted homogeneity: `B_{n,k}(c x_1, c² x_2, c³ x_3, …) = c^n B_{n,k}(x)`. -/
theorem partialBell_pow_mul (c : R) (x : ℕ → R) (n k : ℕ) :
    partialBell (fun j => c ^ j * x j) n k = c ^ n * partialBell x n k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      cases k with
      | zero => simp
      | succ k => simp
    | succ n =>
      cases k with
      | zero => simp
      | succ k =>
        rw [partialBell_succ_succ, partialBell_succ_succ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [ih (n - i) (by omega) k]
        have hpow : c ^ (i + 1) * c ^ (n - i) = c ^ (n + 1) := by
          rw [← pow_add]
          congr 1
          omega
        calc (n.choose i : R) * (c ^ (i + 1) * x (i + 1) * (c ^ (n - i) * partialBell x (n - i) k))
            = (c ^ (i + 1) * c ^ (n - i)) *
                ((n.choose i : R) * (x (i + 1) * partialBell x (n - i) k)) := by ring
          _ = _ := by rw [hpow]

/-- **Bigraded homogeneity:** `B_{n,k}(α β x_1, α β² x_2, …) = α^k β^n B_{n,k}(x)`. -/
theorem partialBell_bihomogeneous (a b : R) (x : ℕ → R) (n k : ℕ) :
    partialBell (fun j => a * b ^ j * x j) n k = a ^ k * b ^ n * partialBell x n k := by
  have h1 : (fun j => a * b ^ j * x j) = fun j => a * (b ^ j * x j) := by
    funext j
    ring
  rw [h1, partialBell_mul_left, partialBell_pow_mul, mul_assoc]

end Homogeneity

/-! ### Touchard polynomials as complete Bell polynomials -/

section Touchard

variable {R : Type*} [CommRing R]

/-- `B_n(x, x, x, …) = ∑_{k ≤ n} S(n,k) x^k`. -/
theorem bell_complete_const (x : R) (n : ℕ) :
    Bell.complete (fun _ => x) n = ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : R) * x ^ k := by
  rw [bell_complete_eq_sum_partialBell]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (fun _ : ℕ => x) = fun _ : ℕ => x * (1 : R) := by
    funext _
    ring
  rw [h, partialBell_mul_left, partialBell_one_cast, mul_comm]

/-- The complete Bell polynomial at constant weights is the Touchard polynomial. -/
theorem bell_complete_const_eq_touchard_eval (x : R) (n : ℕ) :
    Bell.complete (fun _ => x) n = (touchardPolynomial R n).eval x := by
  rw [bell_complete_const, touchardPolynomial, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

end Touchard

section TouchardEGF

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The weight series of constant weights `x` is `x (e^t - 1)`. -/
theorem bellWeightSeries_const (x : A) :
    bellWeightSeries A (fun _ => x) = x • (exp A - 1) := by
  ext n
  rw [bellWeightSeries, coeff_egfA, PowerSeries.coeff_smul, map_sub, PowerSeries.coeff_exp, PowerSeries.coeff_one, smul_eq_mul]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_ne_zero, if_false, sub_zero]
    ring

/-- **The Touchard generating function:** `exp(x (e^t - 1)) = ∑_n T_n(x) t^n/n!`. -/
theorem exp_subst_smul_exp_sub_one (x : A) :
    (exp A).subst (x • (exp A - 1)) =
      egfA A fun n => ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : A) * x ^ k := by
  rw [← bellWeightSeries_const, exp_subst_bellWeightSeries]
  congr 1
  funext n
  exact bell_complete_const x n

end TouchardEGF

end Fabius
