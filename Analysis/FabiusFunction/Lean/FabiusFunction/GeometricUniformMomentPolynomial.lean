import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Geometric-uniform moment polynomials

This file isolates the algebraic recursion for the moment polynomials from the
geometric-uniform model.  It proves the recurrence, the triangular degree
bound, the value at zero, and the first four nonconstant examples.

The identification of this recursive family with coefficients of the analytic
moment-generating product is deliberately not made here.  Likewise, the sharp
leading- and subleading-degree statements require additional input and are out
of scope for this base module.

## Main declarations

* `geometricUniformMomentPolynomial`: the recursively defined polynomial family.
* `geometricUniformMomentPolynomial_succ`: its residual-product recurrence.
* `geometricUniformMomentPolynomial_natDegree_le`: the triangular degree bound.
* `geometricUniformMomentPolynomial_eval_zero`: its factorial value at zero.
* `geometricUniformMomentPolynomial_one` through
  `geometricUniformMomentPolynomial_four`: the first explicit values.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Polynomial

namespace Fabius

noncomputable section

/-- The geometric-uniform moment-polynomial recursion over `ℚ`.

The finite product is the division-free residual `q`-Pochhammer factor
`∏_{j=k+1}^{n} (1 - X^j)`.  The guard exposes the strict decrease required
by course-of-values recursion; on the summation range it is automatically true.
-/
noncomputable def geometricUniformMomentPolynomial : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 =>
      ∑ k ∈ range (n + 1),
        if hk : k < n + 1 then
          C (((n - k + 2).factorial : ℚ)⁻¹) *
            (X ^ k *
              ((∏ j ∈ Ico (k + 1) (n + 1), (1 - X ^ j : ℚ[X])) *
                geometricUniformMomentPolynomial k))
        else 0
termination_by n => n
decreasing_by omega

/-- The zeroth geometric-uniform moment polynomial is one. -/
@[simp] theorem geometricUniformMomentPolynomial_zero :
    geometricUniformMomentPolynomial 0 = 1 := by
  rw [geometricUniformMomentPolynomial]

/-- The division-free residual-product recurrence for the polynomial family. -/
theorem geometricUniformMomentPolynomial_succ (n : ℕ) :
    geometricUniformMomentPolynomial (n + 1) =
      ∑ k ∈ range (n + 1),
        C (((n - k + 2).factorial : ℚ)⁻¹) *
          (X ^ k *
            ((∏ j ∈ Ico (k + 1) (n + 1), (1 - X ^ j : ℚ[X])) *
              geometricUniformMomentPolynomial k)) := by
  rw [geometricUniformMomentPolynomial]
  refine sum_congr rfl fun k hk => ?_
  simp [mem_range.mp hk]

/-- At `X = 0`, every residual `q`-Pochhammer factor evaluates to one. -/
private theorem eval_residualGeometricUniformMomentPolynomial_zero (k n : ℕ) :
    eval 0 (∏ j ∈ Ico (k + 1) n, (1 - X ^ j : ℚ[X])) = 1 := by
  rw [eval_prod]
  refine prod_eq_one fun j hj => ?_
  have hjpos : 0 < j := by
    have := (mem_Ico.mp hj).1
    omega
  simp [hjpos.ne']

/-- The residual product has degree at most the sum of its exponents. -/
private theorem natDegree_residualGeometricUniformMomentPolynomial_le (k n : ℕ) :
    (∏ j ∈ Ico (k + 1) n, (1 - X ^ j : ℚ[X])).natDegree ≤
      ∑ j ∈ Ico (k + 1) n, j := by
  refine (natDegree_prod_le _ _).trans ?_
  refine sum_le_sum fun j _ => ?_
  exact (natDegree_sub_le _ _).trans
    (max_le (by simp) (natDegree_X_pow_le j))

/-- The degree of `P_n` is at most the triangular number `choose n 2`. -/
theorem geometricUniformMomentPolynomial_natDegree_le (n : ℕ) :
    (geometricUniformMomentPolynomial n).natDegree ≤ n.choose 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [geometricUniformMomentPolynomial_succ]
          refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
          have hklt : k < n + 1 := mem_range.mp hk
          have hPk : (geometricUniformMomentPolynomial k).natDegree ≤ k.choose 2 := ih k hklt
          have hres := natDegree_residualGeometricUniformMomentPolynomial_le k (n + 1)
          have hsplit :
              (∑ j ∈ range (k + 1), j) + ∑ j ∈ Ico (k + 1) (n + 1), j =
                ∑ j ∈ range (n + 1), j :=
            sum_range_add_sum_Ico (fun j => j) (by omega)
          have hkchoose : k + k.choose 2 = (k + 1).choose 2 := by
            rw [Nat.choose_succ_succ]
            simp
          have hsplit' :
              (k + 1).choose 2 + ∑ j ∈ Ico (k + 1) (n + 1), j =
                (n + 1).choose 2 := by
            simpa [sum_range_id, Nat.choose_two_right] using hsplit
          calc
            (C (((n - k + 2).factorial : ℚ)⁻¹) *
                (X ^ k *
                  ((∏ j ∈ Ico (k + 1) (n + 1), (1 - X ^ j : ℚ[X])) *
                    geometricUniformMomentPolynomial k))).natDegree
                ≤ (X ^ k *
                    ((∏ j ∈ Ico (k + 1) (n + 1), (1 - X ^ j : ℚ[X])) *
                      geometricUniformMomentPolynomial k)).natDegree := natDegree_C_mul_le _ _
            _ ≤ (X ^ k).natDegree +
                  ((∏ j ∈ Ico (k + 1) (n + 1), (1 - X ^ j : ℚ[X])) *
                    geometricUniformMomentPolynomial k).natDegree := natDegree_mul_le
            _ ≤ k +
                  ((∏ j ∈ Ico (k + 1) (n + 1), (1 - X ^ j : ℚ[X])).natDegree +
                    (geometricUniformMomentPolynomial k).natDegree) :=
              Nat.add_le_add (natDegree_X_pow_le k) natDegree_mul_le
            _ ≤ k + ((∑ j ∈ Ico (k + 1) (n + 1), j) + k.choose 2) :=
              Nat.add_le_add_left (Nat.add_le_add hres hPk) k
            _ = (n + 1).choose 2 := by
              calc
                k + ((∑ j ∈ Ico (k + 1) (n + 1), j) + k.choose 2) =
                    (k + k.choose 2) + ∑ j ∈ Ico (k + 1) (n + 1), j := by omega
                _ = (k + 1).choose 2 + ∑ j ∈ Ico (k + 1) (n + 1), j := by
                  rw [hkchoose]
                _ = (n + 1).choose 2 := hsplit'

/-- The specialization at zero is `P_n(0) = 1 / (n+1)!`. -/
@[simp] theorem geometricUniformMomentPolynomial_eval_zero (n : ℕ) :
    eval 0 (geometricUniformMomentPolynomial n) = (((n + 1).factorial : ℚ)⁻¹) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [geometricUniformMomentPolynomial_succ, eval_finsetSum]
      rw [sum_eq_single 0]
      · simp [eval_residualGeometricUniformMomentPolynomial_zero]
      · intro k hk hk0
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        simp [hkpos.ne']
      · simp

/-- The first geometric-uniform moment polynomial is `1/2`. -/
@[simp] theorem geometricUniformMomentPolynomial_one :
    geometricUniformMomentPolynomial 1 = C (1 / 2 : ℚ) := by
  rw [geometricUniformMomentPolynomial_succ 0]
  norm_num [sum_range_succ, Finset.prod_Ico_eq_prod_range, Nat.factorial,
    geometricUniformMomentPolynomial_zero]

/-- The second geometric-uniform moment polynomial is `(X + 2)/12`. -/
@[simp] theorem geometricUniformMomentPolynomial_two :
    geometricUniformMomentPolynomial 2 = C (1 / 12 : ℚ) * (X + 2) := by
  rw [geometricUniformMomentPolynomial_succ 1]
  norm_num [sum_range_succ, Finset.prod_Ico_eq_prod_range, prod_range_succ, Nat.factorial,
    geometricUniformMomentPolynomial_zero,
    geometricUniformMomentPolynomial_one]
  simp only [← C_mul]
  norm_num
  ring_nf
  simp only [pow_two, ← C_mul]
  norm_num
  have h6 : (C (1 / 6 : ℚ) : ℚ[X]) = 2 * C (1 / 12 : ℚ) := by
    change C (1 / 6 : ℚ) = C (2 : ℚ) * C (1 / 12 : ℚ)
    rw [← C_mul]
    norm_num
  have h4 : (C (1 / 4 : ℚ) : ℚ[X]) = 3 * C (1 / 12 : ℚ) := by
    change C (1 / 4 : ℚ) = C (3 : ℚ) * C (1 / 12 : ℚ)
    rw [← C_mul]
    norm_num
  rw [h6, h4]
  ring

/-- The third geometric-uniform moment polynomial is `(X² + X + 1)/24`. -/
@[simp] theorem geometricUniformMomentPolynomial_three :
    geometricUniformMomentPolynomial 3 = C (1 / 24 : ℚ) * (X ^ 2 + X + 1) := by
  rw [geometricUniformMomentPolynomial_succ 2]
  norm_num [sum_range_succ, Finset.prod_Ico_eq_prod_range, prod_range_succ, Nat.factorial,
    geometricUniformMomentPolynomial_zero,
    geometricUniformMomentPolynomial_one, geometricUniformMomentPolynomial_two]
  simp only [← C_mul]
  norm_num
  ring_nf
  simp only [pow_two, mul_assoc, ← C_mul]
  norm_num
  have h12 : (C (1 / 12 : ℚ) : ℚ[X]) = 2 * C (1 / 24 : ℚ) := by
    change C (1 / 12 : ℚ) = C (2 : ℚ) * C (1 / 24 : ℚ)
    rw [← C_mul]
    norm_num
  rw [h12]
  ring

/-- The fourth geometric-uniform moment polynomial in factored form. -/
@[simp] theorem geometricUniformMomentPolynomial_four :
    geometricUniformMomentPolynomial 4 =
      C (1 / 720 : ℚ) * (X ^ 2 + X + 1) *
        (6 + 3 * X + 5 * X ^ 2 + 2 * X ^ 3 - X ^ 4) := by
  rw [geometricUniformMomentPolynomial_succ 3]
  norm_num [sum_range_succ, Finset.prod_Ico_eq_prod_range, prod_range_succ, Nat.factorial,
    geometricUniformMomentPolynomial_zero,
    geometricUniformMomentPolynomial_one, geometricUniformMomentPolynomial_two,
    geometricUniformMomentPolynomial_three]
  simp only [← C_mul]
  norm_num
  ring_nf
  simp only [pow_two, mul_assoc, ← C_mul]
  norm_num
  have h120 : (C (1 / 120 : ℚ) : ℚ[X]) = 6 * C (1 / 720 : ℚ) := by
    change C (1 / 120 : ℚ) = C (6 : ℚ) * C (1 / 720 : ℚ)
    rw [← C_mul]
    norm_num
  have h48 : (C (1 / 48 : ℚ) : ℚ[X]) = 15 * C (1 / 720 : ℚ) := by
    change C (1 / 48 : ℚ) = C (15 : ℚ) * C (1 / 720 : ℚ)
    rw [← C_mul]
    norm_num
  have h72 : (C (1 / 72 : ℚ) : ℚ[X]) = 10 * C (1 / 720 : ℚ) := by
    change C (1 / 72 : ℚ) = C (10 : ℚ) * C (1 / 720 : ℚ)
    rw [← C_mul]
    norm_num
  rw [h120, h48, h72]
  ring

end

end Fabius
