import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The numerator family of the `x + W(x)` inverse coefficients

The Lambert-inverse transseries drafts write the derivatives of the powers of
`W` in the closed form

`(d/dz)^k v^n = z^{-k} · v^n R_{n,k}(v) / (1 + v)^{2k-1}`,   `k ≥ 1`,

with `R_{n,1} = n` and the two-index recurrence

`R_{n,k+1} = v(1+v) R'_{n,k} + (n(1+v) - (2k-1)v - k(1+v)^2) R_{n,k}`,

and read the structure of the inverse coefficients off it:
`A_m(v) = (-1)^{m+1} v^{m+1} R_{m+1,m}(v) / ((m+1)! (1+v)^{2m-1})`, so that
`P_m = (-1)^{m+1} R_{m+1,m} / (m+1)` carries the whole content of the drafts'
`prop:Pm-structure` and `prop:A-shape`.

This module formalizes that family and its extremal data, purely as algebra
over `ℤ[X]` — no transseries, no analysis.  Indices are shifted by one so the
recursion starts at `0`: `lambertNumerator n j` is the drafts' `R_{n,j+1}`.

## Main results

* `lambertNumerator_succ_eq_draft`: the recursion is the drafts' recurrence.
* `natDegree_lambertNumerator`: `deg R_{n,k} = 2(k-1)`.
* `leadingCoeff_lambertNumerator`: `[v^{2(k-1)}] R_{n,k} = n(-1)^{k-1}(k-1)!`.
* `eval_zero_lambertNumerator`: `R_{n,k}(0) = n(n-1)⋯(n-k+1)`.
* `natCast_dvd_lambertNumerator`: `R_{n,k} ∈ nℤ[v]`, the integrality the drafts
  use to make `P_m` an integer polynomial.

The identification of this family with the analytic coefficients `A_m`, which
needs the operator calculus on functions, is not formalized here.
-/

set_option autoImplicit false

open Polynomial Finset

namespace Fabius

/-- The quadratic multiplier of the recurrence, in expanded form:
`n(1+v) - (2k-1)v - k(1+v)^2` at `k = j+1`. -/
noncomputable def lambertMultiplier (n j : ℕ) : ℤ[X] :=
  C (-((j : ℤ) + 1)) * X ^ 2 + C ((n : ℤ) - 4 * j - 3) * X + C ((n : ℤ) - j - 1)

/-- The multiplier is the drafts' expression. -/
theorem lambertMultiplier_eq (n j : ℕ) :
    lambertMultiplier n j =
      C (n : ℤ) * (1 + X) - C (2 * (j : ℤ) + 1) * X - C ((j : ℤ) + 1) * (1 + X) ^ 2 := by
  unfold lambertMultiplier
  simp only [C_sub, C_add, C_mul, C_neg, C_1, map_ofNat]
  ring

theorem natDegree_lambertMultiplier (n j : ℕ) :
    (lambertMultiplier n j).natDegree = 2 :=
  natDegree_quadratic (by positivity)

theorem leadingCoeff_lambertMultiplier (n j : ℕ) :
    (lambertMultiplier n j).leadingCoeff = -((j : ℤ) + 1) :=
  leadingCoeff_quadratic (by positivity)

/-- `lambertNumerator n j` is the drafts' `R_{n, j+1}`. -/
noncomputable def lambertNumerator (n : ℕ) : ℕ → ℤ[X]
  | 0 => C (n : ℤ)
  | (j + 1) => X * (1 + X) * derivative (lambertNumerator n j)
      + lambertMultiplier n j * lambertNumerator n j

@[simp] theorem lambertNumerator_zero (n : ℕ) : lambertNumerator n 0 = C (n : ℤ) := rfl

theorem lambertNumerator_succ (n j : ℕ) :
    lambertNumerator n (j + 1) = X * (1 + X) * derivative (lambertNumerator n j)
      + lambertMultiplier n j * lambertNumerator n j := rfl

/-- The recursion written as the drafts write it. -/
theorem lambertNumerator_succ_eq_draft (n j : ℕ) :
    lambertNumerator n (j + 1) = X * (1 + X) * derivative (lambertNumerator n j)
      + (C (n : ℤ) * (1 + X) - C (2 * (j : ℤ) + 1) * X - C ((j : ℤ) + 1) * (1 + X) ^ 2)
        * lambertNumerator n j := by
  rw [lambertNumerator_succ, lambertMultiplier_eq]

/-- **Degree and leading coefficient.**  For `n ≥ 1`, `R_{n,j+1}` has degree `2j`
and leading coefficient `n(-1)^j j!`. -/
theorem natDegree_and_leadingCoeff_lambertNumerator {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    (lambertNumerator n j).natDegree = 2 * j ∧
      (lambertNumerator n j).leadingCoeff = (n : ℤ) * (-1) ^ j * (j ! : ℤ) := by
  induction j with
  | zero =>
      refine ⟨by simp, ?_⟩
      simp [lambertNumerator_zero, leadingCoeff_C]
  | succ j ih =>
      obtain ⟨hdeg, hlead⟩ := ih
      have hne : lambertNumerator n j ≠ 0 := by
        intro h
        rw [h, leadingCoeff_zero] at hlead
        have : (n : ℤ) * (-1) ^ j * (j ! : ℤ) ≠ 0 := by
          have h1 : (n : ℤ) ≠ 0 := by exact_mod_cast hn
          have h2 : ((j ! : ℕ) : ℤ) ≠ 0 := by
            exact_mod_cast (Nat.factorial_pos j).ne'
          exact mul_ne_zero (mul_ne_zero h1 (pow_ne_zero _ (by norm_num))) h2
        exact this hlead.symm
      -- the multiplier term carries the top degree
      have hmul : (lambertMultiplier n j * lambertNumerator n j).natDegree = 2 * j + 2 := by
        rw [natDegree_mul' , natDegree_lambertMultiplier, hdeg]
        · ring
        · rw [leadingCoeff_lambertMultiplier, hlead]
          have h1 : (n : ℤ) ≠ 0 := by exact_mod_cast hn
          have h2 : ((j ! : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
          have h3 : -((j : ℤ) + 1) ≠ 0 := by positivity
          exact mul_ne_zero h3 (mul_ne_zero (mul_ne_zero h1 (pow_ne_zero _ (by norm_num))) h2)
      have hmullead : (lambertMultiplier n j * lambertNumerator n j).leadingCoeff
          = -((j : ℤ) + 1) * ((n : ℤ) * (-1) ^ j * (j ! : ℤ)) := by
        rw [leadingCoeff_mul' , leadingCoeff_lambertMultiplier, hlead]
        rw [leadingCoeff_lambertMultiplier, hlead]
        have h1 : (n : ℤ) ≠ 0 := by exact_mod_cast hn
        have h2 : ((j ! : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
        have h3 : -((j : ℤ) + 1) ≠ 0 := by positivity
        exact mul_ne_zero h3 (mul_ne_zero (mul_ne_zero h1 (pow_ne_zero _ (by norm_num))) h2)
      -- the derivative term is of strictly smaller degree
      have hderiv : (X * (1 + X) * derivative (lambertNumerator n j)).natDegree < 2 * j + 2 := by
        have hd : (derivative (lambertNumerator n j)).natDegree ≤ 2 * j - 1 := by
          have := natDegree_derivative_le (lambertNumerator n j)
          omega_nat <;> simp [hdeg] at this ⊢
        calc (X * (1 + X) * derivative (lambertNumerator n j)).natDegree
            ≤ (X * (1 + X)).natDegree + (derivative (lambertNumerator n j)).natDegree :=
              natDegree_mul_le
          _ ≤ 2 + (2 * j - 1) := by
              have hx : (X * (1 + X) : ℤ[X]).natDegree ≤ 2 := by
                calc (X * (1 + X) : ℤ[X]).natDegree ≤ (X : ℤ[X]).natDegree + (1 + X : ℤ[X]).natDegree :=
                      natDegree_mul_le
                  _ ≤ 1 + 1 := by
                      gcongr
                      · simp
                      · simpa using natDegree_add_le (1 : ℤ[X]) X
                  _ = 2 := rfl
              omega
          _ < 2 * j + 2 := by omega
      constructor
      · rw [lambertNumerator_succ, add_comm, natDegree_add_eq_left_of_natDegree_lt (by
          rw [hmul]; exact hderiv), hmul]
        ring
      · rw [lambertNumerator_succ, add_comm,
          leadingCoeff_add_of_degree_lt (by
            refine lt_of_le_of_lt (degree_le_natDegree) ?_
            rw [degree_eq_natDegree (by
              intro h
              rw [h, natDegree_zero] at hmul
              omega)]
            exact_mod_cast hderiv), hmullead]
        push_cast [Nat.factorial_succ]
        ring

theorem natDegree_lambertNumerator {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    (lambertNumerator n j).natDegree = 2 * j :=
  (natDegree_and_leadingCoeff_lambertNumerator hn j).1

theorem leadingCoeff_lambertNumerator {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    (lambertNumerator n j).leadingCoeff = (n : ℤ) * (-1) ^ j * (j ! : ℤ) :=
  (natDegree_and_leadingCoeff_lambertNumerator hn j).2

/-- **The constant term** is the falling factorial `n(n-1)⋯(n-j)`. -/
theorem eval_zero_lambertNumerator (n j : ℕ) :
    (lambertNumerator n j).eval 0 = ∏ i ∈ range (j + 1), ((n : ℤ) - i) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [lambertNumerator_succ, eval_add, eval_mul, eval_mul, eval_X, zero_mul, zero_mul,
        zero_add, ih, prod_range_succ]
      unfold lambertMultiplier
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
      ring

/-- **Integrality**: every member of the family lies in `nℤ[v]`. -/
theorem natCast_dvd_lambertNumerator (n j : ℕ) :
    C (n : ℤ) ∣ lambertNumerator n j := by
  induction j with
  | zero => simp
  | succ j ih =>
      obtain ⟨S, hS⟩ := ih
      refine ⟨X * (1 + X) * derivative S + lambertMultiplier n j * S, ?_⟩
      rw [lambertNumerator_succ, hS, derivative_mul, derivative_C, zero_mul, zero_add]
      ring

end Fabius
