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

open Polynomial Finset Nat

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
  natDegree_quadratic (by simp; omega)

theorem leadingCoeff_lambertMultiplier (n j : ℕ) :
    (lambertMultiplier n j).leadingCoeff = -((j : ℤ) + 1) :=
  leadingCoeff_quadratic (by simp; omega)

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
      (lambertNumerator n j).leadingCoeff = (n : ℤ) * (-1) ^ j * (Nat.factorial j : ℤ) := by
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  induction j with
  | zero => refine ⟨by simp, by simp⟩
  | succ j ih =>
      obtain ⟨hdeg, hlead⟩ := ih
      have hfac : ((Nat.factorial j : ℕ) : ℤ) ≠ 0 := by
        exact_mod_cast (Nat.factorial_pos j).ne'
      have hleadne : (lambertNumerator n j).leadingCoeff ≠ 0 := by
        rw [hlead]
        exact mul_ne_zero (mul_ne_zero hnz (pow_ne_zero _ (by norm_num))) hfac
      have hjne : -((j : ℤ) + 1) ≠ 0 := by
        have : (0 : ℤ) < (j : ℤ) + 1 := by positivity
        linarith [this]
      have hprodne :
          (lambertMultiplier n j).leadingCoeff * (lambertNumerator n j).leadingCoeff ≠ 0 := by
        rw [leadingCoeff_lambertMultiplier]
        exact mul_ne_zero hjne hleadne
      have hmul : (lambertMultiplier n j * lambertNumerator n j).natDegree = 2 * j + 2 := by
        rw [natDegree_mul' hprodne, natDegree_lambertMultiplier, hdeg]
        ring
      have hmullead : (lambertMultiplier n j * lambertNumerator n j).leadingCoeff
          = -((j : ℤ) + 1) * ((n : ℤ) * (-1) ^ j * (Nat.factorial j : ℤ)) := by
        rw [leadingCoeff_mul' hprodne, leadingCoeff_lambertMultiplier, hlead]
      have hxdeg : (X * (1 + X) : ℤ[X]).natDegree ≤ 2 := by
        refine le_trans natDegree_mul_le ?_
        have h1 : (X : ℤ[X]).natDegree ≤ 1 := by simp
        have h2 : ((1 : ℤ[X]) + X).natDegree ≤ 1 := by
          refine le_trans (natDegree_add_le _ _) ?_
          simp
        omega
      have hderiv : (X * (1 + X) * derivative (lambertNumerator n j)).natDegree < 2 * j + 2 := by
        by_cases hzero : derivative (lambertNumerator n j) = 0
        · rw [hzero, mul_zero, natDegree_zero]
          omega
        · have hjpos : j ≠ 0 := by
            rintro rfl
            rw [lambertNumerator_zero, derivative_C] at hzero
            exact hzero rfl
          have hd : (derivative (lambertNumerator n j)).natDegree ≤ 2 * j - 1 := by
            have h := natDegree_derivative_le (lambertNumerator n j)
            rw [hdeg] at h
            exact h
          have := natDegree_mul_le (p := (X * (1 + X) : ℤ[X]))
            (q := derivative (lambertNumerator n j))
          omega
      refine ⟨?_, ?_⟩
      · rw [lambertNumerator_succ, natDegree_add_eq_right_of_natDegree_lt (by rw [hmul]; exact hderiv),
          hmul]
        ring
      · rw [lambertNumerator_succ,
          leadingCoeff_add_of_degree_lt (degree_lt_degree (by rw [hmul]; exact hderiv)), hmullead]
        rw [Nat.factorial_succ]
        push_cast
        ring

theorem natDegree_lambertNumerator {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    (lambertNumerator n j).natDegree = 2 * j :=
  (natDegree_and_leadingCoeff_lambertNumerator hn j).1

theorem leadingCoeff_lambertNumerator {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    (lambertNumerator n j).leadingCoeff = (n : ℤ) * (-1) ^ j * (Nat.factorial j : ℤ) :=
  (natDegree_and_leadingCoeff_lambertNumerator hn j).2

/-- **The constant term** is the falling factorial `n(n-1)⋯(n-j)`. -/
theorem eval_zero_lambertNumerator (n j : ℕ) :
    (lambertNumerator n j).eval 0 = ∏ i ∈ range (j + 1), ((n : ℤ) - i) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : (X * (1 + X) * derivative (lambertNumerator n j)).eval 0 = 0 := by simp
      rw [lambertNumerator_succ, eval_add, h1, zero_add, eval_mul, ih, prod_range_succ]
      unfold lambertMultiplier
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
      push_cast
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
