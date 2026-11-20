import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

/-! The finite-difference certificate for finding a sign of a monic rational
polynomial on any arithmetic progression. The polynomial used here is a
finite rational observation of a polynomial with named real coefficients.
All declarations are ambient Lean theorems. -/

namespace BudgetAnalysis.Root
open Polynomial

/-- The first index maximizing a rational score on the inclusive range. -/
def best (score : Nat → ℚ) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let j := best score n
    if score j < score (n + 1) then n + 1 else j

theorem best_le (score : Nat → ℚ) (n : Nat) : best score n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [best]
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans ih (Nat.le_succ n)

theorem score_le_best (score : Nat → ℚ) (n i : Nat) (hi : i ≤ n) :
    score i ≤ score (best score n) := by
  induction n generalizing i with
  | zero => have := Nat.eq_zero_of_le_zero hi; subst i; rfl
  | succ n ih =>
    simp only [best]
    split <;> rename_i h
    · by_cases he : i = n + 1
      · simp [he]
      · exact le_trans (ih i (by omega)) h.le
    · by_cases he : i = n + 1
      · exact he ▸ le_of_not_gt h
      · exact ih i (by omega)

/-- Each difference level doubles the absolute upper bound on a table. -/
theorem difference_bound (f : ℚ → ℚ) (n : Nat) (x M : ℚ)
    (h : ∀ j : Nat, j ≤ n → |f (x + j)| ≤ M) :
    |((fwdDiff 1)^[n] f) x| ≤ 2^n * M := by
  induction n generalizing x with
  | zero => simpa using h 0 (Nat.le_refl 0)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change |((fwdDiff 1)^[n] f) (x + 1) - ((fwdDiff 1)^[n] f) x| ≤ _
    have hr := ih (x + 1) (fun j hj => by
      have e := h (j + 1) (by omega)
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using e)
    have hl := ih x (fun j hj => h j (by omega))
    refine (abs_sub _ _).trans ?_
    rw [pow_succ]
    linarith

/-- On a progression of length degree+1, choose an actual index. The
selected absolute value is at least d! h^d / 2^d, including for repeated
roots. This implements inequality (R1) of the report. -/
theorem monic_peak (Q : ℚ[X]) (hq : Q.Monic) (u h : ℚ) (hh : 0 < h) :
    let d := Q.natDegree
    let score := fun j : Nat => |Q.eval (u + (j : ℚ) * h)|
    best score d ≤ d ∧ (d.factorial : ℚ) * h^d ≤ 2^d * score (best score d) := by
  let d := Q.natDegree
  let score := fun j : Nat => |Q.eval (u + (j : ℚ) * h)|
  let L : ℚ[X] := C h * X + C u
  let T := Q.comp L
  have ld : L.natDegree = 1 := by
    change (C h * X + C u).natDegree = 1
    rw [natDegree_add_C, natDegree_C_mul_X h hh.ne']
  have lc : L.leadingCoeff = h := by
    have hdeg : (C u).degree < (C h * X).degree := by
      rw [degree_C_mul_X hh.ne']
      exact lt_of_le_of_lt degree_C_le (by decide)
    exact (leadingCoeff_add_of_degree_lt' hdeg).trans (leadingCoeff_C_mul_X h)
  have td : T.natDegree = d := by simp [T, natDegree_comp, ld, d]
  have tc : T.leadingCoeff = h ^ d := by
    change (Q.comp L).leadingCoeff = _
    rw [leadingCoeff_comp (by simp [ld]), hq.leadingCoeff, lc, one_mul]
  have values : ∀ j : Nat, |T.eval (0 + (j : ℚ))| = score j := by
    intro j
    change |(Q.comp (C h * X + C u)).eval (0 + (j : ℚ))| = |Q.eval (u + (j : ℚ) * h)|
    rw [zero_add, eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_C, mul_comm h, add_comm _ u]
  have hb := difference_bound (fun x => T.eval x) d 0 (score (best score d))
    (fun j hj => (values j) ▸ score_le_best score d j hj)
  have iden := congrFun T.fwdDiff_iter_degree_eq_factorial (0 : ℚ)
  rw [td, tc] at iden
  rw [iden] at hb
  refine ⟨best_le score d, ?_⟩
  change (d.factorial : ℚ) * h ^ d ≤ 2 ^ d * score (best score d)
  simpa [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hh.le, mul_comm] using hb

/-- Cross-precision comparison transports a positive finite sign to the
weak bracket predicate at an arbitrary fixed target precision. -/
theorem positive_endpoint (v w current target : ℚ)
    (error : |w - v| ≤ target + current) (positive : current ≤ v) :
    -target ≤ w := by
  have lower := (abs_le.mp error).1
  linarith

end BudgetAnalysis.Root
