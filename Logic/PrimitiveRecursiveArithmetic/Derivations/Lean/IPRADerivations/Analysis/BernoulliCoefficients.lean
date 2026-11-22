import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field

/-!
# The rational coefficients of the normalized Bernoulli polynomials

Packet: `analysis/calculus_ipra`, `report.tex`, the convention `P_n′ = P_{n−1}`, `∫₀¹ P_n = 0` (`n ≥ 1`),
`P_0 = 1`, and the coefficient bound `eq:coefbound`: "`‖P_n‖ ≤ (3/2) ‖P_{n−1}‖ ≤ (3/2)^n ≤ 2^n`. The first inequality
follows because the nonconstant coefficients contribute at most `Σ |a_i|`, and the new constant coefficient at most
`(1/2) Σ |a_i|`."

This is the metalevel (rational) half of `eq:Pfinitebounds`: the coefficients are fixed rational data, and the
iPRA statements about their evaluations are in `Analysis/BernoulliBounds`. With `bc n i` the coefficient of `t^i` in
`P_n`, defined by coefficientwise integration and the zero-mean constant:

* `bc_zero_of_gt`: `P_n` has degree `n`;
* `bc_deriv`: `(i + 1) bc (n+1) (i+1) = bc n i`, i.e. `P_{n+1}′ = P_n`;
* `bc_mean`: `Σ_i bc (n+1) i / (i + 1) = 0`, i.e. `∫₀¹ P_{n+1} = 0`;
* `nrm_succ_le`, `nrm_le`: `‖P_{n+1}‖ ≤ (3/2) ‖P_n‖` and `‖P_n‖ ≤ (3/2)^n` for `‖P‖ = Σ |coefficients|`.
-/

namespace LeanProofs.IPRA.Analysis.BernoulliCoefficients

open Finset

/-- The coefficient of `t^i` in `P_n`. -/
def bc : ℕ → ℕ → ℚ
  | 0, i => if i = 0 then 1 else 0
  | n + 1, 0 => -∑ i ∈ range (n + 1), bc n i / ((i + 1) * (i + 2))
  | n + 1, i + 1 => bc n i / (i + 1)

theorem bc_succ_succ (n i : ℕ) : bc (n + 1) (i + 1) = bc n i / (i + 1) := rfl

theorem bc_succ_zero (n : ℕ) : bc (n + 1) 0 = -∑ i ∈ range (n + 1), bc n i / ((i + 1) * (i + 2)) := rfl

/-- `P_n` has degree at most `n`. -/
theorem bc_zero_of_gt : ∀ n i, n < i → bc n i = 0
  | 0, i, h => by rw [bc, if_neg (by omega)]
  | _ + 1, 0, h => absurd h (by omega)
  | n + 1, i + 1, h => by rw [bc_succ_succ, bc_zero_of_gt n i (by omega), zero_div]

/-- `P_{n+1}′ = P_n`, coefficientwise. -/
theorem bc_deriv (n i : ℕ) : ((i : ℚ) + 1) * bc (n + 1) (i + 1) = bc n i := by
  rw [bc_succ_succ]
  have : ((i : ℚ) + 1) ≠ 0 := by positivity
  field_simp

/-- `∫₀¹ P_{n+1} = 0`. -/
theorem bc_mean (n : ℕ) : ∑ i ∈ range (n + 2), bc (n + 1) i / ((i : ℚ) + 1) = 0 := by
  rw [sum_range_succ', bc_succ_zero]
  have e : ∀ i ∈ range (n + 1), bc (n + 1) (i + 1) / (((i + 1 : ℕ) : ℚ) + 1) = bc n i / ((i + 1) * (i + 2)) :=
    fun i _ => by
      rw [bc_succ_succ]
      have h1 : ((i : ℚ) + 1) ≠ 0 := by positivity
      have h2 : ((i : ℚ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  rw [sum_congr rfl e]
  simp only [Nat.cast_zero, zero_add, div_one]
  ring

/-- `‖P_n‖ = Σ_{i ≤ n} |coefficients|`. -/
def nrm (n : ℕ) : ℚ := ∑ i ∈ range (n + 1), |bc n i|

theorem nrm_nonneg (n : ℕ) : 0 ≤ nrm n := sum_nonneg fun i _ => abs_nonneg _

/-- `‖P_{n+1}‖ ≤ (3/2) ‖P_n‖`. -/
theorem nrm_succ_le (n : ℕ) : nrm (n + 1) ≤ 3 / 2 * nrm n := by
  unfold nrm
  rw [sum_range_succ', bc_succ_zero, abs_neg]
  have h1 : |∑ i ∈ range (n + 1), bc n i / (((i : ℚ) + 1) * ((i : ℚ) + 2))| ≤
      (∑ i ∈ range (n + 1), |bc n i|) / 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sum_div]
    refine sum_le_sum fun i _ => ?_
    have hp : (0 : ℚ) < ((i : ℚ) + 1) * ((i : ℚ) + 2) := by positivity
    rw [abs_div, abs_of_pos hp, div_le_div_iff₀ hp (by norm_num : (0 : ℚ) < 2)]
    have hi : (0 : ℚ) ≤ i := Nat.cast_nonneg i
    have h2 : (2 : ℚ) ≤ ((i : ℚ) + 1) * ((i : ℚ) + 2) := by nlinarith
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h2 : ∑ i ∈ range (n + 1), |bc (n + 1) (i + 1)| ≤ ∑ i ∈ range (n + 1), |bc n i| := by
    refine sum_le_sum fun i _ => ?_
    rw [bc_succ_succ, abs_div]
    have hp : (0 : ℚ) < (i : ℚ) + 1 := by positivity
    rw [abs_of_pos hp]
    exact div_le_self (abs_nonneg _) (by linarith [(Nat.cast_nonneg i : (0 : ℚ) ≤ i)])
  linarith

/-- `‖P_n‖ ≤ (3/2)^n`. -/
theorem nrm_le : ∀ n, nrm n ≤ (3 / 2 : ℚ) ^ n
  | 0 => by simp [nrm, bc]
  | n + 1 => by
    rw [pow_succ]
    have := nrm_le n
    have h := nrm_succ_le n
    nlinarith [nrm_nonneg n]

/-- `‖P_n‖ ≤ 2^n`. -/
theorem nrm_le_two (n : ℕ) : nrm n ≤ 2 ^ n :=
  (nrm_le n).trans (pow_le_pow_left₀ (by norm_num) (by norm_num) n)

end LeanProofs.IPRA.Analysis.BernoulliCoefficients
