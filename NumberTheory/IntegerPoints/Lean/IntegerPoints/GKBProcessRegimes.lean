import IntegerPoints.GKBProcessArithmetic

/-!
# Graham--Kolesnik B-process: elementary outer regimes

This module removes two elementary cases from the analytic core of Theorem
3.10.  If `N < 1`, an interval contained in `[N, 2N]` contains at most one
positive natural number; when it contains one, necessarily `N >= 1/2`, and
the transformed exponent-pair right-hand side pays for that summand.  If
`N >= 1` and the dual scale `L <= 1`, the `(1/2,1/2)` model is bounded by the
main term of the B-transform.

The lemmas are stated independently of `InGKClass`, so later exponent-pair
proofs can reuse the finite-range bookkeeping without unpacking a class.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

namespace GKB

/-! ## Intervals shorter than one -/

/-- The norm of an unweighted exponential sum is at most its number of terms. -/
theorem norm_sum_intRange_e_le_card (a b : ℝ) (f : ℝ → ℝ) :
    ‖∑ n ∈ intRange a b, e (f n)‖ ≤ ((intRange a b).card : ℝ) := by
  calc
    ‖∑ n ∈ intRange a b, e (f n)‖ ≤
        ∑ n ∈ intRange a b, ‖e (f n)‖ := norm_sum_le _ _
    _ = ((intRange a b).card : ℝ) := by simp [norm_e]

/-- An interval with upper endpoint below `2` contains at most one positive
natural-number index. -/
theorem card_intRange_le_one_of_upper_lt_two {a b : ℝ} (hb : b < 2) :
    (intRange a b).card ≤ 1 := by
  rw [intRange, Nat.card_Ioc]
  by_cases hbOne : b < 1
  · rw [Nat.floor_eq_zero.2 hbOne]
    omega
  · have hb0 : 0 ≤ b := by linarith
    have hfloor : ⌊b⌋₊ < 2 := (Nat.floor_lt hb0).2 hb
    omega

/-- If an interval ending by `2N` contains a positive natural number, then
`N >= 1/2`. -/
theorem half_le_of_intRange_nonempty {N a b : ℝ}
    (hb : b ≤ 2 * N) (hne : (intRange a b).Nonempty) :
    1 / 2 ≤ N := by
  obtain ⟨n, hn⟩ := hne
  rw [intRange, Finset.mem_Ioc] at hn
  have hfloor : 1 ≤ ⌊b⌋₊ := by omega
  have hb0 : 0 ≤ b := by
    by_contra h
    have hbOne : b < 1 := by linarith
    have hzero : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.2 hbOne
    omega
  have hbOne : (1 : ℝ) ≤ b := by
    calc
      (1 : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast hfloor
      _ ≤ b := Nat.floor_le hb0
  linarith

/-- The complete `N < 1` estimate used by the B-process.  The result uses
only the class interval's upper-endpoint condition `b <= 2N`. -/
theorem norm_sum_intRange_e_le_two_mul_bRhs_of_lt_one
    {N L a b k l : ℝ} {f : ℝ → ℝ}
    (hN : 0 < N) (hNone : N < 1) (hL : 0 < L)
    (hb : b ≤ 2 * N) (hk : k ≤ 1 / 2) (hl : 1 / 2 ≤ l) :
    ‖∑ n ∈ intRange a b, e (f n)‖ ≤
      2 * (L ^ (l - 1 / 2) * N ^ (k + 1 / 2) + L⁻¹) := by
  rcases (intRange a b).eq_empty_or_nonempty with hempty | hne
  · rw [hempty, Finset.sum_empty, norm_zero]
    positivity
  · have hcard : (intRange a b).card ≤ 1 :=
      card_intRange_le_one_of_upper_lt_two (hb.trans_lt (by linarith))
    have hnorm : ‖∑ n ∈ intRange a b, e (f n)‖ ≤ 1 := by
      exact (norm_sum_intRange_e_le_card a b f).trans (by exact_mod_cast hcard)
    exact hnorm.trans (one_le_two_mul_bRhs_of_half_le_N_of_lt_one
      (half_le_of_intRange_nonempty hb hne) hNone hL hk hl)

/-! ## The small dual-scale comparison -/

/-- The `(1/2,1/2)` main monomial is bounded by the B-transform main
monomial when `N >= 1` and `0 < L <= 1`. -/
theorem halfPairMain_le_bMain_of_le_one {N L k l : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hLone : L ≤ 1)
    (hk : 0 ≤ k) (hl : l ≤ 1) :
    L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) ≤
      L ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  rw [← Real.mul_rpow hL.le hNpos.le, ← Real.sqrt_eq_rpow]
  exact sqrt_mul_le_bMain_of_le_one hN hL hLone hk hl

/-- Consequently, the full `(1/2,1/2)` model, including its reciprocal
error term, is bounded by the transformed B-process model. -/
theorem halfPairModel_le_bRhs_of_le_one {N L k l : ℝ}
    (hN : 1 ≤ N) (hL : 0 < L) (hLone : L ≤ 1)
    (hk : 0 ≤ k) (hl : l ≤ 1) :
    L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) + L⁻¹ ≤
      L ^ (l - 1 / 2) * N ^ (k + 1 / 2) + L⁻¹ :=
  add_le_add (halfPairMain_le_bMain_of_le_one hN hL hLone hk hl) le_rfl

end GKB

end LeanProofs.IntegerPoints
