import IntegerPoints.BerndtKimZaharescu
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The harmonic-sum estimate

This proves the estimate quoted in the Dirichlet-divisor discussion of
`IntegerPoints.BerndtKimZaharescu`.  For `N = ⌊x⌋`, the standard bounds

`H_N - log (N + 1) < γ < H_N - log N`

place `H_N - log x - γ` in an interval of length at most `1 / N`.  When
`x ≥ 1`, one has `x < N + 1 ≤ 2N`, giving the stated bound with the
explicit constant `2`.
-/

open scoped BigOperators

namespace LeanProofs.IntegerPoints

/-- The harmonic-sum estimate holds with `C = 2` and `x₀ = 1`. -/
theorem harmonicSum_estimate_holds : harmonicSum_estimate := by
  refine ⟨2, 1, ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith

  let N : ℕ := ⌊x⌋₊
  have hN_one : 1 ≤ N := by
    dsimp [N]
    exact (Nat.one_le_floor_iff x).2 hx
  have hN_pos_nat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN_one
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hN_pos_nat
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN_pos_nat

  have hNx : (N : ℝ) ≤ x := by
    dsimp [N]
    exact Nat.floor_le hxpos.le
  have hxN1 : x < (N : ℝ) + 1 := by
    simpa [N] using Nat.lt_floor_add_one x
  have hlogNx : Real.log (N : ℝ) ≤ Real.log x :=
    Real.log_le_log hN_pos hNx
  have hlogxN1 : Real.log x ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log hxpos hxN1.le

  have hgamma_lower :
      (harmonic N : ℝ) - Real.log ((N : ℝ) + 1) <
        Real.eulerMascheroniConstant := by
    simpa [Real.eulerMascheroniSeq, Nat.cast_add, Nat.cast_one] using
      Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have hgamma_upper :
      Real.eulerMascheroniConstant <
        (harmonic N : ℝ) - Real.log (N : ℝ) := by
    simpa [Real.eulerMascheroniSeq', hN_ne] using
      Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N

  have herr_gap :
      |(harmonic N : ℝ) - (Real.log x + Real.eulerMascheroniConstant)| ≤
        Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) := by
    rw [abs_le]
    constructor <;> linarith

  have hgap :
      Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) ≤ 1 / (N : ℝ) := by
    calc
      Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) =
          Real.log (((N : ℝ) + 1) / (N : ℝ)) := by
            symm
            exact Real.log_div (by positivity) hN_pos.ne'
      _ ≤ ((N : ℝ) + 1) / (N : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / (N : ℝ) := by
        field_simp [hN_pos.ne']; ring

  have hx_two_N : x ≤ 2 * (N : ℝ) := by
    have hN_cast : (1 : ℝ) ≤ N := by exact_mod_cast hN_one
    linarith
  have hinv : 1 / (N : ℝ) ≤ 2 / x := by
    rw [div_le_div_iff₀ hN_pos hxpos]
    simpa using hx_two_N

  have hsum :
      (∑ n ∈ upTo x, (1 : ℝ) / n) = (harmonic N : ℝ) := by
    simp only [upTo, N, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div]
  rw [hsum]
  exact herr_gap.trans (hgap.trans hinv)

end LeanProofs.IntegerPoints
