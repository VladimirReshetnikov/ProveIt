import IntegerPoints.FiniteComplexAbel
import IntegerPoints.IwaniecMozzochiEq84Quadratic
import Mathlib.Tactic

/-!
# Quadratic Abel-prefix bounds for Iwaniec--Mozzochi (8.4)

The finite Abel identity uses the inclusive prefix through `i`, whereas the
existing quadratic estimate is stated on `Finset.Ioc A B`.  For a sequence
`a`, the exact endpoint conversion is

`prefixSum a i = a 0 + sum_{0 < n <= i} a n`.

For the Section 8 quadratic phase the omitted `n = 0` term is exactly `1`.
Under `1 <= N`, `0 < beta`, and `beta * N <= 4`, this unit term is at most
`2 / sqrt beta`; adding it to the existing `800 / sqrt beta` incomplete-sum
bound gives the explicit uniform prefix constant `802`.
-/

open Real Finset
open scoped BigOperators

namespace LeanProofs.IntegerPoints

/-! ## Inclusive prefixes versus `Ioc 0 i` -/

namespace FiniteComplexAbel

/-- An inclusive zero-based prefix is its `n = 0` term plus the corresponding
right-closed incomplete sum.  This identity is valid, without a special case,
also when `i = 0`. -/
theorem prefixSum_eq_zero_add_sum_Ioc (a : ℕ → ℂ) (i : ℕ) :
    prefixSum a i = a 0 + ∑ n ∈ Finset.Ioc 0 i, a n := by
  unfold prefixSum
  have hrange : Finset.range (i + 1) = insert 0 (Finset.Ioc 0 i) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hzero : 0 ∉ Finset.Ioc 0 i := by simp
  rw [hrange, Finset.sum_insert hzero]

end FiniteComplexAbel

/-- For the quadratic sequence, the initial term in the inclusive prefix is
literally `e(0) = 1`. -/
theorem section8_quadratic_prefixSum_eq_one_add_sum_Ioc
    (alpha beta : ℝ) (i : ℕ) :
    FiniteComplexAbel.prefixSum
        (fun n : ℕ ↦ e (section8QuadraticPhase alpha beta n)) i =
      1 + ∑ n ∈ Finset.Ioc 0 i,
        e (section8QuadraticPhase alpha beta n) := by
  have hzero : e (section8QuadraticPhase alpha beta 0) = 1 := by
    simp [section8QuadraticPhase, e]
  simpa only [Nat.cast_zero, hzero] using
    FiniteComplexAbel.prefixSum_eq_zero_add_sum_Ioc
      (fun n : ℕ ↦ e (section8QuadraticPhase alpha beta n)) i

/-! ## Uniform prefix estimate -/

/-- Every inclusive quadratic prefix through `floor (8N)` is bounded by
`802 / sqrt beta` under exactly the numerical Section 8 inputs.  The constant
is `800` for the `Ioc 0 i` sum plus `2` for its included `n = 0` endpoint. -/
theorem section8_quadratic_prefixSum_uniform_of_bounds
    (alpha beta N : ℝ) (hN : 1 ≤ N)
    (hbeta : 0 < beta) (hbetaN : beta * N ≤ 4)
    {i : ℕ} (hi : i ≤ ⌊8 * N⌋₊) :
    ‖FiniteComplexAbel.prefixSum
        (fun n : ℕ ↦ e (section8QuadraticPhase alpha beta n)) i‖ ≤
      802 / Real.sqrt beta := by
  have hNnonneg : 0 ≤ N := zero_le_one.trans hN
  have hlength : ((i - 0 : ℕ) : ℝ) ≤ 8 * N :=
    section8_Ioc_length_le_eight_mul hNnonneg hi
  have hIoc :
      ‖∑ n ∈ Finset.Ioc 0 i,
          e (section8QuadraticPhase alpha beta n)‖ ≤
        800 / Real.sqrt beta :=
    section8_quadratic_sum_uniform_of_bounds
      alpha beta N 0 i hbeta hbetaN hlength
  have hbetaLeFour : beta ≤ 4 := by
    calc
      beta = beta * 1 := by ring
      _ ≤ beta * N := mul_le_mul_of_nonneg_left hN hbeta.le
      _ ≤ 4 := hbetaN
  have hsqrtBetaPos : 0 < Real.sqrt beta := Real.sqrt_pos.2 hbeta
  have hsqrtBetaLeTwo : Real.sqrt beta ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have honeLe : (1 : ℝ) ≤ 2 / Real.sqrt beta := by
    apply (le_div_iff₀ hsqrtBetaPos).2
    simpa only [one_mul] using hsqrtBetaLeTwo
  rw [section8_quadratic_prefixSum_eq_one_add_sum_Ioc]
  calc
    ‖(1 : ℂ) + ∑ n ∈ Finset.Ioc 0 i,
        e (section8QuadraticPhase alpha beta n)‖ ≤
        ‖(1 : ℂ)‖ +
          ‖∑ n ∈ Finset.Ioc 0 i,
            e (section8QuadraticPhase alpha beta n)‖ := norm_add_le _ _
    _ = 1 +
          ‖∑ n ∈ Finset.Ioc 0 i,
            e (section8QuadraticPhase alpha beta n)‖ := by rw [norm_one]
    _ ≤ 1 + 800 / Real.sqrt beta := by linarith
    _ ≤ 2 / Real.sqrt beta + 800 / Real.sqrt beta :=
      by linarith
    _ = 802 / Real.sqrt beta := by ring

/-- The preceding pointwise estimate in the exact universally quantified form
required by `FiniteComplexAbel.norm_weighted_sum_le_variation`. -/
theorem section8_quadratic_prefixSum_uniform
    (alpha beta N : ℝ) (hN : 1 ≤ N)
    (hbeta : 0 < beta) (hbetaN : beta * N ≤ 4) :
    ∀ i, i ≤ ⌊8 * N⌋₊ →
      ‖FiniteComplexAbel.prefixSum
          (fun n : ℕ ↦ e (section8QuadraticPhase alpha beta n)) i‖ ≤
        802 / Real.sqrt beta := by
  intro i hi
  exact section8_quadratic_prefixSum_uniform_of_bounds
    alpha beta N hN hbeta hbetaN hi

end LeanProofs.IntegerPoints
