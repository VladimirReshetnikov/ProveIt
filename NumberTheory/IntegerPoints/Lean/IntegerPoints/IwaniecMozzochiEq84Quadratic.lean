import IntegerPoints.IwaniecMozzochiEq84

/-!
# The uniform quadratic partial-sum estimate for Iwaniec--Mozzochi (8.4)

This module closes the elementary cancellation step quoted immediately before
(8.4).  On every natural interval contained in the Section 8 support window,
the quadratic exponential sum is at most an explicit absolute constant times
`beta⁻¹ᐟ²`.

The proof keeps both endpoints literal.  The upper endpoint condition
`B ≤ floor (8 * N)` first gives both containment in `section8WeightRange N`
and the real length bound `B - A ≤ 8 * N`.  We then split according as
`2 * beta ≤ 1 / 4`.  In the first regime the second-derivative estimate is
combined with `beta * N ≤ 4`; in the complementary regime the same scale
bound absorbs the trivial interval-length estimate.  The generous constant
`800` is chosen only to keep the normalization arithmetic transparent.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

/-! ## Literal endpoint conversion -/

/-- If the closed upper endpoint of `Ioc A B` is at most `floor (8N)`, then
the whole interval belongs to the finite Section 8 support range
`range (floor (8N) + 1)`. -/
theorem section8_Ioc_subset_weightRange
    {N : ℝ} {A B : ℕ} (hB : B ≤ ⌊8 * N⌋₊) :
    Finset.Ioc A B ⊆ section8WeightRange N := by
  intro n hn
  have hnB : n ≤ B := (Finset.mem_Ioc.mp hn).2
  rw [section8WeightRange, Finset.mem_range]
  omega

/-- The corresponding real interval length is at most `8N`.  This records
explicitly the cast and floor conversion needed by the analytic estimate. -/
theorem section8_Ioc_length_le_eight_mul
    {N : ℝ} (hN : 0 ≤ N) {A B : ℕ} (hB : B ≤ ⌊8 * N⌋₊) :
    ((B - A : ℕ) : ℝ) ≤ 8 * N := by
  have hsub : B - A ≤ B := Nat.sub_le B A
  have hsubCast : ((B - A : ℕ) : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hsub
  have hBcast : (B : ℝ) ≤ (⌊8 * N⌋₊ : ℝ) := by
    exact_mod_cast hB
  have hfloor : (⌊8 * N⌋₊ : ℝ) ≤ 8 * N :=
    Nat.floor_le (mul_nonneg (by norm_num) hN)
  exact hsubCast.trans (hBcast.trans hfloor)

/-! ## A parameter-free quadratic estimate -/

/-- An explicit version of the quadratic estimate used after (8.3).

The hypotheses isolate exactly the two numerical inputs supplied in Section 8:
the interval has length at most `8N`, and `beta * N ≤ 4`.  No Farey, smooth
weight, or short-cell premise is hidden in this lemma. -/
theorem section8_quadratic_sum_uniform_of_bounds
    (alpha beta N : ℝ) (A B : ℕ)
    (hbeta : 0 < beta) (hbetaN : beta * N ≤ 4)
    (hlength : ((B - A : ℕ) : ℝ) ≤ 8 * N) :
    ‖∑ n ∈ Finset.Ioc A B, e (section8QuadraticPhase alpha beta n)‖ ≤
      800 / Real.sqrt beta := by
  have hsqrtBetaPos : 0 < Real.sqrt beta := Real.sqrt_pos.2 hbeta
  have hlengthNonneg : 0 ≤ ((B - A : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN_sqrt_le :
      N * Real.sqrt beta ≤ 4 / Real.sqrt beta := by
    apply (le_div_iff₀ hsqrtBetaPos).2
    calc
      N * Real.sqrt beta * Real.sqrt beta =
          N * (Real.sqrt beta) ^ 2 := by ring
      _ = N * beta := by rw [Real.sq_sqrt hbeta.le]
      _ = beta * N := by ring
      _ ≤ 4 := hbetaN
  have hlength_sqrt_le :
      ((B - A : ℕ) : ℝ) * Real.sqrt beta ≤
        32 / Real.sqrt beta := by
    calc
      ((B - A : ℕ) : ℝ) * Real.sqrt beta ≤
          (8 * N) * Real.sqrt beta :=
        mul_le_mul_of_nonneg_right hlength (Real.sqrt_nonneg beta)
      _ = 8 * (N * Real.sqrt beta) := by ring
      _ ≤ 8 * (4 / Real.sqrt beta) :=
        mul_le_mul_of_nonneg_left hN_sqrt_le (by norm_num)
      _ = 32 / Real.sqrt beta := by ring
  by_cases hsmall : 2 * beta ≤ 1 / 4
  · have hsqrtTwoLe : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    have hsqrtTwoBeta :
        Real.sqrt (2 * beta) ≤ 2 * Real.sqrt beta := by
      calc
        Real.sqrt (2 * beta) = Real.sqrt 2 * Real.sqrt beta :=
          Real.sqrt_mul (by norm_num) beta
        _ ≤ 2 * Real.sqrt beta :=
          mul_le_mul_of_nonneg_right hsqrtTwoLe (Real.sqrt_nonneg beta)
    have hsqrtMono : Real.sqrt beta ≤ Real.sqrt (2 * beta) :=
      Real.sqrt_le_sqrt (by linarith [hbeta.le])
    have hinvSqrt :
        1 / Real.sqrt (2 * beta) ≤ 1 / Real.sqrt beta :=
      one_div_le_one_div_of_le hsqrtBetaPos hsqrtMono
    have hfirst :
        12 * ((B - A : ℕ) : ℝ) * Real.sqrt (2 * beta) ≤
          768 / Real.sqrt beta := by
      calc
        12 * ((B - A : ℕ) : ℝ) * Real.sqrt (2 * beta) ≤
            12 * ((B - A : ℕ) : ℝ) * (2 * Real.sqrt beta) :=
          mul_le_mul_of_nonneg_left hsqrtTwoBeta
            (mul_nonneg (by norm_num) hlengthNonneg)
        _ = 24 * (((B - A : ℕ) : ℝ) * Real.sqrt beta) := by ring
        _ ≤ 24 * (32 / Real.sqrt beta) :=
          mul_le_mul_of_nonneg_left hlength_sqrt_le (by norm_num)
        _ = 768 / Real.sqrt beta := by ring
    have hsecond :
        24 / Real.sqrt (2 * beta) ≤ 24 / Real.sqrt beta := by
      calc
        24 / Real.sqrt (2 * beta) =
            24 * (1 / Real.sqrt (2 * beta)) := by ring
        _ ≤ 24 * (1 / Real.sqrt beta) :=
          mul_le_mul_of_nonneg_left hinvSqrt (by norm_num)
        _ = 24 / Real.sqrt beta := by ring
    calc
      ‖∑ n ∈ Finset.Ioc A B,
          e (section8QuadraticPhase alpha beta n)‖ ≤
          12 * ((B - A : ℕ) : ℝ) * Real.sqrt (2 * beta) +
            24 / Real.sqrt (2 * beta) :=
        section8_quadratic_sum_vdc alpha beta A B hbeta hsmall
      _ ≤ 768 / Real.sqrt beta + 24 / Real.sqrt beta :=
        add_le_add hfirst hsecond
      _ = 792 / Real.sqrt beta := by ring
      _ ≤ 800 / Real.sqrt beta :=
        div_le_div_of_nonneg_right (by norm_num) hsqrtBetaPos.le
  · have hlargeTwo : 1 / 4 < 2 * beta := lt_of_not_ge hsmall
    have hlarge : 1 / 8 < beta := by linarith
    have hquarterSqrt : (1 : ℝ) / 4 < Real.sqrt beta := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith
    have hinvSqrtLeFour : 1 / Real.sqrt beta ≤ 4 := by
      apply (div_le_iff₀ hsqrtBetaPos).2
      nlinarith
    have hlengthSqrtLeEightHundred :
        ((B - A : ℕ) : ℝ) * Real.sqrt beta ≤ 800 := by
      calc
        ((B - A : ℕ) : ℝ) * Real.sqrt beta ≤
            32 / Real.sqrt beta := hlength_sqrt_le
        _ = 32 * (1 / Real.sqrt beta) := by ring
        _ ≤ 32 * 4 :=
          mul_le_mul_of_nonneg_left hinvSqrtLeFour (by norm_num)
        _ ≤ 800 := by norm_num
    calc
      ‖∑ n ∈ Finset.Ioc A B,
          e (section8QuadraticPhase alpha beta n)‖ ≤
          ((B - A : ℕ) : ℝ) :=
        section8_quadratic_sum_trivial alpha beta A B
      _ ≤ 800 / Real.sqrt beta :=
        (le_div_iff₀ hsqrtBetaPos).2 hlengthSqrtLeEightHundred

/-! ## Section 8 specialization -/

/-- Every quadratic partial sum whose literal upper endpoint lies in the
Section 8 support window satisfies the paper's `O(beta⁻¹ᐟ²)` estimate, with
the absolute constant `800`. -/
theorem section8_quadratic_sum_uniform
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) (A B : ℕ)
    (hB : B ≤ ⌊8 * shiftLength x M⌋₊) :
    ‖∑ n ∈ Finset.Ioc A B,
        e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2)‖ ≤
      800 / Real.sqrt (betaIM x a c h) := by
  have hN : 0 ≤ shiftLength x M := (section8_shiftLength_pos hmain).le
  have hlength : ((B - A : ℕ) : ℝ) ≤ 8 * shiftLength x M :=
    section8_Ioc_length_le_eight_mul hN hB
  simpa [section8QuadraticPhase] using
    section8_quadratic_sum_uniform_of_bounds
      (alphaIM x a c h) (betaIM x a c h) (shiftLength x M) A B
      (betaIM_pos_of_mem_intRange hmain hfarey hh)
      (betaIM_mul_shiftLength_le_four hmain hfarey hh) hlength

end LeanProofs.IntegerPoints
