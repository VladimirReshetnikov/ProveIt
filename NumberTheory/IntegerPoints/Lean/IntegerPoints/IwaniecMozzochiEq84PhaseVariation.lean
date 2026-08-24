import IntegerPoints.IwaniecMozzochiEq84RemainderBounds
import IntegerPoints.IwaniecMozzochiEq84SigmaVariation
import IntegerPoints.SP3Tail

/-!
# Variation of the Section 8 remainder phase factor

This module supplies the next finite partial-summation layer in the proof of
Iwaniec--Mozzochi (8.4).  For the exact remainder `t(n)` it introduces

`v(n) = e(t(n)) - 1`

and controls `v` on the whole inclusive index interval
`0, ..., floor (8 * shiftLength x M)`.

The real-window estimates from `IwaniecMozzochiEq84RemainderBounds` are used
at every point between consecutive indices, so the first-difference estimate
is a genuine mean-value-theorem argument rather than a pointwise shortcut.
Together with the fixed smooth-weight bounds, this gives an explicit
variation bound for `sigma(n/N) * v(n)`.  No final conversion to a power of
`x` is attempted here.
-/

open Real Set
open scoped BigOperators

namespace LeanProofs.IntegerPoints

noncomputable section

/-! ## The phase-error factor and elementary exponential Lipschitz bound -/

/-- The perturbation factor retained in the exact error sum for (8.4). -/
noncomputable def section8PhaseErrorFactor
    (x : Real) (a c h n : Nat) : Complex :=
  e (section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) n) - 1

/-- The additive character is globally `2 * pi`-Lipschitz on the real line.
This two-point form follows from multiplicativity, unit norm, and the existing
one-point estimate `SP.norm_e_sub_one_le`. -/
theorem section8_norm_e_sub_e_le (s t : Real) :
    ‖e s - e t‖ <= 2 * Real.pi * |s - t| := by
  have hs : s = t + (s - t) := by ring
  have hfactor : e s - e t = e t * (e (s - t) - 1) := by
    rw [hs, KL.e_add]
    ring
  rw [hfactor, norm_mul, PS.norm_e_one, one_mul]
  exact SP.norm_e_sub_one_le (s - t)

/-! ## Exact inclusive index geometry -/

/-- Every natural index through `floor (8N)` belongs to the unscaled real
window `[0, 8N]`.  This is kept separate from the analogous scaled-weight
fact so that both endpoints in the remainder MVT are explicit. -/
theorem section8_nat_mem_remainder_window
    {N : Real} (hN : 0 <= N) {n : Nat} (hn : n <= ⌊8 * N⌋₊) :
    (n : Real) ∈ Set.Icc (0 : Real) (8 * N) := by
  have hnCast : (n : Real) <= (⌊8 * N⌋₊ : Real) := by
    exact_mod_cast hn
  exact ⟨Nat.cast_nonneg n,
    hnCast.trans (section8_floor_cast_le_eight_mul hN)⟩

/-! ## Uniform endpoint and first-difference estimates -/

/-- The pointwise remainder bound gives a uniform norm bound for the phase
error factor through the inclusive terminal index. -/
theorem section8PhaseErrorFactor_norm_le
    {x H M : Real} {a c h n : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H))
    (hn : n <= ⌊8 * shiftLength x M⌋₊) :
    ‖section8PhaseErrorFactor x a c h n‖ <=
      60000 * Real.pi * x * H * (shiftLength x M) ^ 3 / M ^ 4 := by
  have hnWindow : (n : Real) ∈
      Set.Icc (0 : Real) (8 * shiftLength x M) :=
    section8_nat_mem_remainder_window (section8_shiftLength_pos hmain).le hn
  have ht := section8_farey_remainder_abs_le
    (h := h) hmain hfarey hh hnWindow
  unfold section8PhaseErrorFactor
  calc
    ‖e (section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) n) - 1‖ <=
        2 * Real.pi *
          |section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) n| :=
      SP.norm_e_sub_one_le _
    _ <= 2 * Real.pi *
        (30000 * x * H * (shiftLength x M) ^ 3 / M ^ 4) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 60000 * Real.pi * x * H * (shiftLength x M) ^ 3 / M ^ 4 := by
      ring

/-- The real remainder changes by at most the uniform derivative bound across
each admissible unit step.  Differentiability and the derivative estimate are
both supplied on the entire real interval containing the two endpoints. -/
theorem section8_farey_remainder_step_abs_le
    {x H M : Real} {a c h n : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H))
    (hn : n + 1 <= ⌊8 * shiftLength x M⌋₊) :
    |section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) (n + 1) -
        section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) n| <=
      30000 * x * H * (shiftLength x M) ^ 2 / M ^ 4 := by
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  have hnFloor : n <= ⌊8 * shiftLength x M⌋₊ :=
    (Nat.le_succ n).trans hn
  have hu : (n : Real) ∈ Set.Icc (0 : Real) (8 * shiftLength x M) :=
    section8_nat_mem_remainder_window hN.le hnFloor
  have hv : ((n + 1 : Nat) : Real) ∈
      Set.Icc (0 : Real) (8 * shiftLength x M) :=
    section8_nat_mem_remainder_window hN.le hn
  have hdiff : ∀ z ∈ Set.Icc (0 : Real) (8 * shiftLength x M),
      DifferentiableAt Real
        (section8Remainder x h (fareyPoint x a c) (fareyFrac x a c)) z := by
    intro z hz
    exact (section8_farey_remainder_hasDerivAt
      (h := h) hmain hfarey hz).differentiableAt
  have hderiv : ∀ z ∈ Set.Icc (0 : Real) (8 * shiftLength x M),
      ‖deriv (section8Remainder x h (fareyPoint x a c) (fareyFrac x a c)) z‖ <=
        30000 * x * H * (shiftLength x M) ^ 2 / M ^ 4 := by
    intro z hz
    have hd := section8_farey_remainder_hasDerivAt
      (h := h) hmain hfarey hz
    rw [hd.deriv, Real.norm_eq_abs]
    exact section8_farey_remainderDeriv_abs_le
      (h := h) hmain hfarey hh hz
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := Real)
    (f := section8Remainder x h (fareyPoint x a c) (fareyFrac x a c))
    (s := Set.Icc (0 : Real) (8 * shiftLength x M))
    (x := (n : Real)) (y := ((n + 1 : Nat) : Real))
    (C := 30000 * x * H * (shiftLength x M) ^ 2 / M ^ 4)
    hdiff hderiv (convex_Icc (0 : Real) (8 * shiftLength x M)) hu hv
  have hstep : ((n + 1 : Nat) : Real) - (n : Real) = 1 := by
    push_cast
    ring
  have hstepNorm : ‖((n + 1 : Nat) : Real) - (n : Real)‖ = 1 := by
    rw [hstep, norm_one]
  rw [hstepNorm, mul_one] at hmvt
  simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using hmvt

/-- Applying the two-point exponential estimate to the real MVT bound gives
the first-difference estimate for `v(n) = e(t(n)) - 1`. -/
theorem section8PhaseErrorFactor_step_norm_le
    {x H M : Real} {a c h n : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H))
    (hn : n + 1 <= ⌊8 * shiftLength x M⌋₊) :
    ‖section8PhaseErrorFactor x a c h n -
        section8PhaseErrorFactor x a c h (n + 1)‖ <=
      60000 * Real.pi * x * H * (shiftLength x M) ^ 2 / M ^ 4 := by
  let t₀ : Real :=
    section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) (n : Real)
  let t₁ : Real :=
    section8Remainder x h (fareyPoint x a c) (fareyFrac x a c)
      ((n : Real) + 1)
  have ht : |t₁ - t₀| <=
      30000 * x * H * (shiftLength x M) ^ 2 / M ^ 4 := by
    simpa only [t₀, t₁] using
      section8_farey_remainder_step_abs_le hmain hfarey hh hn
  have ht' : |t₀ - t₁| <=
      30000 * x * H * (shiftLength x M) ^ 2 / M ^ 4 := by
    rw [abs_sub_comm]
    exact ht
  simp only [section8PhaseErrorFactor, Nat.cast_add, Nat.cast_one]
  change ‖(e t₀ - 1) - (e t₁ - 1)‖ <=
    60000 * Real.pi * x * H * (shiftLength x M) ^ 2 / M ^ 4
  rw [show (e t₀ - 1) - (e t₁ - 1) = e t₀ - e t₁ by ring]
  calc
    ‖e t₀ - e t₁‖ <= 2 * Real.pi * |t₀ - t₁| :=
      section8_norm_e_sub_e_le t₀ t₁
    _ <= 2 * Real.pi *
        (30000 * x * H * (shiftLength x M) ^ 2 / M ^ 4) :=
      mul_le_mul_of_nonneg_left ht' (by positivity)
    _ = 60000 * Real.pi * x * H * (shiftLength x M) ^ 2 / M ^ 4 := by
      ring

/-! ## Aggregate phase-factor and product variation -/

/-- Summing the explicit step estimate over `range (floor (8N))` produces a
uniform variation contribution on the same `N^3 / M^4` scale as the endpoint
bound.  Every summand's successor remains inside the inclusive terminal
index. -/
theorem section8PhaseErrorFactor_difference_sum_le
    {x H M : Real} {a c h : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    (∑ i ∈ Finset.range ⌊8 * shiftLength x M⌋₊,
        ‖section8PhaseErrorFactor x a c h i -
          section8PhaseErrorFactor x a c h (i + 1)‖) <=
      480000 * Real.pi * x * H * (shiftLength x M) ^ 3 / M ^ 4 := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hM : 0 < M :=
    (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  have hfloor : (⌊8 * shiftLength x M⌋₊ : Real) <=
      8 * shiftLength x M :=
    section8_floor_cast_le_eight_mul hN.le
  have hstepNonneg :
      0 <= 60000 * Real.pi * x * H * (shiftLength x M) ^ 2 / M ^ 4 := by
    positivity
  calc
    (∑ i ∈ Finset.range ⌊8 * shiftLength x M⌋₊,
        ‖section8PhaseErrorFactor x a c h i -
          section8PhaseErrorFactor x a c h (i + 1)‖) <=
        ∑ _i ∈ Finset.range ⌊8 * shiftLength x M⌋₊,
          60000 * Real.pi * x * H * (shiftLength x M) ^ 2 / M ^ 4 := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hiLt : i < ⌊8 * shiftLength x M⌋₊ := Finset.mem_range.mp hi
      have hiSucc : i + 1 <= ⌊8 * shiftLength x M⌋₊ :=
        Nat.add_one_le_iff.mpr hiLt
      exact section8PhaseErrorFactor_step_norm_le hmain hfarey hh hiSucc
    _ = (⌊8 * shiftLength x M⌋₊ : Real) *
        (60000 * Real.pi * x * H * (shiftLength x M) ^ 2 / M ^ 4) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ <= (8 * shiftLength x M) *
        (60000 * Real.pi * x * H * (shiftLength x M) ^ 2 / M ^ 4) :=
      mul_le_mul_of_nonneg_right hfloor hstepNonneg
    _ = 480000 * Real.pi * x * H * (shiftLength x M) ^ 3 / M ^ 4 := by
      ring

/-- Complete finite product-variation estimate for
`sigma(n/N) * (e(t(n)) - 1)`.  The constants `S₀,S₁` are arbitrary compact
bounds for the one fixed smooth weight; their nonnegativity follows from the
two displayed bound hypotheses at `0`.  The result deliberately stops at the
exact `x * H * N^3 / M^4` scale. -/
theorem section8SigmaPhaseError_variation_le
    {sigma : Real → Real} (hsigma : IsSmoothWeight sigma 4 8)
    {S₀ S₁ : Real}
    (hsigmaBound : ∀ t ∈ Set.Icc (0 : Real) 8, |sigma t| <= S₀)
    (hderiv : ∀ t ∈ Set.Icc (0 : Real) 8, |deriv sigma t| <= S₁)
    {x H M : Real} {a c h : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    FiniteComplexAbel.variation
        (fun i ↦ section8SigmaWeight sigma (shiftLength x M) i *
          section8PhaseErrorFactor x a c h i)
        ⌊8 * shiftLength x M⌋₊ <=
      60000 * Real.pi * (9 * S₀ + 8 * S₁) * x * H *
        (shiftLength x M) ^ 3 / M ^ 4 := by
  have hzero : (0 : Real) ∈ Set.Icc (0 : Real) 8 := by norm_num
  have hS₀ : 0 <= S₀ :=
    (abs_nonneg (sigma 0)).trans (hsigmaBound 0 hzero)
  have hS₁ : 0 <= S₁ :=
    (abs_nonneg (deriv sigma 0)).trans (hderiv 0 hzero)
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  let B : Real :=
    60000 * Real.pi * x * H * (shiftLength x M) ^ 3 / M ^ 4
  let D : Real :=
    480000 * Real.pi * x * H * (shiftLength x M) ^ 3 / M ^ 4
  have hu : ∀ i, i <= ⌊8 * shiftLength x M⌋₊ →
      ‖section8SigmaWeight sigma (shiftLength x M) i‖ <= S₀ := by
    intro i hi
    exact section8SigmaWeight_norm_le hsigmaBound hN hi
  have hv : ∀ i, i <= ⌊8 * shiftLength x M⌋₊ →
      ‖section8PhaseErrorFactor x a c h i‖ <= B := by
    intro i hi
    simpa only [B] using
      section8PhaseErrorFactor_norm_le hmain hfarey hh hi
  have hdu :
      (∑ i ∈ Finset.range ⌊8 * shiftLength x M⌋₊,
        ‖section8SigmaWeight sigma (shiftLength x M) i -
          section8SigmaWeight sigma (shiftLength x M) (i + 1)‖) <=
        8 * S₁ :=
    section8SigmaWeight_difference_sum_le_eight hsigma hS₁ hderiv hN
  have hdv :
      (∑ i ∈ Finset.range ⌊8 * shiftLength x M⌋₊,
        ‖section8PhaseErrorFactor x a c h i -
          section8PhaseErrorFactor x a c h (i + 1)‖) <= D := by
    simpa only [D] using
      section8PhaseErrorFactor_difference_sum_le hmain hfarey hh
  have hvariation :
      FiniteComplexAbel.variation
          (fun i ↦ section8SigmaWeight sigma (shiftLength x M) i *
            section8PhaseErrorFactor x a c h i)
          ⌊8 * shiftLength x M⌋₊ <=
        S₀ * B + B * (8 * S₁) + S₀ * D :=
    FiniteComplexAbel.variation_mul_le_of_uniform_norm_and_difference_sum_bounds
      (section8SigmaWeight sigma (shiftLength x M))
      (section8PhaseErrorFactor x a c h) ⌊8 * shiftLength x M⌋₊
      S₀ B (8 * S₁) D hu hv hdu hdv
  calc
    FiniteComplexAbel.variation
        (fun i ↦ section8SigmaWeight sigma (shiftLength x M) i *
          section8PhaseErrorFactor x a c h i)
        ⌊8 * shiftLength x M⌋₊ <=
      S₀ * B + B * (8 * S₁) + S₀ * D := hvariation
    _ = 60000 * Real.pi * (9 * S₀ + 8 * S₁) * x * H *
        (shiftLength x M) ^ 3 / M ^ 4 := by
      dsimp [B, D]
      ring

/-- For one fixed Section 8 weight, a single nonnegative constant controls the
preceding product variation uniformly in every main-range scale, Farey point,
and Fourier frequency.  The constant is chosen before all arithmetic
parameters; the remaining scale is still the exact pre-absorption expression
`x * H * N^3 / M^4`. -/
theorem exists_section8SigmaPhaseError_variation_constant
    {sigma : Real → Real} (hsigma : IsSmoothWeight sigma 4 8) :
    ∃ C : Real, 0 <= C ∧
      ∀ (x H M : Real) (a c h : Nat),
        InMainRange x H M → InFareySet x H M a c →
          h ∈ intRange H (4 * H) →
            FiniteComplexAbel.variation
                (fun i ↦ section8SigmaWeight sigma (shiftLength x M) i *
                  section8PhaseErrorFactor x a c h i)
                ⌊8 * shiftLength x M⌋₊ <=
              C * (x * H * (shiftLength x M) ^ 3 / M ^ 4) := by
  obtain ⟨S, hS, hbounds⟩ := exists_section8_smoothWeight_C1_bound hsigma
  let C : Real := 1020000 * Real.pi * S
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro x H M a c h hmain hfarey hh
    have hvariation := section8SigmaPhaseError_variation_le
      (S₀ := S) (S₁ := S) hsigma
      (fun t ht ↦ (hbounds t ht).1) (fun t ht ↦ (hbounds t ht).2)
      hmain hfarey hh
    calc
      FiniteComplexAbel.variation
          (fun i ↦ section8SigmaWeight sigma (shiftLength x M) i *
            section8PhaseErrorFactor x a c h i)
          ⌊8 * shiftLength x M⌋₊ <=
        60000 * Real.pi * (9 * S + 8 * S) * x * H *
          (shiftLength x M) ^ 3 / M ^ 4 := hvariation
      _ = C * (x * H * (shiftLength x M) ^ 3 / M ^ 4) := by
        dsimp [C]
        ring

end

end LeanProofs.IntegerPoints
