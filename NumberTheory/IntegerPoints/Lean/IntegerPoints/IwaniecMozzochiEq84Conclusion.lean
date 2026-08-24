import IntegerPoints.IwaniecMozzochiEq84AbelAssembly
import IntegerPoints.IwaniecMozzochiEq84PhaseVariation
import Mathlib.Tactic

/-!
# Completion of Iwaniec--Mozzochi (8.4)

This module closes the remaining finite and scale-arithmetic steps in (8.4).
The exact perturbation sum from `IwaniecMozzochiEq84` is first identified with
the product weight used by finite Abel summation.  The already proved
quadratic-prefix bound and the concrete remainder-phase variation then give

`(802 / sqrt beta) * (C_sigma * x * H * N^3 / M^4)`.

The last lemma below performs the paper's scale calculation without any new
analytic premise.  Enlarging the model denominator from `8 * M^3` to
`16 * M^3` gives the convenient reciprocal-square-root constant `4`; the main
range bound `H <= M * x^(-theta0)` and the exact definition of `N` reduce the
remaining factor to

`4 * M * x^(-7 * (1 - theta0) / 10)`,

which is controlled by the existing terminal exponent comparison.  Thus the
final constant is selected after the fixed weight (and the harmless fixed
parameter `mu1`) but before every arithmetic parameter, exactly as required by
`iwaniecMozzochi_eq84`.
-/

open Real Set
open scoped BigOperators

namespace LeanProofs.IntegerPoints

noncomputable section

/-! ## Elementary square-root and scale identities -/

private theorem section8_sqrt_cube_eq_rpow_three_halves
    {M : Real} (hM : 0 <= M) :
    Real.sqrt (M ^ 3) = M ^ ((3 : Real) / 2) := by
  calc
    Real.sqrt (M ^ 3) = (M ^ 3) ^ ((1 : Real) / 2) :=
      Real.sqrt_eq_rpow _
    _ = (M ^ (3 : Real)) ^ ((1 : Real) / 2) := by
      exact congrArg (fun t : Real => t ^ ((1 : Real) / 2))
        (Real.rpow_natCast M 3).symm
    _ = M ^ ((3 : Real) * ((1 : Real) / 2)) :=
      (Real.rpow_mul hM (3 : Real) ((1 : Real) / 2)).symm
    _ = M ^ ((3 : Real) / 2) := by
      congr 1
      ring

private theorem section8_sqrt_rpow
    {x r : Real} (hx : 0 <= x) :
    Real.sqrt (x ^ r) = x ^ (r / 2) := by
  calc
    Real.sqrt (x ^ r) = (x ^ r) ^ ((1 : Real) / 2) :=
      Real.sqrt_eq_rpow _
    _ = x ^ (r * ((1 : Real) / 2)) :=
      (Real.rpow_mul hx r ((1 : Real) / 2)).symm
    _ = x ^ (r / 2) := by
      congr 1
      ring

private theorem section8_shiftLength_cube
    {x M : Real} (hx : 0 <= x) :
    (shiftLength x M) ^ 3 =
      M ^ 3 * x ^ (-(6 : Real) / 5 * (1 - theta0)) := by
  unfold shiftLength
  calc
    (M * x ^ (-(2 : Real) / 5 * (1 - theta0))) ^ 3 =
        M ^ 3 * (x ^ (-(2 : Real) / 5 * (1 - theta0))) ^ 3 := by
      rw [mul_pow]
    _ = M ^ 3 *
        x ^ ((-(2 : Real) / 5 * (1 - theta0)) * (3 : Nat)) := by
      rw [Real.rpow_mul_natCast hx]
    _ = M ^ 3 * x ^ (-(6 : Real) / 5 * (1 - theta0)) := by
      congr 1
      ring

/-! ## Absorption of the beta and remainder scales -/

/-- The exact scale calculation following (8.3).  It is stated for an
arbitrary positive `beta` satisfying the already proved model lower bound, so
the algebra is reusable independently of the definition of `betaIM`.

The factor on the left is literally the one produced by the Abel-prefix
estimate.  Equivalently, `1 / sqrt beta = beta ^ (-1/2)` for positive `beta`.
-/
theorem section8_reciprocal_sqrt_beta_remainder_scale_le
    {x H M beta : Real}
    (hmain : InMainRange x H M) (hbeta : 0 < beta)
    (hbetaLower : x * H / (8 * M ^ 3) <= beta) :
    (1 / Real.sqrt beta) *
        (x * H * (shiftLength x M) ^ 3 / M ^ 4) <=
      4 * x ^ ((1 : Real) / 44) := by
  rcases hmain with
    ⟨hx, hxM, hMsqrt, hH, hHupper, hHlower, hHlowerTwo, hMlower⟩
  have hmain' : InMainRange x H M :=
    ⟨hx, hxM, hMsqrt, hH, hHupper, hHlower, hHlowerTwo, hMlower⟩
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  have hMPos : 0 < M := (Real.rpow_pos_of_pos hxPos theta0).trans hxM
  have hNPos : 0 < shiftLength x M := section8_shiftLength_pos hmain'
  have hxHPos : 0 < x * H := mul_pos hxPos hHPos
  have hsqrtBetaPos : 0 < Real.sqrt beta := Real.sqrt_pos.2 hbeta
  have hsqrtXHPos : 0 < Real.sqrt (x * H) := Real.sqrt_pos.2 hxHPos

  have hxHLeEight :
      x * H <= (8 * M ^ 3) * beta := by
    have hdenPos : 0 < 8 * M ^ 3 :=
      mul_pos (by norm_num) (pow_pos hMPos 3)
    have h := (div_le_iff₀ hdenPos).1 hbetaLower
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  have hxHLeSixteen :
      x * H <= 16 * M ^ 3 * beta := by
    calc
      x * H <= (8 * M ^ 3) * beta := hxHLeEight
      _ = 8 * (M ^ 3 * beta) := by ring
      _ <= 16 * (M ^ 3 * beta) :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg (pow_nonneg hMPos.le 3) hbeta.le)
      _ = 16 * M ^ 3 * beta := by ring
  have hsqrtModel :
      Real.sqrt (x * H) <=
        4 * M ^ ((3 : Real) / 2) * Real.sqrt beta := by
    have hsqrt := Real.sqrt_le_sqrt hxHLeSixteen
    calc
      Real.sqrt (x * H) <= Real.sqrt (16 * M ^ 3 * beta) := hsqrt
      _ = Real.sqrt 16 * Real.sqrt (M ^ 3 * beta) := by
        rw [show 16 * M ^ 3 * beta = 16 * (M ^ 3 * beta) by ring,
          Real.sqrt_mul (by norm_num : (0 : Real) <= 16)]
      _ = Real.sqrt 16 * (Real.sqrt (M ^ 3) * Real.sqrt beta) := by
        rw [Real.sqrt_mul (pow_nonneg hMPos.le 3)]
      _ = 4 * M ^ ((3 : Real) / 2) * Real.sqrt beta := by
        rw [section8_sqrt_cube_eq_rpow_three_halves hMPos.le]
        norm_num
        ring
  have hreciprocal :
      1 / Real.sqrt beta <=
        (4 * M ^ ((3 : Real) / 2)) / Real.sqrt (x * H) := by
    apply (div_le_div_iff₀ hsqrtBetaPos hsqrtXHPos).2
    simpa only [one_mul] using hsqrtModel

  have hxHDivSqrt :
      (x * H) / Real.sqrt (x * H) = Real.sqrt (x * H) := by
    apply (div_eq_iff hsqrtXHPos.ne').2
    exact (Real.mul_self_sqrt hxHPos.le).symm
  have hxHUpper :
      x * H <= M * x ^ (1 - theta0) := by
    calc
      x * H <= x * (M * x ^ (-theta0)) :=
        mul_le_mul_of_nonneg_left hHupper hxPos.le
      _ = M * (x ^ (1 : Real) * x ^ (-theta0)) := by
        rw [Real.rpow_one]
        ring
      _ = M * x ^ ((1 : Real) + (-theta0)) := by
        rw [Real.rpow_add hxPos]
      _ = M * x ^ (1 - theta0) := by
        ring
  have hsqrtXHUpper :
      Real.sqrt (x * H) <=
        Real.sqrt M * x ^ ((1 - theta0) / 2) := by
    calc
      Real.sqrt (x * H) <= Real.sqrt (M * x ^ (1 - theta0)) :=
        Real.sqrt_le_sqrt hxHUpper
      _ = Real.sqrt M * Real.sqrt (x ^ (1 - theta0)) := by
        rw [Real.sqrt_mul hMPos.le]
      _ = Real.sqrt M * x ^ ((1 - theta0) / 2) := by
        rw [section8_sqrt_rpow hxPos.le]
  have hMThreeHalvesMulSqrt :
      M ^ ((3 : Real) / 2) * Real.sqrt M = M ^ 2 := by
    rw [Real.sqrt_eq_rpow]
    calc
      M ^ ((3 : Real) / 2) * M ^ ((1 : Real) / 2) =
          M ^ ((3 : Real) / 2 + (1 : Real) / 2) :=
        (Real.rpow_add hMPos _ _).symm
      _ = M ^ (2 : Real) := by
        congr 1
        norm_num
      _ = M ^ 2 := Real.rpow_natCast M 2
  have hNcube := section8_shiftLength_cube (x := x) (M := M) hxPos.le
  have hexponent :
      (1 - theta0) / 2 + (-(6 : Real) / 5 * (1 - theta0)) =
        -(7 : Real) / 10 * (1 - theta0) := by
    ring
  have hremainingNonneg :
      0 <= (shiftLength x M) ^ 3 / M ^ 4 :=
    div_nonneg (pow_nonneg hNPos.le 3) (pow_nonneg hMPos.le 4)
  have hfullScaleNonneg :
      0 <= x * H * (shiftLength x M) ^ 3 / M ^ 4 :=
    div_nonneg
      (mul_nonneg (mul_nonneg hxPos.le hHPos.le) (pow_nonneg hNPos.le 3))
      (pow_nonneg hMPos.le 4)

  calc
    (1 / Real.sqrt beta) *
          (x * H * (shiftLength x M) ^ 3 / M ^ 4) <=
        ((4 * M ^ ((3 : Real) / 2)) / Real.sqrt (x * H)) *
          (x * H * (shiftLength x M) ^ 3 / M ^ 4) :=
      mul_le_mul_of_nonneg_right hreciprocal hfullScaleNonneg
    _ = (4 * M ^ ((3 : Real) / 2)) *
        ((x * H) / Real.sqrt (x * H)) *
          ((shiftLength x M) ^ 3 / M ^ 4) := by ring
    _ = (4 * M ^ ((3 : Real) / 2)) * Real.sqrt (x * H) *
          ((shiftLength x M) ^ 3 / M ^ 4) := by
      rw [hxHDivSqrt]
    _ <= (4 * M ^ ((3 : Real) / 2)) *
        (Real.sqrt M * x ^ ((1 - theta0) / 2)) *
          ((shiftLength x M) ^ 3 / M ^ 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrtXHUpper
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hMPos.le _)))
        hremainingNonneg
    _ = 4 * (M ^ ((3 : Real) / 2) * Real.sqrt M) *
          x ^ ((1 - theta0) / 2) *
            ((shiftLength x M) ^ 3 / M ^ 4) := by ring
    _ = 4 * M ^ 2 * x ^ ((1 - theta0) / 2) *
          ((shiftLength x M) ^ 3 / M ^ 4) := by
      rw [hMThreeHalvesMulSqrt]
    _ = 4 * M ^ 2 * x ^ ((1 - theta0) / 2) *
          (M ^ 3 * x ^ (-(6 : Real) / 5 * (1 - theta0)) / M ^ 4) := by
      rw [hNcube]
    _ = 4 * M *
          (x ^ ((1 - theta0) / 2) *
            x ^ (-(6 : Real) / 5 * (1 - theta0))) := by
      field_simp [hMPos.ne']
    _ = 4 * M * x ^
          ((1 - theta0) / 2 + (-(6 : Real) / 5 * (1 - theta0))) := by
      rw [Real.rpow_add hxPos]
    _ = 4 * (M * x ^ (-(7 : Real) / 10 * (1 - theta0))) := by
      rw [hexponent]
      ring
    _ <= 4 * x ^ ((1 : Real) / 44) :=
      mul_le_mul_of_nonneg_left (section8_final_scale_le hmain') (by norm_num)

/-- The preceding absorption in the literal `beta ^ (-1/2)` notation used in
the paper. -/
theorem section8_beta_rpow_neg_half_remainder_scale_le
    {x H M beta : Real}
    (hmain : InMainRange x H M) (hbeta : 0 < beta)
    (hbetaLower : x * H / (8 * M ^ 3) <= beta) :
    beta ^ (-(1 : Real) / 2) *
        (x * H * (shiftLength x M) ^ 3 / M ^ 4) <=
      4 * x ^ ((1 : Real) / 44) := by
  have hconvert :
      beta ^ (-(1 : Real) / 2) = 1 / Real.sqrt beta := by
    calc
      beta ^ (-(1 : Real) / 2) =
          beta ^ (-((1 : Real) / 2)) := by
        congr 1
        ring
      _ = (beta ^ ((1 : Real) / 2))⁻¹ :=
        Real.rpow_neg hbeta.le ((1 : Real) / 2)
      _ = (Real.sqrt beta)⁻¹ := by rw [Real.sqrt_eq_rpow]
      _ = 1 / Real.sqrt beta := by rw [one_div]
  rw [hconvert]
  exact section8_reciprocal_sqrt_beta_remainder_scale_le
    hmain hbeta hbetaLower

/-! ## Exact finite-sum alignment and Abel estimate -/

/-- The summand in `section8_error_eq_perturbation_sum` is exactly the product
weight used by Abel summation times the pure quadratic exponential.  This
identity records the support/range alignment explicitly; both sides use the
same inclusive `section8WeightRange` and no endpoint is discarded. -/
theorem section8_perturbation_sum_eq_phase_error_sum
    (sigma : Real -> Real) (N alpha beta x : Real) (a c h : Nat) :
    (∑ n ∈ section8WeightRange N,
        (sigma ((n : Real) / N) : Complex) *
          e (alpha * n + beta * (n : Real) ^ 2) *
            (e (section8Remainder x h (fareyPoint x a c)
              (fareyFrac x a c) n) - 1)) =
      ∑ n ∈ section8WeightRange N,
        section8SigmaWeight sigma N n *
          e (section8QuadraticPhase alpha beta n) *
            section8PhaseErrorFactor x a c h n := by
  apply Finset.sum_congr rfl
  intro n _hn
  unfold section8SigmaWeight section8QuadraticPhase section8PhaseErrorFactor
  ring

/-- Abel summation with the already established quadratic-prefix bound and an
explicit bound for the concrete sigma/remainder product variation. -/
theorem section8_phase_error_sum_le_of_variation
    {sigma : Real -> Real} {C : Real} {x H M : Real} {a c h : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H))
    (hvariation :
      FiniteComplexAbel.variation
          (fun i => section8SigmaWeight sigma (shiftLength x M) i *
            section8PhaseErrorFactor x a c h i)
          ⌊8 * shiftLength x M⌋₊ <=
        C * (x * H * (shiftLength x M) ^ 3 / M ^ 4)) :
    ‖∑ n ∈ section8WeightRange (shiftLength x M),
        section8SigmaWeight sigma (shiftLength x M) n *
          e (section8QuadraticPhase (alphaIM x a c h)
            (betaIM x a c h) n) *
            section8PhaseErrorFactor x a c h n‖ <=
      (802 / Real.sqrt (betaIM x a c h)) *
        (C * (x * H * (shiftLength x M) ^ 3 / M ^ 4)) := by
  have hprefix := section8_quadratic_prefixSum_uniform
    (alphaIM x a c h) (betaIM x a c h) (shiftLength x M)
    (one_le_section8_shiftLength hmain)
    (betaIM_pos_of_mem_intRange hmain hfarey hh)
    (betaIM_mul_shiftLength_le_four hmain hfarey hh)
  have hAbel := FiniteComplexAbel.norm_weighted_sum_le_of_variation_le
    (fun n : Nat =>
      e (section8QuadraticPhase (alphaIM x a c h) (betaIM x a c h) n))
    (fun n : Nat =>
      section8SigmaWeight sigma (shiftLength x M) n *
        section8PhaseErrorFactor x a c h n)
    ⌊8 * shiftLength x M⌋₊
    (802 / Real.sqrt (betaIM x a c h))
    (C * (x * H * (shiftLength x M) ^ 3 / M ^ 4))
    hprefix hvariation
  calc
    ‖∑ n ∈ section8WeightRange (shiftLength x M),
        section8SigmaWeight sigma (shiftLength x M) n *
          e (section8QuadraticPhase (alphaIM x a c h)
            (betaIM x a c h) n) *
            section8PhaseErrorFactor x a c h n‖ =
      ‖∑ n ∈ Finset.range (⌊8 * shiftLength x M⌋₊ + 1),
        (section8SigmaWeight sigma (shiftLength x M) n *
          section8PhaseErrorFactor x a c h n) *
            e (section8QuadraticPhase (alphaIM x a c h)
              (betaIM x a c h) n)‖ := by
        apply congrArg norm
        rw [section8WeightRange]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
    _ <= (802 / Real.sqrt (betaIM x a c h)) *
        (C * (x * H * (shiftLength x M) ^ 3 / M ^ 4)) := hAbel

/-! ## Public conclusion -/

/-- Unconditional proof of the public proposition (8.4).  The hypothesis
`mu1 * Gscale x H M < c` is part of the paper's short-cell regime but is not
needed for this stronger analytic estimate. -/
theorem iwaniecMozzochi_eq84_holds : iwaniecMozzochi_eq84 := by
  intro sigma mu1 hsigma _hmu1
  obtain ⟨Cphase, hCphase, hvariation⟩ :=
    exists_section8SigmaPhaseError_variation_constant hsigma
  refine ⟨3208 * Cphase, ?_⟩
  intro x H M a c h hmain hfarey _hshort hh
  have hvariation' := hvariation x H M a c h hmain hfarey hh
  have hsum := section8_phase_error_sum_le_of_variation
    hmain hfarey hh hvariation'
  have hscale := section8_reciprocal_sqrt_beta_remainder_scale_le
    hmain (betaIM_pos_of_mem_intRange hmain hfarey hh)
      (x_mul_H_div_eight_mul_M_cube_le_betaIM hmain hfarey hh)
  rw [section8_error_eq_perturbation_sum hsigma hmain hfarey,
    section8_perturbation_sum_eq_phase_error_sum,
    norm_mul, PS.norm_e_one, one_mul]
  calc
    ‖∑ n ∈ section8WeightRange (shiftLength x M),
        section8SigmaWeight sigma (shiftLength x M) n *
          e (section8QuadraticPhase (alphaIM x a c h)
            (betaIM x a c h) n) *
            section8PhaseErrorFactor x a c h n‖ <=
      (802 / Real.sqrt (betaIM x a c h)) *
        (Cphase * (x * H * (shiftLength x M) ^ 3 / M ^ 4)) := hsum
    _ = (802 * Cphase) *
        ((1 / Real.sqrt (betaIM x a c h)) *
          (x * H * (shiftLength x M) ^ 3 / M ^ 4)) := by ring
    _ <= (802 * Cphase) * (4 * x ^ ((1 : Real) / 44)) :=
      mul_le_mul_of_nonneg_left hscale
        (mul_nonneg (by norm_num) hCphase)
    _ = (3208 * Cphase) * x ^ ((1 : Real) / 44) := by ring

end

end LeanProofs.IntegerPoints
