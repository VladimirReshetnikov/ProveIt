import FabiusFunction.DyadicAnalytic
import FabiusFunction.ScaleTranslation
import Mathlib.Analysis.Calculus.Taylor

/-!
# Taylor reduction for the signed Fabius function

This module turns the translated-remainder cancellation theorem into the
finite recursive formula of Proposition 10.  The proof handles nonnegative
indices by Taylor expansion and negative indices directly by the
power-of-two sign-translation law.  It also records the constant order-zero
polynomial, its value at the Taylor base point, and sign-specialized wrappers
that remove the conditional from the public reduction formula.
-/

open scoped BigOperators ContDiff Interval
open Finset Set

namespace Fabius

set_option autoImplicit false

/-- The finite Taylor sum occurring in Proposition 10. -/
noncomputable def fabiusReductionSum (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1),
    (2 : ℝ) ^ ((Nat.choose (k + 1) 2 : ℤ) - Nat.choose (n - k) 2) *
      (halfMoment (n - k) : ℝ) / (n - k).factorial * y ^ k / k.factorial

/-- The order-zero reduction polynomial is the constant polynomial `1`. -/
theorem fabiusReductionSum_zero (y : ℝ) :
    fabiusReductionSum 0 y = 1 := by
  simp [fabiusReductionSum, halfMoment_zero]

/-- At the Taylor base point only the constant coefficient survives. -/
theorem fabiusReductionSum_at_zero (n : ℕ) :
    fabiusReductionSum n 0 =
      (2 : ℝ) ^ (-((n.choose 2 : ℕ) : ℤ)) *
        (halfMoment n : ℝ) / n.factorial := by
  rw [fabiusReductionSum, Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [zero_pow hk0]
  · simp

private theorem global_taylor_integral_remainder
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (x₀ x : ℝ) :
    extendedFabius F x -
        ∑ k ∈ range (n + 1),
          (x - x₀) ^ k / k.factorial * iteratedDeriv k (extendedFabius F) x₀ =
      (∫ t in x₀..x,
        (x - t) ^ n * iteratedDeriv (n + 1) (extendedFabius F) t) /
          n.factorial := by
  rcases eq_or_ne x₀ x with rfl | hne
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      simp [zero_pow hk0]
    · simp
  let s : Set ℝ := uIcc x₀ x
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_uIcc hne
  have hcont : ContDiffOn ℝ (n + 1 : ℕ) (extendedFabius F) s :=
    (extendedFabius_contDiff F hF).contDiffOn.of_le (by
      exact WithTop.coe_le_coe.mpr le_top)
  have ht := taylor_integral_remainder hcont
  have hx₀s : x₀ ∈ s := left_mem_uIcc
  rw [taylor_within_apply] at ht
  have hcoeff :
      (∑ k ∈ range (n + 1),
        (((k.factorial : ℝ)⁻¹ * (x - x₀) ^ k) •
          iteratedDerivWithin k (extendedFabius F) s x₀)) =
      ∑ k ∈ range (n + 1),
        (x - x₀) ^ k / k.factorial * iteratedDeriv k (extendedFabius F) x₀ := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv hs
      ((extendedFabius_contDiff F hF).contDiffAt.of_le (by
        exact WithTop.coe_le_coe.mpr le_top)) hx₀s]
    simp only [smul_eq_mul]
    ring
  rw [hcoeff] at ht
  have hintegral :
      (∫ t in x₀..x,
          ((x - t) ^ n / (n.factorial : ℝ)) •
            iteratedDerivWithin (n + 1) (extendedFabius F) s t) =
        (∫ t in x₀..x,
          (x - t) ^ n * iteratedDeriv (n + 1) (extendedFabius F) t) /
            n.factorial := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t htmem
    change ((x - t) ^ n / (n.factorial : ℝ)) *
        iteratedDerivWithin (n + 1) (extendedFabius F) s t =
      ((x - t) ^ n * iteratedDeriv (n + 1) (extendedFabius F) t) /
        n.factorial
    rw [iteratedDerivWithin_eq_iteratedDeriv hs
      ((extendedFabius_contDiff F hF).contDiffAt.of_le (by
        exact WithTop.coe_le_coe.mpr le_top)) htmem]
    ring
  rw [hintegral] at ht
  exact ht

private theorem extendedFabius_inverse_two_pow
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    extendedFabius F ((2 : ℝ) ^ (-(m : ℤ))) =
      (halfMoment m : ℝ) /
        ((m.factorial : ℝ) * (2 : ℝ) ^ m.choose 2) := by
  have harg : (2 : ℝ) ^ (-(m : ℤ)) = 1 / (2 : ℝ) ^ m := by
    rw [zpow_neg, zpow_natCast]
    simp only [one_div]
  have hx : (2 : ℝ) ^ (-(m : ℤ)) ∈ Icc (0 : ℝ) 1 := by
    rw [harg]
    constructor
    · positivity
    · simpa only [one_div] using
        (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num) :
          (1 : ℝ) ≤ (2 : ℝ) ^ m))
  rw [extendedFabius_eq_fabiusReal F hF hx]
  have hcast := fabiusDyadic_cast F hF m 1 Nat.one_le_two_pow
  have hpoint : ((1 : ℕ) : ℝ) / (2 : ℝ) ^ m =
      (2 : ℝ) ^ (-(m : ℤ)) := by norm_num [harg]
  rw [hpoint] at hcast
  rw [← hcast, ← fabiusAtInverseTwoPow, fabiusAtInverseTwoPow_eq_halfMoment,
    halfMomentFabiusValue]
  push_cast
  rfl

/-- The constant coefficient of the order-`n` reduction polynomial is the
analytic value at the inverse dyadic Taylor base point. -/
theorem fabiusReductionSum_at_zero_eq_extendedFabius
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReductionSum n 0 =
      extendedFabius F ((2 : ℝ) ^ (-(n : ℤ))) := by
  rw [fabiusReductionSum_at_zero,
    extendedFabius_inverse_two_pow F hF, zpow_neg, zpow_natCast]
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ n.choose 2 ≠ 0 := by positivity
  field_simp [hfac, hpow]

private theorem taylorAtInverse_eq_reduction
    (F : BoundedFabius) (hF : IsFabius F) (N : ℕ) (y : ℝ) :
    (∑ k ∈ range (N + 1),
      y ^ k / k.factorial *
        iteratedDeriv k (extendedFabius F) ((2 : ℝ) ^ (-(N : ℤ)))) =
      fabiusReductionSum N y := by
  rw [fabiusReductionSum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by simpa using Finset.mem_range.mp hk
  have harg : (2 : ℝ) ^ k * (2 : ℝ) ^ (-(N : ℤ)) =
      (2 : ℝ) ^ (-((N - k : ℕ) : ℤ)) := by
    rw [← zpow_natCast]
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega
  rw [iteratedDeriv_extendedFabius F hF, harg,
    extendedFabius_inverse_two_pow F hF]
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
  ring

/-- Proposition 10's recursive reduction formula for the signed extension. -/
theorem extendedFabius_reduction (F : BoundedFabius) (hF : IsFabius F)
    (x : ℝ) (n : ℤ)
    (hx : 0 < x)
    (hlo : (2 : ℝ) ^ (-n) ≤ x)
    (hhi : x < (2 : ℝ) ^ (-n + 1)) :
    let y := x - (2 : ℝ) ^ (-n)
    extendedFabius F x = -extendedFabius F y +
      if 0 ≤ n then fabiusReductionSum n.toNat y else 0 := by
  dsimp only
  by_cases hn : 0 ≤ n
  · rw [if_pos hn]
    let N : ℕ := n.toNat
    let a : ℝ := (2 : ℝ) ^ (-n)
    let y : ℝ := x - a
    have hNcast : (N : ℤ) = n := Int.toNat_of_nonneg hn
    have hbase : a = (2 : ℝ) ^ (-(N : ℤ)) := by
      dsimp only [a]
      rw [hNcast]
    have horder : (0 : ℤ) ≤ -n + N := by rw [hNcast]; omega
    have hrem := taylorRemainder_translate F hF x (-n) N hx hlo hhi horder
    have htA := global_taylor_integral_remainder F hF N a x
    have ht0 := global_taylor_integral_remainder F hF N 0 y
    have hzeroDeriv : ∀ k : ℕ,
        iteratedDeriv k (extendedFabius F) 0 = 0 := by
      intro k
      rw [iteratedDeriv_extendedFabius F hF,
        show (2 : ℝ) ^ k * 0 = 0 by ring,
        extendedFabius_eq_zero_of_nonpos F hF (by norm_num : (0 : ℝ) ≤ 0)]
      ring
    have hzeroSum :
        (∑ k ∈ range (N + 1),
          (y - 0) ^ k / k.factorial * iteratedDeriv k (extendedFabius F) 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hzeroDeriv]
      ring
    have hTaylor :
        (∑ k ∈ range (N + 1),
          (x - a) ^ k / k.factorial * iteratedDeriv k (extendedFabius F) a) =
          fabiusReductionSum N y := by
      rw [show x - a = y by rfl, hbase]
      exact taylorAtInverse_eq_reduction F hF N y
    rw [hTaylor] at htA
    rw [hzeroSum] at ht0
    simp only [sub_zero] at ht0
    have hrem' :
        (∫ t in a..x,
          (x - t) ^ N * iteratedDeriv (N + 1) (extendedFabius F) t) =
        -(∫ t in 0..y,
          (y - t) ^ N * iteratedDeriv (N + 1) (extendedFabius F) t) := by
      simpa only [a, y] using hrem
    rw [hrem'] at htA
    change extendedFabius F x = -extendedFabius F y + fabiusReductionSum N y
    linear_combination htA + ht0
  · rw [if_neg hn, add_zero]
    have hnneg : n < 0 := lt_of_not_ge hn
    let r : ℕ := (-n).toNat
    let a : ℝ := (2 : ℝ) ^ (-n)
    let y : ℝ := x - a
    have hrCast : (r : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    have hr : 1 ≤ r := by
      have : (1 : ℤ) ≤ -n := by omega
      rw [← hrCast] at this
      exact_mod_cast this
    have hpow : (2 : ℝ) ^ r = a := by
      dsimp only [a]
      rw [← zpow_natCast, hrCast]
    have hy0 : 0 ≤ y := by dsimp only [y, a]; linarith
    have hpowSucc : (2 : ℝ) ^ (-n + 1) = 2 * a := by
      dsimp only [a]
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
      ring
    have hyle : y ≤ (2 : ℝ) ^ r := by
      rw [hpow]
      rw [hpowSucc] at hhi
      dsimp only [y]
      linarith
    have hs := extendedFabius_add_pow_two F hF r hr hy0 hyle
    change extendedFabius F x = -extendedFabius F y
    convert hs using 1
    dsimp only [y]
    rw [hpow]
    ring_nf

/-- Natural-index form of `extendedFabius_reduction`.  The nonnegative branch
is selected definitionally, so its conclusion contains no conditional. -/
theorem extendedFabius_reduction_nat
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) (n : ℕ)
    (hx : 0 < x)
    (hlo : (2 : ℝ) ^ (-((n : ℤ))) ≤ x)
    (hhi : x < (2 : ℝ) ^ (-((n : ℤ)) + 1)) :
    let y := x - (2 : ℝ) ^ (-((n : ℤ)))
    extendedFabius F x = -extendedFabius F y + fabiusReductionSum n y := by
  have hn : (0 : ℤ) ≤ (n : ℤ) := by omega
  simpa [hn] using extendedFabius_reduction F hF x (n : ℤ) hx hlo hhi

/-- Negative-index form of `extendedFabius_reduction`.  In this range the
Taylor polynomial disappears and the formula is exactly sign translation. -/
theorem extendedFabius_reduction_of_neg
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) (n : ℤ)
    (hn : n < 0) (hx : 0 < x)
    (hlo : (2 : ℝ) ^ (-n) ≤ x)
    (hhi : x < (2 : ℝ) ^ (-n + 1)) :
    let y := x - (2 : ℝ) ^ (-n)
    extendedFabius F x = -extendedFabius F y := by
  have hn' : ¬ (0 : ℤ) ≤ n := not_le_of_gt hn
  simpa [hn'] using
    extendedFabius_reduction F hF x n hx hlo hhi

end Fabius
