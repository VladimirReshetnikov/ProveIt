import IntegerPoints.IwaniecMozzochi
import IntegerPoints.PoissonBounds

/-!
# The bounded Fourier expansion in Iwaniec--Mozzochi §3

This file proves the bounded truncated Fourier expansion of the sawtooth
function stated in `IntegerPoints.IwaniecMozzochi`.  The proof combines the
sharp interior estimate from `IntegerPoints.Sawtooth` with the uniform bound
from `IntegerPoints.PoissonBounds`.  The latter is essential at integral
arguments, where the sawtooth convention has value `-1 / 2`.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

private theorem sum_Icc_one_sine_eq_S (H : ℕ) (t : ℝ) :
    ∑ h ∈ Finset.Icc 1 H, Real.sin (2 * π * h * t) / (π * h) = Sawtooth.S H t := by
  unfold Sawtooth.S
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le H)),
        Finset.sum_range_succ, ih]
      norm_num

/-- On the unit interval, the distance to the nearest integer is the distance
to the nearer endpoint. -/
private theorem nearestIntDist_eq_min_fract (t : ℝ) :
    nearestIntDist t = min (Int.fract t) (1 - Int.fract t) := by
  let u := Int.fract t
  have hu0 : 0 ≤ u := Int.fract_nonneg t
  have hu1 : u < 1 := Int.fract_lt_one t
  have hperiod : nearestIntDist u = nearestIntDist t := by
    change nearestIntDist (Int.fract t) = nearestIntDist t
    rw [Int.fract, KL.nearestIntDist_sub_int]
  have lower_of_half {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
      x ≤ nearestIntDist x := by
    unfold nearestIntDist
    rcases le_or_gt (round x) 0 with h | h
    · have hr : ((round x : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hr : (1 : ℝ) ≤ ((round x : ℤ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
  change nearestIntDist t = min u (1 - u)
  rcases le_or_gt u (1 / 2) with hu | hu
  · rw [min_eq_left (by linarith)]
    apply le_antisymm
    · rw [← hperiod]
      have h := KL.nearestIntDist_le u 0
      simpa [abs_of_nonneg hu0] using h
    · rw [← hperiod]
      exact lower_of_half hu0 hu
  · rw [min_eq_right (by linarith)]
    apply le_antisymm
    · rw [← hperiod]
      have h := KL.nearestIntDist_le u 1
      rw [Int.cast_one, abs_of_nonpos (by linarith)] at h
      linarith
    · calc
        1 - u ≤ nearestIntDist (1 - u) :=
          lower_of_half (by linarith) (by linarith)
        _ = nearestIntDist (u - 1) := by
          rw [show 1 - u = -(u - 1) by ring, KL.nearestIntDist_neg]
        _ = nearestIntDist u := by
          simpa using (KL.nearestIntDist_sub_int u (1 : ℤ))
        _ = nearestIntDist t := hperiod

/-- The bounded Fourier expansion of the sawtooth function used in
Iwaniec--Mozzochi §3. -/
theorem sawtooth_fourierExpansion_holds : sawtooth_fourierExpansion := by
  refine ⟨16, ?_⟩
  intro t y hy
  let H := ⌊y⌋₊
  let d := nearestIntDist t
  have hH : 1 ≤ H := by
    dsimp [H]
    exact (Nat.one_le_floor_iff y).2 hy
  have hHreal : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hylt : y < (H : ℝ) + 1 := by
    dsimp [H]
    simpa using Nat.lt_floor_add_one y
  have hyH : y ≤ 2 * (H : ℝ) := by nlinarith
  have hsum :
      ∑ h ∈ upTo y, Real.sin (2 * π * h * t) / (π * h) = Sawtooth.S H t := by
    simpa only [upTo, H] using sum_Icc_one_sine_eq_S H t
  rw [hsum]
  change |EM.ψ t + Sawtooth.S H t| ≤ 16 * (1 + d * y)⁻¹
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact PS.nearestIntDist_nonneg t
  have hdy0 : 0 ≤ d * y := mul_nonneg hd0 hy0.le
  have hden : 0 < 1 + d * y := by linarith
  rcases le_or_gt (d * y) 1 with hsmall | hlarge
  · calc
      |EM.ψ t + Sawtooth.S H t| ≤ 9 / 2 := PS.abs_ψ_add_S_le H t
      _ ≤ 16 * (1 + d * y)⁻¹ := by
        rw [← div_eq_mul_inv]
        apply (le_div_iff₀ hden).2
        nlinarith
  · have hdpos : 0 < d := by
      by_contra h
      have hdle : d ≤ 0 := le_of_not_gt h
      have : d * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hdle hy0.le
      linarith
    let u := Int.fract t
    have hu0 : 0 ≤ u := Int.fract_nonneg t
    have hu1 : u < 1 := Int.fract_lt_one t
    have hdmin : d = min u (1 - u) := by
      dsimp [d, u]
      exact nearestIntDist_eq_min_fract t
    have hminpos : 0 < min u (1 - u) := by rw [← hdmin]; exact hdpos
    have hupos : 0 < u := lt_of_lt_of_le hminpos (min_le_left _ _)
    have hS : Sawtooth.S H t = Sawtooth.S H u := by
      calc
        Sawtooth.S H t = Sawtooth.S H (u + (⌊t⌋ : ℤ)) := by
          simp [u]
        _ = Sawtooth.S H u := PS.S_add_int H u ⌊t⌋
    have hpsi : EM.ψ t = u - 1 / 2 := by simp [EM.ψ, u]
    have hprecise :
        |EM.ψ t + Sawtooth.S H t| ≤ 4 / ((H : ℝ) * d) := by
      calc
        |EM.ψ t + Sawtooth.S H t| = |(u - 1 / 2) + Sawtooth.S H u| := by
          rw [hpsi, hS]
        _ ≤ 4 / ((H : ℝ) * min u (1 - u)) :=
          Sawtooth.sawtooth_expansion hH hupos hu1
        _ = 4 / ((H : ℝ) * d) := by rw [hdmin]
    have hdyH : d * y ≤ d * (2 * (H : ℝ)) :=
      mul_le_mul_of_nonneg_left hyH hd0
    have hHd : 0 < (H : ℝ) * d :=
      mul_pos (lt_of_lt_of_le zero_lt_one hHreal) hdpos
    calc
      |EM.ψ t + Sawtooth.S H t| ≤ 4 / ((H : ℝ) * d) := hprecise
      _ ≤ 16 * (1 + d * y)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ hHd hden]
        nlinarith

end LeanProofs.IntegerPoints
