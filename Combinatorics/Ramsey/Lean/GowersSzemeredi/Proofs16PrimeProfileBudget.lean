import GowersSzemeredi.Proofs16SparseRelationProfile
import GowersSzemeredi.Proofs16PolynomialSpectrumSpan

/-! Explicit modulus-independent cutoff and finite-size budgets for the
prime split-profile estimate. The smoothing radius is floor(tau*N). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A proportional smoothing interval has at least its prescribed mass. -/
theorem centeredBall_floor_mass {N : Nat} [NeZero N] {tau : Real}
    (htau : 0 < tau) (htauHalf : tau < 1 / 2) :
    2 * ⌊tau * N⌋₊ < N ∧ tau * N ≤ ((centeredBall N ⌊tau * N⌋₊).card : Real) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hf := Nat.floor_le (show 0 ≤ tau * N by positivity)
  have hc : 2 * ⌊tau * N⌋₊ < N := by
    have h := mul_lt_mul_of_pos_right htauHalf hN
    have : (2 : Real) * ⌊tau * N⌋₊ < N := by linarith
    exact_mod_cast this
  refine ⟨hc, ?_⟩
  have h := Nat.lt_floor_add_one (tau * N)
  have hcard : (⌊tau * N⌋₊ : Real) + 1 ≤ (centeredBall N ⌊tau * N⌋₊).card := by
    exact_mod_cast centeredBall_card_ge_succ hc
  linarith

/-- The rounded band error lies between 2*m*tau and 6*m*tau once tau*N≥1. -/
theorem prime_profile_band_scaled {N : Nat} [NeZero N] (m : Nat) {tau : Real}
    (htau : 0 < tau) (hN : 1 ≤ tau * N) :
    2 * m * tau ≤ (m : Real) * (4 * ⌊tau * N⌋₊ + 2) / N ∧
      (m : Real) * (4 * ⌊tau * N⌋₊ + 2) / N ≤ 6 * m * tau := by
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hlo := Nat.lt_floor_add_one (tau * N)
  have hhi := Nat.floor_le (show 0 ≤ tau * N by positivity)
  have hm : (0 : Real) ≤ m := Nat.cast_nonneg _
  have hfloor : (0 : Real) ≤ ⌊tau * N⌋₊ := Nat.cast_nonneg _
  constructor
  · apply (le_div_iff₀ hNpos).mpr
    have h : 2 * (tau * N) ≤ 4 * (⌊tau * N⌋₊ : Real) + 2 := by linarith
    have := mul_le_mul_of_nonneg_left h hm
    nlinarith only [this]
  · apply (div_le_iff₀ hNpos).mpr
    have h : 4 * (⌊tau * N⌋₊ : Real) + 2 ≤ 6 * (tau * N) := by linarith
    have := mul_le_mul_of_nonneg_left h hm
    nlinarith only [this]

/-- Cutoff 1/tau² controls the full product error; the tuple dimension
enters only the smallness condition m*tau≤1/2. -/
theorem prime_profile_truncation_scaled {N : Nat} [NeZero N] (m R : Nat) {tau : Real}
    (htau : 0 < tau) (htauHalf : tau < 1 / 2) (hsmall : (m : Real) * tau ≤ 1 / 2)
    (hR : 1 / tau^2 ≤ R + 1) :
    (1 + N / ((centeredBall N ⌊tau * N⌋₊).card * (R + 1 : Real)))^m - 1 ≤ 2 * m * tau := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨hc, hmass⟩ := centeredBall_floor_mass (N := N) htau htauHalf
  have hC : (0 : Real) < (centeredBall N ⌊tau * N⌋₊).card := (mul_pos htau hN).trans_le hmass
  have hcut : 1 ≤ (R + 1 : Real) * tau^2 := (div_le_iff₀ (sq_pos_of_pos htau)).mp hR
  have herr : N / ((centeredBall N ⌊tau * N⌋₊).card * (R + 1 : Real)) ≤ tau := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h1 := mul_le_mul_of_nonneg_right hmass (show 0 ≤ (R + 1 : Real) * tau by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcut hN.le
    nlinarith only [h1, h2]
  have hnonneg : 0 ≤ N / ((centeredBall N ⌊tau * N⌋₊).card * (R + 1 : Real)) := by positivity
  have hscalar := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg m)
  exact (one_add_pow_sub_one_le_twice hnonneg m (hscalar.trans hsmall)).trans (by linarith)

/-- The band budget and the box-error ratio follow from one lower bound
on the base set; all bounds are uniform in the ambient modulus. -/
theorem prime_profile_size_scaled {N : Nat} [NeZero N] (m B : Nat) {tau beta : Real}
    (htau : 0 < tau) (hN : 1 ≤ tau * N) (hbeta : 0 < beta)
    (hB : beta * N ≤ B) (hsmall : 120 * m * tau ≤ beta) :
    20 * ((m : Real) * (4 * ⌊tau * N⌋₊ + 2)) ≤ B ∧
      80 * ((m : Real) * (4 * ⌊tau * N⌋₊ + 2)) / B ≤ 480 * m * tau / beta := by
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hBpos : (0 : Real) < B := (mul_pos hbeta hNpos).trans_le hB
  have hband := (prime_profile_band_scaled (N := N) m htau hN).2
  have hband' := (div_le_iff₀ hNpos).mp hband
  constructor
  · have := mul_le_mul_of_nonneg_right hsmall hNpos.le
    nlinarith
  · apply (div_le_div_iff₀ hBpos hbeta).mpr
    have h1 := mul_le_mul_of_nonneg_right hband' (show 0 ≤ 80 * beta by positivity)
    have h2 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 480 * m * tau by positivity)
    nlinarith only [h1, h2]

end LeanProofs.GowersSzemeredi
