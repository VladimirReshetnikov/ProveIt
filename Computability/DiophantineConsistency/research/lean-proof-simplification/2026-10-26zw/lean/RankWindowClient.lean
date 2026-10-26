import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace DiophantineProofIdeas.RankWindowClient

/-- This is the exact arithmetic contract consumed by source_window_bound:
the unchanged source provides hC, htarget and hscale. -/
theorem window_from_source_identities
    (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ) (R : ℤ)
    (hx : ∀ i, 0 < x i)
    (hMCβ : ports 2 < ports 0) (hMFβ : ports 3 < 2 * ports 0)
    (hC : 0 < (1 + (x 0 : ℤ) * ports 0) - x 1 - x 2)
    (htarget : R = (((1 + (x 0 : ℤ) * ports 0) - 1) *
      ((1 + (x 0 : ℤ) * ports 0) - x 1) + x 2) *
      ((1 + (x 0 : ℤ) * ports 0) ^ 2 - 1) +
      (ports 2 + ports 3 * (1 + (x 0 : ℤ) * ports 0)) * x 0)
    (hscale : (x 17 : ℤ) = (1 + (x 0 : ℤ) * ports 0) ^ 4 * (x 10 * x 9)) :
    R + 1 < (x 17 : ℤ) := by
  let q : ℤ := 1 + (x 0 : ℤ) * ports 0
  have hF : (0 : ℤ) < x 1 := by exact_mod_cast hx 1
  have hα : (0 : ℤ) < x 2 := by exact_mod_cast hx 2
  have hJ : (0 : ℤ) < x 0 := by exact_mod_cast hx 0
  change 0 < q - x 1 - x 2 at hC
  have hq3 : 3 ≤ q := by omega
  have hL : 0 ≤ q ^ 2 - 1 := by nlinarith
  have hF1 : 0 ≤ (x 1 : ℤ) - 1 := by omega
  have hC1 : 0 ≤ q - x 1 - x 2 - 1 := by omega
  have hJ1 : 0 ≤ (x 0 : ℤ) - 1 := by omega
  have hM : 0 ≤ ports 0 - ports 2 - 1 := by omega
  have hH : 0 ≤ 2 * ports 0 - ports 3 - 1 := by omega
  have hgap := add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg (show 0 ≤ q by omega) hL) hF1) (mul_nonneg hL hC1))
    (mul_nonneg (show 0 ≤ q + 1 by omega) hJ1))
    (mul_nonneg hJ.le (add_nonneg hM (mul_nonneg (show 0 ≤ q by omega) hH)))
  have he : q ^ 4 - q ^ 3 - q - 1 - R =
      q * (q ^ 2 - 1) * ((x 1 : ℤ) - 1) + (q ^ 2 - 1) * (q - x 1 - x 2 - 1) +
      (q + 1) * ((x 0 : ℤ) - 1) +
      (x 0 : ℤ) * ((ports 0 - ports 2 - 1) + q * (2 * ports 0 - ports 3 - 1)) := by
    rw [htarget]
    dsimp [q]
    ring
  rw [← he] at hgap
  have hEbound : q ^ 4 ≤ (x 17 : ℤ) := by
    rw [hscale]
    exact le_mul_of_one_le_right (pow_nonneg (show 0 ≤ q by omega) 4)
      (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hx 10) (by exact_mod_cast hx 9))
  have hcube : 0 < q ^ 3 := pow_pos (by omega) _
  omega

#print axioms window_from_source_identities

end DiophantineProofIdeas.RankWindowClient
