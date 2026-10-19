import GowersSzemeredi.Proofs13FejerFourierExtraction
import GowersSzemeredi.Proofs13SpectralExponentBound

/-! The purified graph improves the explicit all-parameter length exponent
from top power 2^88 to 2^53. The density bound is simultaneously 2^42.

`theorem_13_12_fejer_explicit_threshold` and
`theorem_13_12_with_fejer_explicit_bound` are in
`Proofs13FejerExplicitExponentSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_spectral_upper {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    15 * section13Q ((alpha / 2) ^ (4207554485 : Nat)) ≤
      (2 / alpha) ^ ((2 : Nat) ^ 53) := by
  let t := 2 / alpha
  have ht : 2 ≤ t := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hcollapse : ((alpha / 2) ^ (4207554485 : Nat)) ^ (-((2 : Real) ^ 21)) =
      t ^ ((4207554485 : Nat) * (2 : Nat) ^ 21) := by
    rw [Real.rpow_neg (by positivity), show (2 : Real) ^ 21 = ((2 ^ 21 : Nat) : Real) by norm_num,
      Real.rpow_natCast, ← pow_mul, ← inv_pow, inv_div]
  unfold section13Q
  rw [hcollapse]
  calc _ ≤ t ^ 4 * (t ^ (2 ^ 20) * t ^ (4207554485 * 2 ^ 21)) := by
        gcongr
        exact le_trans (by norm_num) (pow_le_pow_left₀ zero_le_two ht 4)
    _ = t ^ (4 + 2 ^ 20 + 4207554485 * 2 ^ 21) := by ring
    _ ≤ _ := pow_le_pow_right₀ (one_le_two.trans ht) (by norm_num)

theorem section13_fejer_exponent_lower {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53)) ≤
      section13SquareExponent ((alpha / 2) ^ (4207554485 : Nat)) := by
  have hδ : 0 < (alpha / 2) ^ (4207554485 : Nat) := pow_pos (by positivity) _
  have hδone : (alpha / 2) ^ (4207554485 : Nat) ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith only [hαone])
  calc
    _ = (2 : Real) ^ (-((2 / alpha) ^ ((2 : Nat) ^ 53))) := by
      rw [Real.rpow_neg_eq_inv_rpow, one_div]
    _ ≤ (2 : Real) ^ (-(15 * section13Q ((alpha / 2) ^ (4207554485 : Nat)))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (neg_le_neg (section13_fejer_spectral_upper hα hαone))
    _ ≤ _ := section13SquareExponent_ge_spectral_power hδ hδone

end LeanProofs.GowersSzemeredi
