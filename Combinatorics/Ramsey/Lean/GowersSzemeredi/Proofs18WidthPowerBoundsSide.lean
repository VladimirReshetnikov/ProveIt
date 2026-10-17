import GowersSzemeredi.Proofs18WidthPowerBounds
import GowersSzemeredi.Proofs16PolyCoverTwoSide
import GowersSzemeredi.Proofs18LengthSixRoute

/-! Declarations of `Proofs18WidthPowerBounds` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem sixEb_le_one {A Bq : Nat → Real} (l : Nat) (g t s : Real) (hs : 0 < s) (hs1 : s ≤ 1) :
    sixEb A Bq l g t s ≤ 1 := by
  unfold sixEb
  split_ifs
  · exact cubicBaseExponent_le_one (section16BaseFamilyBound_pos g t) hs hs1
  · exact section16CappedWidthExponent_le_one _ _

/-- **The width `sixW` is a power above an explicit threshold.** -/
theorem sixW_powerLB {Eb : Nat → Real → Real → Real → Real} {alpha t : Real}
    (hE : ∀ l g u s, 0 < s → s ≤ 1 → 0 < Eb l g u s ∧ Eb l g u s ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    WidthPowerLB (sixW Eb alpha t) (sixWExp Eb alpha t) (sixWThr Eb alpha t) := by
  have hs8 : 0 < t / 2 / 2 / 2 := by positivity
  have hs81 : t / 2 / 2 / 2 ≤ 1 := by linarith
  have hs4 : 0 < t / 2 / 2 := by positivity
  have hs41 : t / 2 / 2 ≤ 1 := by linarith
  obtain ⟨h1, h1'⟩ := hE 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2) _ hs8 hs81
  obtain ⟨h2, h2'⟩ := hE 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2) _ hs4 hs41
  have hA := liftLastW_two_coverWidth_powerLB
    (E := Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2)) (t := t) h1 h1'
  have hB := liftLastW_coverWidth_powerLB
    (E := Eb 2 (alpha / 2) (globalBudget alpha (alpha / 2) 2)) (t := t) h2 h2'
  have hA1 : (1 : Real) ≤ max (8 * max (8 * 0 + 8) ((6 : Real) ^ (4 / Eb 1 (alpha / 2)
      (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2))) + 8)
      ((6 : Real) ^ (4 / (Eb 1 (alpha / 2) (globalBudget alpha (alpha / 2) 2)
        (t / 2 / 2 / 2) / 4))) := by
    refine le_trans ?_ (le_max_left _ _)
    have : (8 : Real) ≤ max (8 * 0 + 8) ((6 : Real) ^ (4 / Eb 1 (alpha / 2)
      (globalBudget alpha (alpha / 2) 2) (t / 2 / 2 / 2))) := by
      refine le_trans ?_ (le_max_left _ _); norm_num
    linarith
  have h := WidthPowerLB.min hA hB hA1
  intro L hL
  have hL' := h L hL
  simpa only [sixW, sixWExp, Function.iterate_one] using hL'

end LeanProofs.GowersSzemeredi
