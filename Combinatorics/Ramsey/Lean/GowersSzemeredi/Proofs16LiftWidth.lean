import GowersSzemeredi.Proofs16LocalizationBudget
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Bertrand

/-! # An explicit rounded width for synchronized affine lifting

`section16_local_affine_lift_sqrt` is in `Proofs16LiftWidthSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Choose the integer tiling scale without hiding either rounding loss.
For refined base width w>=16, the final box width is at least sqrt(w)/4. -/
theorem section16_lift_width_rounding {w : ℝ} (hw : 16 ≤ w) :
    ∃ v : Nat, 1 ≤ v ∧ (v : ℝ) ^ 2 + 1 ≤ w ∧
      Real.sqrt w / 4 ≤ (v - 1 : Nat) := by
  have hw0 : 0 ≤ w := by linarith
  have hs0 := Real.sqrt_nonneg w
  have hs2 := Real.sq_sqrt hw0
  have hs4 : 4 ≤ Real.sqrt w := by nlinarith
  let v := Nat.floor (Real.sqrt w / 2) + 1
  have hfloor := Nat.floor_le (show 0 ≤ Real.sqrt w / 2 by positivity)
  have hvupper : (v : ℝ) ≤ Real.sqrt w / 2 + 1 := by
    dsimp [v]
    push_cast
    linarith
  obtain ⟨_, hlower⟩ := floor_half_lower (show 2 ≤ Real.sqrt w / 2 by linarith)
  refine ⟨v, by dsimp [v]; omega, ?_, ?_⟩
  · have _ : (0 : ℝ) ≤ v := Nat.cast_nonneg _
    have hsquare : (v : ℝ) ^ 2 ≤ (Real.sqrt w / 2 + 1) ^ 2 := by nlinarith
    nlinarith
  · simp only [v, Nat.add_sub_cancel]
    linarith

end LeanProofs.GowersSzemeredi
