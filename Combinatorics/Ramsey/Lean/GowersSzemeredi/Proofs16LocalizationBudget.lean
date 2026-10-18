import GowersSzemeredi.Proofs16LocalizedCover

/-!
# Absorbing localization and floor losses in the recurrence scale

This module keeps `floor_half_lower`; the rest of the development, with its
description, is in `Proofs16LocalizationBudgetSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Above two, taking a natural floor loses at most a factor two. -/
theorem floor_half_lower {x : Real} (hx : 2 ≤ x) :
    0 < Nat.floor x ∧ x ≤ 2 * (Nat.floor x : Real) := by
  have hpos : 0 < Nat.floor x := Nat.floor_pos.mpr (by linarith)
  have hlt := Nat.lt_floor_add_one x
  exact ⟨hpos, by linarith⟩

end LeanProofs.GowersSzemeredi
