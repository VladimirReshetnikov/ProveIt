import GowersSzemeredi.Proofs16ClassPieces
import GowersSzemeredi.Proofs16SinglePieceGlobalSide

/-! Declarations of `Proofs16ClassPieces` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

theorem classBudget_pos_le {theta gamma : Real} (k : Nat) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < classBudget theta gamma k ∧ classBudget theta gamma k ≤ 1 := by
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le k ht ht1 hg hg1
  have h2 : (1 : Real) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
  unfold classBudget
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  linarith

end

end LeanProofs.GowersSzemeredi
