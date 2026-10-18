import GowersSzemeredi.Proofs17PhaseRemoval

/-! Elementary interfaces for local uniformity and phase twisting.

`not_uniformOnPartition_exists_cell` is in `Proofs17PartitionEnergySide`,
outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Twisting by a polynomial phase preserves the unit-disc bound. -/
theorem phaseTwist_discValued {N : Nat} [NeZero N] {f : ZMod N → Complex}
    (hf : DiscValued f) (phi : ZMod N → ZMod N) : DiscValued (phaseTwist f phi) := by
  intro s
  change ‖f s * exponential (-(phi s))‖ ≤ 1
  have hexp : ‖exponential (-(phi s))‖ = 1 := (ZMod.stdAddChar (N := N)).norm_apply (-(phi s))
  rw [norm_mul, hexp, mul_one]
  exact hf s

/-- Extension by zero outside a cell preserves the unit-disc bound. -/
theorem restrictToCell_discValued {N : Nat} {f : ZMod N → Complex}
    (hf : DiscValued f) (Q : Finset (ZMod N)) : DiscValued (restrictToCell Q f) := by
  intro s
  by_cases hs : s ∈ Q
  · simpa only [restrictToCell, if_pos hs] using hf s
  · simp only [restrictToCell, if_neg hs, norm_zero, zero_le_one]

end LeanProofs.GowersSzemeredi
