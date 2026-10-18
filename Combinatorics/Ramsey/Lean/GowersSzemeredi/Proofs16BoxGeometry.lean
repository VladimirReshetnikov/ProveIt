import GowersSzemeredi.Section16

/-!
# Geometric safeguards for multiple linearity

Proper axes identify formal lengths with cardinalities. The upper bound on
the loss parameter is also necessary: at loss 2 the printed width formula
would force a proper partition cell in ZMod 2 to have width at least 4.

`binaryFullBox` and `multipleLinearity_uncapped_loss_counterexample` are in
`Proofs16BoxGeometrySide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Width is at most the length of each axis. -/
theorem Box.width_le_axis_length {N k : Nat} (P : Box N k) (i : Fin k) :
    P.width ≤ (P.axis i).length := by
  have hk : k ≠ 0 := by have := i.isLt; omega
  simp only [Box.width, dif_neg hk]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- In a proper box width measures cardinality, not an inflated presentation. -/
theorem Box.width_le_axis_card {N k : Nat} (P : Box N k) (hP : P.IsProper)
    (i : Fin k) : P.width ≤ (P.axis i).carrier.card := by
  rw [hP i]
  exact P.width_le_axis_length i

/-- Every proper box in ZMod N has width at most N. -/
theorem Box.width_le_modulus {N k : Nat} [NeZero N] (P : Box N k)
    (hP : P.IsProper) : P.width ≤ N := by
  by_cases hk : k = 0
  · subst k
    simp [Box.width]
  · let i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
    exact (P.width_le_axis_card hP i).trans (by
      simpa using Finset.card_le_univ (P.axis i).carrier)

end LeanProofs.GowersSzemeredi
