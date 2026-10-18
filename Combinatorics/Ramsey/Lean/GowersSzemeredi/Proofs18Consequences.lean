import GowersSzemeredi.Proofs18ColorClass

/-!
# Elementary consequences of the quantitative Szemeredi theorem

This module isolates the finite-coloring argument at the end of the paper,
which derives Corollary 18.7 from Theorem 18.2 without importing any unproved
statement as an axiom.  The wrappers that supply the exact numbered results
from Theorem 18.2 (`corollary_18_7_holds_of_theorem_18_2`,
`theorem_1_2_holds_of_theorem_18_2`) are in `Proofs18ConsequencesSide`,
outside the final route. -/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

private theorem szemeredi_half_threshold_le_two_color (k : Nat) :
    szemerediThreshold (1 / 2 : Real) k ≤ twoColorThreshold k := by
  simp only [szemerediThreshold, twoColorThreshold]
  norm_num

/-- Corollary 18.7 at a single length `k`, from Theorem 18.2 at that length
and density one half. The two thresholds coincide at density one half. -/
theorem corollary_18_7_at_of_half_density {k : Nat}
    (h : ∀ N : Nat, szemerediThreshold (1 / 2 : Real) k ≤ N →
      ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → (1 / 2 : Real) * N ≤ A.card →
        HasNatAP A k) :
    ∀ N : Nat, twoColorThreshold k ≤ N →
      ∀ color : Nat → Fin 2, HasMonochromaticAP N 2 color k := by
  intro N hN color
  exact hasMonochromaticAP_of_density (by decide)
    (h N ((szemeredi_half_threshold_le_two_color k).trans hN)) color

end LeanProofs.GowersSzemeredi
