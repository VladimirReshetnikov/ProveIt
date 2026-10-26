import Lean.Elab.Tactic.Omega

/-! Checked generic integer kernel for the initial-strip width proposal.
This file uses no Mathlib or project imports. The actual production adapter
remains source-reviewed only; see StripWidthKernel.log for its timeout.
-/

namespace StripWidthCore

/-- One shifted left seam cannot lie strictly inside the open gap. -/
theorem width_le_period {S : Int → Prop} {N L R : Nat}
    (hN : 0 < N) (hleft : S (-(L : Int)))
    (hgap : ∀ x : Int, -(L : Int) < x → x < (R : Int) → ¬ S x)
    (hperiod : ∀ x : Int, S (x + (N : Int)) ↔ S x) :
    L + R ≤ N := by
  by_cases h : L + R ≤ N
  · exact h
  · exact False.elim
      (hgap (-(L : Int) + (N : Int)) (by omega) (by omega)
        ((hperiod (-(L : Int))).mpr hleft))

/-- The existing left/right minimum lengths imply the period obstruction. -/
theorem period_gt_two {N L R : Nat}
    (hleft : 0 < L) (hright : 2 ≤ R) (hwidth : L + R ≤ N) : 2 < N := by
  omega

#print axioms width_le_period
#print axioms period_gt_two

end StripWidthCore
