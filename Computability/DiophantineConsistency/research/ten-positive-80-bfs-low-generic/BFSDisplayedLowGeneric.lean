import DiophantineConsistency.CompactConcreteMask

/-! Exact low-mask weighted-support recipe over a variable radix. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace BFSDisplayedLowGeneric
open Finset CompactListMask CompactConcreteMask
open scoped BigOperators

theorem low_recipe (B len special : ℕ) (S : Finset ℕ)
    (hB : 4 ≤ B) (hS : S ⊆ range len) (hs : special ∈ S) :
    Nat.ofDigits B (digits B len special S) =
      B^len - 1 - (∑ j ∈ S, B^j) - 2*B^special := by
  have h := digits_add_defect B len special S hB
  rw [defect_sum B len special S hS hs] at h
  omega

#print axioms BFSDisplayedLowGeneric.low_recipe
end BFSDisplayedLowGeneric
