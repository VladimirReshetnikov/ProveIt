import Trace74GenericDefect
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedIndices
open Finset CompactListMask
open scoped BigOperators

/-- Fix only lengths and special index; radix and support remain symbolic. -/
theorem low_add_defect (B : ℕ) (S : Finset ℕ) (hB : 4 ≤ B)
    (hsupport : S ⊆ Finset.range 3297) :
    Nat.ofDigits B (digits B 8807 1063 S) +
      Nat.ofDigits B ((List.range 3297).map (defect 1063 S)) + 1 = B^8807 := by
  exact Trace74GenericDefect.low_add_defect B 3297 8807 1063 S
    hB (by decide) (by decide) hsupport

#print axioms Trace74FixedIndices.low_add_defect
end Trace74FixedIndices
