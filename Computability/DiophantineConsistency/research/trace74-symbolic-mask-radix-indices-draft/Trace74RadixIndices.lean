import Trace74FixedIndices
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74RadixIndices
open Finset CompactListMask
open scoped BigOperators

/-- Fix base and indices together while leaving the mask support symbolic. -/
theorem low_add_defect (S : Finset ℕ) (hsupport : S ⊆ Finset.range 3297) :
    Nat.ofDigits (2^67) (digits (2^67) 8807 1063 S) +
      Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 S)) + 1 =
        (2^67)^8807 := by
  exact Trace74FixedIndices.low_add_defect (2^67) S (by norm_num) hsupport

#print axioms Trace74RadixIndices.low_add_defect
end Trace74RadixIndices
