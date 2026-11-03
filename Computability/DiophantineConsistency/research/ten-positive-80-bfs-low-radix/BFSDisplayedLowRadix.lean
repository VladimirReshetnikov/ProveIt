import BFSDisplayedBetaIPRAV2
import BFSDisplayedLowGeneric

/-! The weighted low-mask identity at an abstracted fixed radix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSDisplayedLowRadix
open Finset CompactSymbolicKernel CompactConcreteMask
open scoped BigOperators
attribute [local irreducible] rho

def displayedSupport : Finset ℕ :=
  ((range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032 ∪
    {1063,1064,1095,2195,3296}) \ {1})
theorem support_eq : displayedSupport = CompactConcreteMask.support := rfl

def displayedLow : ℕ := rho^8807 - 1 - (∑ j ∈ displayedSupport, rho^j) - 2*rho^1063

theorem radix_large : 4 ≤ rho := by unfold rho; norm_num

theorem formula_to_digits : displayedLow =
    Nat.ofDigits rho (CompactListMask.digits rho 8807 1063 CompactConcreteMask.support) := by
  unfold displayedLow
  rw [support_eq]
  exact (BFSDisplayedLowGeneric.low_recipe rho 8807 1063
    CompactConcreteMask.support radix_large CompactConcreteMask.support_bounded
    CompactConcreteMask.special_mem).symm

#print axioms BFSDisplayedLowRadix.formula_to_digits
end BFSDisplayedLowRadix
