import BFSDisplayedBetaIPRAV2

/-! Compose the low-mask alias and its existing exact recipe. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace BFSDisplayedLowInferred

theorem low_alias : CompactSymbolicPorts.lowNat =
    Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support) := rfl

theorem low_formula := Eq.trans low_alias CompactConcreteMask.concrete_recipe

#print axioms BFSDisplayedLowInferred.low_formula
end BFSDisplayedLowInferred
