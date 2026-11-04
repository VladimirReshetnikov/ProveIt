import DiophantineConsistency.CompactSymbolicPorts
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74LowNatDefinition
open CompactListMask CompactConcreteMask CompactSymbolicPorts

/-- The unexpanded symbolic definition of the actual low port. -/
theorem low_nat_definition : lowNat =
    Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) := by
  rfl

#print axioms Trace74LowNatDefinition.low_nat_definition
end Trace74LowNatDefinition
