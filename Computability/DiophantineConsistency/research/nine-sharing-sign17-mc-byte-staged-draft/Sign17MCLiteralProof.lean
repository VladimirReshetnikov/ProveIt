import DiophantineConsistency.Sign17MCLiteralDecl

/-! SOURCE-ONLY: isolate the original finite mask comparison. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17MCByteLiteral

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem low_port_literal : CurrentMasks2011.lowPort = mcLiteral := by
  unfold CurrentMasks2011.lowPort LowMaskCoding.mask LowMaskCoding.supportValue mcLiteral
  rw [CurrentMasks2011.lowSupport_def]
  decide +kernel

theorem current_port2_literal : CurrentWindowCarry2011.ports 2 = (mcLiteral : ℤ) := by
  change (CurrentMasks2011.lowPort : ℤ) = (mcLiteral : ℤ)
  exact_mod_cast low_port_literal

end DiophantineConsistency.Sign17MCByteLiteral
#print axioms DiophantineConsistency.Sign17MCByteLiteral.low_port_literal
#print axioms DiophantineConsistency.Sign17MCByteLiteral.current_port2_literal
