import DiophantineConsistency.Sign20CurrentExpressionDef

/-! SOURCE-ONLY: positivity of exactly the current port used by sign20. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20CurrentBeta
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.radix CurrentMasks2011.lowPort CurrentMasks2011.highPort

set_option maxHeartbeats 4000000 in
theorem positive : (0 : ℤ) < CurrentWindowCarry2011.ports 0 := by
  have hr : 1 < CurrentMasks2011.radix ^ 2011 :=
    one_lt_pow₀ (by unfold CurrentMasks2011.radix; decide : 1 < CurrentMasks2011.radix) (by decide)
  have hb : 0 < CurrentMasks2011.beta := by unfold CurrentMasks2011.beta; omega
  change (0 : ℤ) < (CurrentMasks2011.beta : ℤ)
  exact_mod_cast hb

theorem nonzero : CurrentWindowCarry2011.ports 0 ≠ 0 := ne_of_gt positive
end DiophantineConsistency.Sign20CurrentBeta
#print axioms DiophantineConsistency.Sign20CurrentBeta.positive
#print axioms DiophantineConsistency.Sign20CurrentBeta.nonzero
