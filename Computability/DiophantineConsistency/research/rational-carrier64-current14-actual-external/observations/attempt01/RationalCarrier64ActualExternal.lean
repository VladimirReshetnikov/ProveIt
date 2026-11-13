import RationalCarrier64CurrentSpecialization
import Current14BetaNonzero

/-! Actual-port external positive-zero equivalence; no internal formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.RationalCarrier64ActualExternal

open RationalCarrier64Current RationalCarrier64CurrentSpecialization
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem actual_rational_zero_iff :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      value64 (portsQ CurrentWindowCarry2011.ports) (inputQ v)
        ((CurrentWindowCarry2011.ports 3 : ℚ) / (CurrentWindowCarry2011.ports 0 : ℚ))
        ((CurrentWindowCarry2011.ports 2 : ℚ) - (CurrentWindowCarry2011.ports 3 : ℚ)) = 0) ↔
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports).eval v = 0) :=
  positive_zero_iff CurrentWindowCarry2011.ports Current14BetaNonzero.actual_beta_ne

#print axioms actual_rational_zero_iff

end DiophantineConsistency.RationalCarrier64ActualExternal
