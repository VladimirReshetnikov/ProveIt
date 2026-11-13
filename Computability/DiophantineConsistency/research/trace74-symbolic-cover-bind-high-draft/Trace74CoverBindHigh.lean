import Trace74CoverDischargeDefect
import Trace74HighDigitBound
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoverBindHigh
open CompactFixedBeta CompactSymbolicPorts

attribute [local irreducible] Nat.pow CompactFixedBeta.betaNat
  CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat

/-- Discharge the actual high bound and obtain the natural symbolic-port cover. -/
theorem cover_nat : betaNat+1 ≤ lowNat+highNat := by
  exact Trace74CoverDischargeDefect.cover highNat Trace74HighDigitBound.high_at_least

#print axioms Trace74CoverBindHigh.cover_nat
end Trace74CoverBindHigh
