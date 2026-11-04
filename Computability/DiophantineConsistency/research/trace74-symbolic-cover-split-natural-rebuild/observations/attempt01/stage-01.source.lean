import Trace74GenericPowerCover
import Trace74HighDigitBound
import Trace74BetaPower
import Trace74ConcreteDefectBound
import Trace74LowPortIdentity
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74SymbolicCoverNat
open CompactListMask CompactConcreteMask CompactFixedBeta CompactSymbolicPorts

def defectNat : ℕ := Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support))

/-- Apply the generic symbolic power sandwich to the retained natural ports. -/
theorem cover_nat : betaNat + 1 ≤ lowNat + highNat := by
  exact Trace74GenericPowerCover.cover (2^67) 3297 4393 8807 betaNat lowNat defectNat highNat
    (by norm_num) (by decide) Trace74BetaPower.beta_plus_one
    Trace74LowPortIdentity.low_add_defect Trace74ConcreteDefectBound.defect_lt
    Trace74HighDigitBound.high_at_least

#print axioms Trace74SymbolicCoverNat.cover_nat
end Trace74SymbolicCoverNat
