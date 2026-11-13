import Trace74ConcreteLowRaw
import DiophantineConsistency.CompactSymbolicPorts
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74LowPortIdentity
open CompactListMask CompactConcreteMask CompactSymbolicPorts

/-- Bind the checked raw identity to the actual low port without expanding digits. -/
theorem low_add_defect :
    lowNat + Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support)) + 1 =
      (2^67)^8807 := by
  rw [show lowNat = Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) by rfl]
  exact Trace74ConcreteLowRaw.low_add_defect

#print axioms Trace74LowPortIdentity.low_add_defect
end Trace74LowPortIdentity
