import Trace74RadixIndices
import Trace74SupportShort
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74ConcreteLowRaw
open CompactListMask CompactConcreteMask

/-- Specialize the already fixed radix/index identity to the concrete support. -/
theorem low_add_defect :
    Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) +
      Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support)) + 1 =
        (2^67)^8807 := by
  exact Trace74RadixIndices.low_add_defect support Trace74SupportShort.support_short

#print axioms Trace74ConcreteLowRaw.low_add_defect
end Trace74ConcreteLowRaw
