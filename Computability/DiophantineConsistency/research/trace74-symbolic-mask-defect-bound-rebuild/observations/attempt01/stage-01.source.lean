import Trace74GenericDefect
import Trace74SupportShort
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74ConcreteDefectBound
open CompactListMask CompactConcreteMask

/-- The concrete short defect is below the corresponding base power. -/
theorem defect_lt :
    Nat.ofDigits (2^67) ((List.range 3297).map (defect 1063 support)) <
      (2^67)^3297 := by
  exact Trace74GenericDefect.digits_lt (2^67) 3297 1063 support (by norm_num)

#print axioms Trace74ConcreteDefectBound.defect_lt
end Trace74ConcreteDefectBound
