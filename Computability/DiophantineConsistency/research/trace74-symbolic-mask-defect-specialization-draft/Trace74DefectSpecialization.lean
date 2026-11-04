import Trace74GenericDefect
import Trace74SupportShort
import DiophantineConsistency.CompactSymbolicPorts
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74DefectSpecialization
open CompactListMask CompactConcreteMask CompactSymbolicPorts

def B : ℕ := 2^67
def shortDefect : List ℕ := (List.range 3297).map (defect 1063 support)

/-- The specific low mask plus its short defect is the full base power. -/
theorem low_add_defect : lowNat + Nat.ofDigits B shortDefect + 1 = B^8807 := by
  change Nat.ofDigits B (digits B 8807 1063 support) +
    Nat.ofDigits B ((List.range 3297).map (defect 1063 support)) + 1 = B^8807
  exact Trace74GenericDefect.low_add_defect B 3297 8807 1063 support
    (by norm_num [B]) (by decide) (by decide) Trace74SupportShort.support_short

/-- The same concrete defect is strictly below the shorter base power. -/
theorem defect_lt : Nat.ofDigits B shortDefect < B^3297 := by
  change Nat.ofDigits B ((List.range 3297).map (defect 1063 support)) < B^3297
  exact Trace74GenericDefect.digits_lt B 3297 1063 support (by norm_num [B])

#print axioms Trace74DefectSpecialization.low_add_defect
#print axioms Trace74DefectSpecialization.defect_lt
end Trace74DefectSpecialization
