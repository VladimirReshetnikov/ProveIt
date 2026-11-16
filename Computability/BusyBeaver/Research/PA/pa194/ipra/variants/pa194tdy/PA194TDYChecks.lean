import PA194RegisterContracts
import PA194TDYAllocation
import PA194TDYData

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194TDYChecks
open PA194RegisterContracts PA194TDYAllocation PA194TDYData

abbrev check := checkAt allocation machine

theorem checkHalt :
    PA194SourceContracts.haltContract machine PA194SourceProgram.path 10 512 = true := by
  decide +kernel

theorem selected : check 46 = true ∧ check 48 = true ∧ check 95 = true ∧ check 100 = true := by
  decide +kernel

#print axioms checkHalt
#print axioms selected
end PA194TDYChecks
