import PA194RegisterContracts
import PA194P5Allocation
import PA194P5Data

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194P5Representative
open PA194RegisterContracts PA194P5Allocation PA194P5Data

abbrev check := checkAt allocation machine

theorem checkHalt :
    PA194SourceContracts.haltContract machine PA194SourceProgram.path 10 512 = true := by
  decide +kernel
theorem checkStart : check 25 = true := by decide +kernel
theorem checkFetch : check 28 = true := by decide +kernel
theorem checkAInc : check 46 = true := by decide +kernel
theorem checkADec : check 48 = true := by decide +kernel
theorem checkTInc : check 54 = true := by decide +kernel
theorem checkTDec : check 50 = true := by decide +kernel
theorem checkDDec : check 95 = true := by decide +kernel
theorem checkDInc : check 100 = true := by decide +kernel
theorem checkMP : check 3554 = true := by decide +kernel
theorem checkSHIFT : check 3661 = true := by decide +kernel

#print axioms checkHalt
#print axioms checkStart
#print axioms checkFetch
#print axioms checkDInc
#print axioms checkMP
#print axioms checkSHIFT
end PA194P5Representative
