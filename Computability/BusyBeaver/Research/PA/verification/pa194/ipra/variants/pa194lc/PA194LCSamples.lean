import PA194LCChecks

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194LCSamples

/-- Four increment sites and the loop continuation in the first changed subtree. -/
theorem firstLoop : PA194LCChecks.blockCheck 124 5 = true := by decide +kernel

theorem laterLoop : PA194LCChecks.blockCheck 3311 5 = true := by decide +kernel

#print axioms firstLoop
#print axioms laterLoop
end PA194LCSamples
