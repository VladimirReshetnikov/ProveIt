import PA194LCCChecks
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194LCCSamples
/-- Four changed LC_C increment addresses and their loop continuation. -/
theorem firstChanged : PA194LCCChecks.blockCheck 124 5 = true := by decide +kernel
/-- Four changed LC_C addresses close to the end of the source program. -/
theorem lastChanged : PA194LCCChecks.blockCheck 3616 5 = true := by decide +kernel
#print axioms firstChanged
#print axioms lastChanged
end PA194LCCSamples
