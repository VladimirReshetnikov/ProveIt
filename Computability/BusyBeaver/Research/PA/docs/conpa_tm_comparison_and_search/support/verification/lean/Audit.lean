module
import PA196.PhysicalEndpoint

/-! A guarded audit of the endpoints actually rebuilt in this research.
This deliberately does not assert a fresh build of the arithmetic-independence
development. Any additional axiom, including `sorryAx`, fails these guards. -/

/-- info: 'PA196.Startup.startup_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PA196.Startup.startup_exact

/-- info: 'PA196.Coverage.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Coverage.complete

/-- info: 'PA196.PhysicalEndpoint.blank_halting_iff_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.PhysicalEndpoint.blank_halting_iff_source
