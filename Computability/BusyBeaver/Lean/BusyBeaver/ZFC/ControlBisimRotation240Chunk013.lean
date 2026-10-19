import BusyBeaver.ZFC.ControlBisimRotation240Common

set_option autoImplicit false

/-! Certificate interval [1640,1768), using the unchanged packed checker.
The original proof options are retained under a separate bounded root check.
-/

namespace SetTheory.BusyBeaver.ZFC.ControlBisimRotation240Split

open ControlBisimRotation240

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check013 : chunk 1640 128 = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.ControlBisimRotation240Split
