import BusyBeaver.ZFC.ControlBisimRotation240Common

set_option autoImplicit false

/-! First measurement candidate: unchanged predicate on certificate entries[0,128).
The original source's proof options are retained; the guard wall/memory limits remain bounded.
-/

namespace SetTheory.BusyBeaver.ZFC.ControlBisimRotation240Split

open ControlBisimRotation240

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check000 : chunk 0 128 = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.ControlBisimRotation240Split
