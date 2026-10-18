import BusyBeaver.ZFC.BisimRouting245Data

/-! Exact certificate block [2656, 2688); full-certificate successor lookup.
This unit checks only this block. Complete source bisimulation requires all95. -/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk083
open RMBisim

theorem checked : allC BisimRouting245Data.test BisimRouting245Data.chunk083 = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk083
