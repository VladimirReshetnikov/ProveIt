import BusyBeaver.ZFC.BisimRouting245Data

/-! Exact certificate block [64, 96); full-certificate successor lookup.
This unit checks only this block. Complete source bisimulation requires all95. -/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk002
open RMBisim

theorem checked : allC BisimRouting245Data.test BisimRouting245Data.chunk002 = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk002
