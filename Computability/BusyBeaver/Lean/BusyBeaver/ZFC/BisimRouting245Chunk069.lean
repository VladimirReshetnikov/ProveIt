import BusyBeaver.ZFC.BisimRouting245Data

/-! Exact certificate block [2208, 2240); full-certificate successor lookup.
This unit checks only this block. Complete source bisimulation requires all95. -/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk069
open RMBisim

theorem checked : allC BisimRouting245Data.test BisimRouting245Data.chunk069 = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk069
