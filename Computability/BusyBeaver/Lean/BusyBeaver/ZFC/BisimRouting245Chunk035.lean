import BusyBeaver.ZFC.BisimRouting245Data

/-! Exact certificate block [1120, 1152); full-certificate successor lookup.
This unit checks only this block. Complete source bisimulation requires all95. -/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk035
open RMBisim

theorem checked : allC BisimRouting245Data.test BisimRouting245Data.chunk035 = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk035
