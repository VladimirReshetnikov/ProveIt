import BusyBeaver.ZFC.BisimRouting245Data

/-! Exact certificate block [2720, 2752); full-certificate successor lookup.
This unit checks only this block. Complete source bisimulation requires all95. -/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk085
open RMBisim

theorem checked : allC BisimRouting245Data.test BisimRouting245Data.chunk085 = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk085
