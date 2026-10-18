import BusyBeaver.ZFC.BisimRouting245Data

/-! Exact certificate block [2784, 2816); full-certificate successor lookup.
This unit checks only this block. Complete source bisimulation requires all95. -/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk087
open RMBisim

theorem checked : allC BisimRouting245Data.test BisimRouting245Data.chunk087 = true := by
  decide +kernel

end SetTheory.BusyBeaver.ZFC.BisimRouting245Chunk087
