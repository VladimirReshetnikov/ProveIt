import BusyBeaver.ZFC.KSource215WfData

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim RMPlainCodec
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem wfBlock15 : ([480, 481, 482, 483, 484, 485, 486] : List Nat).all wfNode = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
