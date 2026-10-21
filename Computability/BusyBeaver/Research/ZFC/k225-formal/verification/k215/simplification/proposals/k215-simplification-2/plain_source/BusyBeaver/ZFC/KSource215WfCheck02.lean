import BusyBeaver.ZFC.KSource215WfData

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim RMPlainCodec
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem wfBlock02 : ([64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95] : List Nat).all wfNode = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
