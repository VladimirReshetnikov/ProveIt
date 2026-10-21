import BusyBeaver.ZFC.KSource215WfData

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim RMPlainCodec
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem wfBlock06 : ([192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223] : List Nat).all wfNode = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
