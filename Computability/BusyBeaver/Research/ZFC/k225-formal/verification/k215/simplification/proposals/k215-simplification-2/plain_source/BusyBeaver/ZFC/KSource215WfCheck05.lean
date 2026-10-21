import BusyBeaver.ZFC.KSource215WfData

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim RMPlainCodec
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem wfBlock05 : ([160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191] : List Nat).all wfNode = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
