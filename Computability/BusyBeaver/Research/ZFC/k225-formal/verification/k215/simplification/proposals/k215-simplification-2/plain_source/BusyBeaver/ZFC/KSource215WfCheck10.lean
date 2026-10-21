import BusyBeaver.ZFC.KSource215WfData

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim RMPlainCodec
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem wfBlock10 : ([320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351] : List Nat).all wfNode = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
