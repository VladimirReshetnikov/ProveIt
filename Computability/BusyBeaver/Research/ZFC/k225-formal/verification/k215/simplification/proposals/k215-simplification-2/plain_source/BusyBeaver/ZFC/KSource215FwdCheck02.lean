import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim RMPlainCodec
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok2 : allC fwdF fwd2 = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
