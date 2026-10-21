import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok15 : allC fwdF fwd15 = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
