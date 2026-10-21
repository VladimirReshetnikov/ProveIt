import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim RMOffsetBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem bwd_ok14 : allO bwdF bwd14 = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
