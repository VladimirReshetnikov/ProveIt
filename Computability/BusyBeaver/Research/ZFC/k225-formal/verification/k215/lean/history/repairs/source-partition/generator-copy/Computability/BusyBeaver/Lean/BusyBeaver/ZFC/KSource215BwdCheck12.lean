import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim RMOffsetBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem bwd_ok12 : allO bwdF bwd12 = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
