import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim RMOffsetBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem bwd_ok8 : allO bwdF bwd8 = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
