import BusyBeaver.ZFC.KSource215NormalizedData

namespace SetTheory.BusyBeaver.ZFC.KSource215Normalized

open RegisterPath RMBisim RMNormalizedBisim KSource215
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem chunk_ok6 : allC checkEntry chunk6 = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215Normalized
