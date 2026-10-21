import BusyBeaver.ZFC.KSource215CertParts

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim RMPlainCodec
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok9A : allC fwdF (certLeft fwd9) = true := by decide +kernel

end SetTheory.BusyBeaver.ZFC.KSource215
