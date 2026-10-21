import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck08A
import BusyBeaver.ZFC.KSource215FwdCheck08B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok8 : allC fwdF fwd8 = true :=
  allC_of_halves fwdF fwd8 fwd_ok8A fwd_ok8B

end SetTheory.BusyBeaver.ZFC.KSource215
