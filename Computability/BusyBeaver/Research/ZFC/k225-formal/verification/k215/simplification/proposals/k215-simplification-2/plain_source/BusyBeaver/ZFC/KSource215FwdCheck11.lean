import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck11A
import BusyBeaver.ZFC.KSource215FwdCheck11B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok11 : allC fwdF fwd11 = true :=
  allC_of_halves fwdF fwd11 fwd_ok11A fwd_ok11B

end SetTheory.BusyBeaver.ZFC.KSource215
