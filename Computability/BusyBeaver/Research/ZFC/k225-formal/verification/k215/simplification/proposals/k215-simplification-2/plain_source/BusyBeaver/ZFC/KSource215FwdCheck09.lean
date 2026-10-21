import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck09A
import BusyBeaver.ZFC.KSource215FwdCheck09B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok9 : allC fwdF fwd9 = true :=
  allC_of_halves fwdF fwd9 fwd_ok9A fwd_ok9B

end SetTheory.BusyBeaver.ZFC.KSource215
