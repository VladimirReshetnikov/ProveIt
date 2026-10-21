import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck13A
import BusyBeaver.ZFC.KSource215FwdCheck13B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok13 : allC fwdF fwd13 = true :=
  allC_of_halves fwdF fwd13 fwd_ok13A fwd_ok13B

end SetTheory.BusyBeaver.ZFC.KSource215
