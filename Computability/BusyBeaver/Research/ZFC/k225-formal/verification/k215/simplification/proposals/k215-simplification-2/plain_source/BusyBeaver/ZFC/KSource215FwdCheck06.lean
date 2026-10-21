import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck06A
import BusyBeaver.ZFC.KSource215FwdCheck06B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok6 : allC fwdF fwd6 = true :=
  allC_of_halves fwdF fwd6 fwd_ok6A fwd_ok6B

end SetTheory.BusyBeaver.ZFC.KSource215
