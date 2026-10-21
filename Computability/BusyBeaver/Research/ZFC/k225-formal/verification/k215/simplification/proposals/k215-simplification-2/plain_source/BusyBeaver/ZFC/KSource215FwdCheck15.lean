import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck15A
import BusyBeaver.ZFC.KSource215FwdCheck15B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok15 : allC fwdF fwd15 = true :=
  allC_of_halves fwdF fwd15 fwd_ok15A fwd_ok15B

end SetTheory.BusyBeaver.ZFC.KSource215
