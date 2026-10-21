import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck14A
import BusyBeaver.ZFC.KSource215FwdCheck14B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok14 : allC fwdF fwd14 = true :=
  allC_of_halves fwdF fwd14 fwd_ok14A fwd_ok14B

end SetTheory.BusyBeaver.ZFC.KSource215
