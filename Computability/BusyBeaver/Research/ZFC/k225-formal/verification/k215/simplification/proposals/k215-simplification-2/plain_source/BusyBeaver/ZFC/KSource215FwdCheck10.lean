import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck10A
import BusyBeaver.ZFC.KSource215FwdCheck10B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok10 : allC fwdF fwd10 = true :=
  allC_of_halves fwdF fwd10 fwd_ok10A fwd_ok10B

end SetTheory.BusyBeaver.ZFC.KSource215
