import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck12A
import BusyBeaver.ZFC.KSource215FwdCheck12B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok12 : allC fwdF fwd12 = true :=
  allC_of_halves fwdF fwd12 fwd_ok12A fwd_ok12B

end SetTheory.BusyBeaver.ZFC.KSource215
