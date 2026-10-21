import BusyBeaver.ZFC.KSource215CertCompose
import BusyBeaver.ZFC.KSource215FwdCheck07A
import BusyBeaver.ZFC.KSource215FwdCheck07B

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RMBisim RMPlainCodec

theorem fwd_ok7 : allC fwdF fwd7 = true :=
  allC_of_halves fwdF fwd7 fwd_ok7A fwd_ok7B

end SetTheory.BusyBeaver.ZFC.KSource215
