import BusyBeaver.ZFC.KSource215Data
import BusyBeaver.ZFC.KSource215Fwd11Left
import BusyBeaver.ZFC.KSource215Fwd11Right

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok11 : allC fwdF fwd11 = true := by
  change (allC fwdF fwd11Left && allC fwdF fwd11Right) = true
  rw [fwd11Left_ok, fwd11Right_ok]
  rfl

end SetTheory.BusyBeaver.ZFC.KSource215

#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok11
