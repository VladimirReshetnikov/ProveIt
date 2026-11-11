import BusyBeaver.ZFC.KSource215Data
import BusyBeaver.ZFC.KSource215Fwd14Left
import BusyBeaver.ZFC.KSource215Fwd14Right

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok14 : allC fwdF fwd14 = true := by
  change (allC fwdF fwd14Left && allC fwdF fwd14Right) = true
  rw [fwd14Left_ok, fwd14Right_ok]
  rfl

end SetTheory.BusyBeaver.ZFC.KSource215

#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok14
