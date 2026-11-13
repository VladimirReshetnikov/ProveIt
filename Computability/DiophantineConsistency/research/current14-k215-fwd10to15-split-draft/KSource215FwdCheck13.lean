import BusyBeaver.ZFC.KSource215Data
import BusyBeaver.ZFC.KSource215Fwd13Left
import BusyBeaver.ZFC.KSource215Fwd13Right

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok13 : allC fwdF fwd13 = true := by
  change (allC fwdF fwd13Left && allC fwdF fwd13Right) = true
  rw [fwd13Left_ok, fwd13Right_ok]
  rfl

end SetTheory.BusyBeaver.ZFC.KSource215

#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok13
