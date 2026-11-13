import BusyBeaver.ZFC.KSource215Data
import BusyBeaver.ZFC.KSource215Fwd10Left
import BusyBeaver.ZFC.KSource215Fwd10Right

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok10 : allC fwdF fwd10 = true := by
  change (allC fwdF fwd10Left && allC fwdF fwd10Right) = true
  rw [fwd10Left_ok, fwd10Right_ok]
  rfl

end SetTheory.BusyBeaver.ZFC.KSource215

#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok10
