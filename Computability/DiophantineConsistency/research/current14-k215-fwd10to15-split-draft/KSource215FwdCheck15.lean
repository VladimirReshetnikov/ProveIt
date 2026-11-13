import BusyBeaver.ZFC.KSource215Data
import BusyBeaver.ZFC.KSource215Fwd15Left
import BusyBeaver.ZFC.KSource215Fwd15Right

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok15 : allC fwdF fwd15 = true := by
  change (allC fwdF fwd15Left && allC fwdF fwd15Right) = true
  rw [fwd15Left_ok, fwd15Right_ok]
  rfl

end SetTheory.BusyBeaver.ZFC.KSource215

#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok15
