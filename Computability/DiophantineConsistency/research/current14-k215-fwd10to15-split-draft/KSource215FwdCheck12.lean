import BusyBeaver.ZFC.KSource215Data
import BusyBeaver.ZFC.KSource215Fwd12Left
import BusyBeaver.ZFC.KSource215Fwd12Right

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok12 : allC fwdF fwd12 = true := by
  change (allC fwdF fwd12Left && allC fwdF fwd12Right) = true
  rw [fwd12Left_ok, fwd12Right_ok]
  rfl

end SetTheory.BusyBeaver.ZFC.KSource215

#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok12
