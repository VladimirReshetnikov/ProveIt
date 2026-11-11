import BusyBeaver.ZFC.KSource215Data
import BusyBeaver.ZFC.KSource215Fwd09Left
import BusyBeaver.ZFC.KSource215Fwd09Right

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem fwd_ok9 : allC fwdF fwd9 = true := by
  change (allC fwdF fwd9Left && allC fwdF fwd9Right) = true
  rw [fwd9Left_ok, fwd9Right_ok]
  rfl

end SetTheory.BusyBeaver.ZFC.KSource215

#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd_ok9
