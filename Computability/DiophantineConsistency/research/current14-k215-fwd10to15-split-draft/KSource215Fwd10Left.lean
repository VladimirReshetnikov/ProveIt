import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def fwd10Left : CTree := match fwd10 with
  | .branch _ l _ => l
  | _ => .empty

theorem fwd10Left_ok : allC fwdF fwd10Left = true := by
  decide +kernel
end SetTheory.BusyBeaver.ZFC.KSource215
#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd10Left_ok
