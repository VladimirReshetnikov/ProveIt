import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def fwd10Right : CTree := match fwd10 with
  | .branch _ _ r => r
  | _ => .empty

theorem fwd10Right_ok : allC fwdF fwd10Right = true := by
  decide +kernel
end SetTheory.BusyBeaver.ZFC.KSource215
#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd10Right_ok
