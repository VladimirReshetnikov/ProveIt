import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def fwd13Left : CTree := match fwd13 with
  | .branch _ l _ => l
  | _ => .empty

theorem fwd13Left_ok : allC fwdF fwd13Left = true := by
  decide +kernel
end SetTheory.BusyBeaver.ZFC.KSource215
#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd13Left_ok
