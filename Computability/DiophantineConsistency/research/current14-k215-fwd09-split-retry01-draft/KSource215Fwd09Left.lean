import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def fwd9Left : CTree := match fwd9 with
  | .branch _ l _ => l
  | _ => .empty

theorem fwd9Left_ok : allC fwdF fwd9Left = true := by
  decide +kernel
end SetTheory.BusyBeaver.ZFC.KSource215
#print axioms SetTheory.BusyBeaver.ZFC.KSource215.fwd9Left_ok
