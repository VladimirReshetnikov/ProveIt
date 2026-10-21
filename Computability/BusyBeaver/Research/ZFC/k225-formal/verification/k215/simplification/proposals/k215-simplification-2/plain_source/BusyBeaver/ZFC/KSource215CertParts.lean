import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215
open RegisterPath RMBisim RMPlainCodec
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def certLeft : CTree → CTree
  | .branch _ l _ => l
  | T => T

def certRight : CTree → CTree
  | .branch _ _ r => r
  | T => T

end SetTheory.BusyBeaver.ZFC.KSource215
