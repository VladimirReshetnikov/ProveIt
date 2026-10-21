import BusyBeaver.ZFC.KSource215AutoData
namespace SetTheory.BusyBeaver.ZFC.KSource215Auto
open RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem block_ok1 : allC checkEntry block1 = true := by decide +kernel
end SetTheory.BusyBeaver.ZFC.KSource215Auto
