import Cert.Common
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RejectAudit
theorem beforeLast : safeRun 42 (2,4718592,8901080328916847363191969278853120) = some (63,4,9333459206974312140706382378542689157121) := by decide
theorem lastStep : safeRun 1 (63,4,9333459206974312140706382378542689157121) = some (196,9,4666729603487156070353191189271344578560) := by decide
end RejectAudit
