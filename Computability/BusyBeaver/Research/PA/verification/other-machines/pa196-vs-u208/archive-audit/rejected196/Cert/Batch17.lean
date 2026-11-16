import Cert.Common
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RejectAudit
theorem seg170 : safeRun 43 (2,4718592,8901080328916847363191969278853120) = some (196,9,4666729603487156070353191189271344578560) := by decide
end RejectAudit
