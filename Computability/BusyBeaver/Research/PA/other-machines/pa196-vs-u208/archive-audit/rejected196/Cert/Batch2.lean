import Cert.Common
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RejectAudit
theorem seg20 : safeRun 256 (98,25,119208250703628) = some (3,6607871,458921307) := by decide
theorem seg21 : safeRun 256 (3,6607871,458921307) = some (57,1652351,1835707103) := by decide
theorem seg22 : safeRun 256 (57,1652351,1835707103) = some (3,403,120631314939906) := by decide
theorem seg23 : safeRun 256 (3,403,120631314939906) = some (85,25809,1884864296959) := by decide
theorem seg24 : safeRun 256 (85,25809,1884864296959) = some (11,100,482525251633148) := by decide
theorem seg25 : safeRun 256 (11,100,482525251633148) = some (4,101,482523112538108) := by decide
theorem seg26 : safeRun 256 (4,101,482523112538108) = some (57,26869759,1840687789) := by decide
theorem seg27 : safeRun 256 (57,26869759,1840687789) = some (35,6782975,7360304488) := by decide
theorem seg28 : safeRun 256 (35,6782975,7360304488) = some (10,105984,7539189439487) := by decide
theorem seg29 : safeRun 256 (10,105984,7539189439487) = some (69,0,126468595292699597184) := by decide
end RejectAudit
