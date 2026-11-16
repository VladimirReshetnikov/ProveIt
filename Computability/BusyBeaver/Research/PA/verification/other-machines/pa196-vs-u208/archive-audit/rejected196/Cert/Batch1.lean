import Cert.Common
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RejectAudit
theorem seg10 : safeRun 256 (34,0,93833761118848) = some (28,21,458134192128) := by decide
theorem seg11 : safeRun 256 (28,21,458134192128) = some (2,352,28633387008) := by decide
theorem seg12 : safeRun 256 (2,352,28633387008) = some (51,22783,357922559) := by decide
theorem seg13 : safeRun 256 (51,22783,357922559) = some (61,369,18612076543) := by decide
theorem seg14 : safeRun 256 (61,369,18612076543) = some (33,1509949294,109909) := by decide
theorem seg15 : safeRun 256 (33,1509949294,109909) = some (3,397311,450189167) := by decide
theorem seg16 : safeRun 256 (3,397311,450189167) = some (2,6400,28812096512) := by decide
theorem seg17 : safeRun 256 (2,6400,28812096512) = some (2,1608,115248308224) := by decide
theorem seg18 : safeRun 256 (2,1608,115248308224) = some (39,421789686,7170901) := by decide
theorem seg19 : safeRun 256 (39,421789686,7170901) = some (98,25,119208250703628) := by decide
end RejectAudit
