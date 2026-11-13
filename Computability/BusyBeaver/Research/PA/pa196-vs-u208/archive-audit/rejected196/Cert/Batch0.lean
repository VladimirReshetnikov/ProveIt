import Cert.Common
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RejectAudit
theorem seg0 : safeRun 256 (0,0,0) = some (62,279550,64) := by decide
theorem seg1 : safeRun 256 (62,279550,64) = some (51,4367,73151) := by decide
theorem seg2 : safeRun 256 (51,4367,73151) = some (85,71565239,68) := by decide
theorem seg3 : safeRun 256 (85,71565239,68) = some (85,4595707,9558) := by decide
theorem seg4 : safeRun 256 (85,4595707,9558) = some (122,20,2505916412) := by decide
theorem seg5 : safeRun 256 (122,20,2505916412) = some (61,84223,546263) := by decide
theorem seg6 : safeRun 256 (61,84223,546263) = some (69,0,20708016983200) := by decide
theorem seg7 : safeRun 256 (69,0,20708016983200) = some (6,0,5955962011176) := by decide
theorem seg8 : safeRun 256 (6,0,5955962011176) = some (33,1359,363523071) := by decide
theorem seg9 : safeRun 256 (33,1359,363523071) = some (34,0,93833761118848) := by decide
end RejectAudit
