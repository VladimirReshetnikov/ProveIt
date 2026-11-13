import Cert.Common
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RejectAudit
theorem seg30 : safeRun 256 (69,0,126468595292699597184) = some (32,6687,120627031031807) := by decide
theorem seg31 : safeRun 256 (32,6687,120627031031807) = some (3,107647,7539188742143) := by decide
theorem seg32 : safeRun 256 (3,107647,7539188742143) = some (34,0,126486597974538364288) := by decide
theorem seg33 : safeRun 256 (34,0,126486597974538364288) = some (88,421,1930032317726736) := by decide
theorem seg34 : safeRun 256 (88,421,1930032317726736) = some (2,27594752,29449956020) := by decide
theorem seg35 : safeRun 256 (2,27594752,29449956020) = some (1,7064322038,115022506) := by decide
theorem seg36 : safeRun 256 (1,7064322038,115022506) = some (15,0,31621648948165749088) := by decide
theorem seg37 : safeRun 256 (15,0,31621648948165749088) = some (6,6,123522068284118569) := by decide
theorem seg38 : safeRun 256 (6,6,123522068284118569) = some (6,421,1930032283908440) := by decide
theorem seg39 : safeRun 256 (6,421,1930032283908440) = some (19,26950,482525975322625) := by decide
end RejectAudit
