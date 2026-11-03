import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_055 : checkRows 880 16=true := by decide
theorem inverse_055 : checkRowInverse 880 16=true := by decide
#print axioms DirectBFSCoverage.rows_055
#print axioms DirectBFSCoverage.inverse_055
end DirectBFSCoverage
