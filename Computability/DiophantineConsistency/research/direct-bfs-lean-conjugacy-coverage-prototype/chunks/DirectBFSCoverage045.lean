import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_045 : checkRows 720 16=true := by decide
theorem inverse_045 : checkRowInverse 720 16=true := by decide
#print axioms DirectBFSCoverage.rows_045
#print axioms DirectBFSCoverage.inverse_045
end DirectBFSCoverage
