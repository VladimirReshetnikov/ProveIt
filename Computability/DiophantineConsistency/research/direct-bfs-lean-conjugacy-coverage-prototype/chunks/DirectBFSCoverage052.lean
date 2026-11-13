import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_052 : checkRows 832 16=true := by decide
theorem inverse_052 : checkRowInverse 832 16=true := by decide
#print axioms DirectBFSCoverage.rows_052
#print axioms DirectBFSCoverage.inverse_052
end DirectBFSCoverage
