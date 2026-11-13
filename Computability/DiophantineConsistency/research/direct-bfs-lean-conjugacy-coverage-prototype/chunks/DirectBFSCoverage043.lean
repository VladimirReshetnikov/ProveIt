import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_043 : checkRows 688 16=true := by decide
theorem inverse_043 : checkRowInverse 688 16=true := by decide
#print axioms DirectBFSCoverage.rows_043
#print axioms DirectBFSCoverage.inverse_043
end DirectBFSCoverage
