import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_049 : checkRows 784 16=true := by decide
theorem inverse_049 : checkRowInverse 784 16=true := by decide
#print axioms DirectBFSCoverage.rows_049
#print axioms DirectBFSCoverage.inverse_049
end DirectBFSCoverage
