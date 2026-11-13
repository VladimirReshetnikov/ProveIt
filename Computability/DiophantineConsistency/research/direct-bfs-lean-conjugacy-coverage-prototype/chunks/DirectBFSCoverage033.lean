import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_033 : checkRows 528 16=true := by decide
theorem inverse_033 : checkRowInverse 528 16=true := by decide
#print axioms DirectBFSCoverage.rows_033
#print axioms DirectBFSCoverage.inverse_033
end DirectBFSCoverage
