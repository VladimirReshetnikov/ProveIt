import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_029 : checkRows 464 16=true := by decide
theorem inverse_029 : checkRowInverse 464 16=true := by decide
#print axioms DirectBFSCoverage.rows_029
#print axioms DirectBFSCoverage.inverse_029
end DirectBFSCoverage
