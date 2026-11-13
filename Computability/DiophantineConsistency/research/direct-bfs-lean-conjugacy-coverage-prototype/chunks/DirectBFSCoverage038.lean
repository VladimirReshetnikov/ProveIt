import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_038 : checkRows 608 16=true := by decide
theorem inverse_038 : checkRowInverse 608 16=true := by decide
#print axioms DirectBFSCoverage.rows_038
#print axioms DirectBFSCoverage.inverse_038
end DirectBFSCoverage
