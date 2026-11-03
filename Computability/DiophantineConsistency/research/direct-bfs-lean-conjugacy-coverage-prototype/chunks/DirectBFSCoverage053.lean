import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_053 : checkRows 848 16=true := by decide
theorem inverse_053 : checkRowInverse 848 16=true := by decide
#print axioms DirectBFSCoverage.rows_053
#print axioms DirectBFSCoverage.inverse_053
end DirectBFSCoverage
