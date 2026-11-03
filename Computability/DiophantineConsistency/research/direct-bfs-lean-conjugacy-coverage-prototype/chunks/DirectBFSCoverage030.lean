import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_030 : checkRows 480 16=true := by decide
theorem inverse_030 : checkRowInverse 480 16=true := by decide
#print axioms DirectBFSCoverage.rows_030
#print axioms DirectBFSCoverage.inverse_030
end DirectBFSCoverage
