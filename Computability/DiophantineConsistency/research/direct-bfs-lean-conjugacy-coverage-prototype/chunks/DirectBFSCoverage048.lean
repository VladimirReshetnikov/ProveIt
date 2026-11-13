import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_048 : checkRows 768 16=true := by decide
theorem inverse_048 : checkRowInverse 768 16=true := by decide
#print axioms DirectBFSCoverage.rows_048
#print axioms DirectBFSCoverage.inverse_048
end DirectBFSCoverage
