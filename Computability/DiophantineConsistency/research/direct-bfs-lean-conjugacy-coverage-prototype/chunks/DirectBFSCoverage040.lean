import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_040 : checkRows 640 16=true := by decide
theorem inverse_040 : checkRowInverse 640 16=true := by decide
#print axioms DirectBFSCoverage.rows_040
#print axioms DirectBFSCoverage.inverse_040
end DirectBFSCoverage
