import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_024 : checkRows 384 16=true := by decide
theorem inverse_024 : checkRowInverse 384 16=true := by decide
theorem vertical_024 : checkVertical 384 16=true := by decide
#print axioms DirectBFSCoverage.rows_024
#print axioms DirectBFSCoverage.inverse_024
#print axioms DirectBFSCoverage.vertical_024
end DirectBFSCoverage
