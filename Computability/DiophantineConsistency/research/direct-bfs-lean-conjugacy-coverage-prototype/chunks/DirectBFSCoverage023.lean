import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_023 : checkRows 368 16=true := by decide
theorem inverse_023 : checkRowInverse 368 16=true := by decide
theorem vertical_023 : checkVertical 368 16=true := by decide
#print axioms DirectBFSCoverage.rows_023
#print axioms DirectBFSCoverage.inverse_023
#print axioms DirectBFSCoverage.vertical_023
end DirectBFSCoverage
