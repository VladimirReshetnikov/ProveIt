import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_004 : checkRows 64 16=true := by decide
theorem inverse_004 : checkRowInverse 64 16=true := by decide
theorem horizontal_004 : checkHorizontal 64 16=true := by decide
theorem vertical_004 : checkVertical 64 16=true := by decide
#print axioms DirectBFSCoverage.rows_004
#print axioms DirectBFSCoverage.inverse_004
#print axioms DirectBFSCoverage.horizontal_004
#print axioms DirectBFSCoverage.vertical_004
end DirectBFSCoverage
