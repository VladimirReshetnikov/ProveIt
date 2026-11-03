import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_001 : checkRows 16 16=true := by decide
theorem inverse_001 : checkRowInverse 16 16=true := by decide
theorem horizontal_001 : checkHorizontal 16 16=true := by decide
theorem vertical_001 : checkVertical 16 16=true := by decide
#print axioms DirectBFSCoverage.rows_001
#print axioms DirectBFSCoverage.inverse_001
#print axioms DirectBFSCoverage.horizontal_001
#print axioms DirectBFSCoverage.vertical_001
end DirectBFSCoverage
