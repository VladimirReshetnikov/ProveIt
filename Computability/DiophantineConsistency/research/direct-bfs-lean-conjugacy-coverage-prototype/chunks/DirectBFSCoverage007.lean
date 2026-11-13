import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_007 : checkRows 112 16=true := by decide
theorem inverse_007 : checkRowInverse 112 16=true := by decide
theorem horizontal_007 : checkHorizontal 112 16=true := by decide
theorem vertical_007 : checkVertical 112 16=true := by decide
#print axioms DirectBFSCoverage.rows_007
#print axioms DirectBFSCoverage.inverse_007
#print axioms DirectBFSCoverage.horizontal_007
#print axioms DirectBFSCoverage.vertical_007
end DirectBFSCoverage
