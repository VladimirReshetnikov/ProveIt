import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_012 : checkRows 192 16=true := by decide
theorem inverse_012 : checkRowInverse 192 16=true := by decide
theorem horizontal_012 : checkHorizontal 192 16=true := by decide
theorem vertical_012 : checkVertical 192 16=true := by decide
#print axioms DirectBFSCoverage.rows_012
#print axioms DirectBFSCoverage.inverse_012
#print axioms DirectBFSCoverage.horizontal_012
#print axioms DirectBFSCoverage.vertical_012
end DirectBFSCoverage
