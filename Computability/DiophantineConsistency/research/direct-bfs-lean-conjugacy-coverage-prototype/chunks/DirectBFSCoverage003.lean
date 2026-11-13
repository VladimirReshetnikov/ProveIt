import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_003 : checkRows 48 16=true := by decide
theorem inverse_003 : checkRowInverse 48 16=true := by decide
theorem horizontal_003 : checkHorizontal 48 16=true := by decide
theorem vertical_003 : checkVertical 48 16=true := by decide
#print axioms DirectBFSCoverage.rows_003
#print axioms DirectBFSCoverage.inverse_003
#print axioms DirectBFSCoverage.horizontal_003
#print axioms DirectBFSCoverage.vertical_003
end DirectBFSCoverage
