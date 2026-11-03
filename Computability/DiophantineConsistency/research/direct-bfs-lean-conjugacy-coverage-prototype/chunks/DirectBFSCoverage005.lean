import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_005 : checkRows 80 16=true := by decide
theorem inverse_005 : checkRowInverse 80 16=true := by decide
theorem horizontal_005 : checkHorizontal 80 16=true := by decide
theorem vertical_005 : checkVertical 80 16=true := by decide
#print axioms DirectBFSCoverage.rows_005
#print axioms DirectBFSCoverage.inverse_005
#print axioms DirectBFSCoverage.horizontal_005
#print axioms DirectBFSCoverage.vertical_005
end DirectBFSCoverage
