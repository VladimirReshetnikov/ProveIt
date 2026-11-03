import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_006 : checkRows 96 16=true := by decide
theorem inverse_006 : checkRowInverse 96 16=true := by decide
theorem horizontal_006 : checkHorizontal 96 16=true := by decide
theorem vertical_006 : checkVertical 96 16=true := by decide
#print axioms DirectBFSCoverage.rows_006
#print axioms DirectBFSCoverage.inverse_006
#print axioms DirectBFSCoverage.horizontal_006
#print axioms DirectBFSCoverage.vertical_006
end DirectBFSCoverage
