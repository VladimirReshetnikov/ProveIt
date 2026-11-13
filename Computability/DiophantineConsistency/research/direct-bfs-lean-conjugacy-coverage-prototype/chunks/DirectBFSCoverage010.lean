import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_010 : checkRows 160 16=true := by decide
theorem inverse_010 : checkRowInverse 160 16=true := by decide
theorem horizontal_010 : checkHorizontal 160 16=true := by decide
theorem vertical_010 : checkVertical 160 16=true := by decide
#print axioms DirectBFSCoverage.rows_010
#print axioms DirectBFSCoverage.inverse_010
#print axioms DirectBFSCoverage.horizontal_010
#print axioms DirectBFSCoverage.vertical_010
end DirectBFSCoverage
