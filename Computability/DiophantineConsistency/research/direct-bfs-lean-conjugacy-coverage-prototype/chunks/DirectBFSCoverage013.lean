import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_013 : checkRows 208 16=true := by decide
theorem inverse_013 : checkRowInverse 208 16=true := by decide
theorem horizontal_013 : checkHorizontal 208 16=true := by decide
theorem vertical_013 : checkVertical 208 16=true := by decide
#print axioms DirectBFSCoverage.rows_013
#print axioms DirectBFSCoverage.inverse_013
#print axioms DirectBFSCoverage.horizontal_013
#print axioms DirectBFSCoverage.vertical_013
end DirectBFSCoverage
