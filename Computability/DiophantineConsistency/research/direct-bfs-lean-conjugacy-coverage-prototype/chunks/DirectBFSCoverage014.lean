import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_014 : checkRows 224 16=true := by decide
theorem inverse_014 : checkRowInverse 224 16=true := by decide
theorem horizontal_014 : checkHorizontal 224 16=true := by decide
theorem vertical_014 : checkVertical 224 16=true := by decide
#print axioms DirectBFSCoverage.rows_014
#print axioms DirectBFSCoverage.inverse_014
#print axioms DirectBFSCoverage.horizontal_014
#print axioms DirectBFSCoverage.vertical_014
end DirectBFSCoverage
