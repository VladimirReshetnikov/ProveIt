import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_011 : checkRows 176 16=true := by decide
theorem inverse_011 : checkRowInverse 176 16=true := by decide
theorem horizontal_011 : checkHorizontal 176 16=true := by decide
theorem vertical_011 : checkVertical 176 16=true := by decide
#print axioms DirectBFSCoverage.rows_011
#print axioms DirectBFSCoverage.inverse_011
#print axioms DirectBFSCoverage.horizontal_011
#print axioms DirectBFSCoverage.vertical_011
end DirectBFSCoverage
