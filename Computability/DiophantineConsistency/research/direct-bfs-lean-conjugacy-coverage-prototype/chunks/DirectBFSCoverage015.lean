import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_015 : checkRows 240 16=true := by decide
theorem inverse_015 : checkRowInverse 240 16=true := by decide
theorem horizontal_015 : checkHorizontal 240 10=true := by decide
theorem vertical_015 : checkVertical 240 16=true := by decide
#print axioms DirectBFSCoverage.rows_015
#print axioms DirectBFSCoverage.inverse_015
#print axioms DirectBFSCoverage.horizontal_015
#print axioms DirectBFSCoverage.vertical_015
end DirectBFSCoverage
