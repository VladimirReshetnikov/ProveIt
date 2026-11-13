import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_002 : checkRows 32 16=true := by decide
theorem inverse_002 : checkRowInverse 32 16=true := by decide
theorem horizontal_002 : checkHorizontal 32 16=true := by decide
theorem vertical_002 : checkVertical 32 16=true := by decide
#print axioms DirectBFSCoverage.rows_002
#print axioms DirectBFSCoverage.inverse_002
#print axioms DirectBFSCoverage.horizontal_002
#print axioms DirectBFSCoverage.vertical_002
end DirectBFSCoverage
