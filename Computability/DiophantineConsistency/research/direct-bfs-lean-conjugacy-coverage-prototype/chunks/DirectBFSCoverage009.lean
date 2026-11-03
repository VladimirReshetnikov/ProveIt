import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_009 : checkRows 144 16=true := by decide
theorem inverse_009 : checkRowInverse 144 16=true := by decide
theorem horizontal_009 : checkHorizontal 144 16=true := by decide
theorem vertical_009 : checkVertical 144 16=true := by decide
#print axioms DirectBFSCoverage.rows_009
#print axioms DirectBFSCoverage.inverse_009
#print axioms DirectBFSCoverage.horizontal_009
#print axioms DirectBFSCoverage.vertical_009
end DirectBFSCoverage
