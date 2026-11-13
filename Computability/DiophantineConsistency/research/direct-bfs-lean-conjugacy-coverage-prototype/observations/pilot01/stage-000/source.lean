import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_000 : checkRows 0 16=true := by decide
theorem inverse_000 : checkRowInverse 0 16=true := by decide
theorem horizontal_000 : checkHorizontal 0 16=true := by decide
theorem vertical_000 : checkVertical 0 16=true := by decide
#print axioms DirectBFSCoverage.rows_000
#print axioms DirectBFSCoverage.inverse_000
#print axioms DirectBFSCoverage.horizontal_000
#print axioms DirectBFSCoverage.vertical_000
end DirectBFSCoverage
