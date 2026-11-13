import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_016 : checkRows 256 16=true := by decide
theorem inverse_016 : checkRowInverse 256 16=true := by decide
theorem vertical_016 : checkVertical 256 16=true := by decide
#print axioms DirectBFSCoverage.rows_016
#print axioms DirectBFSCoverage.inverse_016
#print axioms DirectBFSCoverage.vertical_016
end DirectBFSCoverage
