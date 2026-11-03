import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_018 : checkRows 288 16=true := by decide
theorem inverse_018 : checkRowInverse 288 16=true := by decide
theorem vertical_018 : checkVertical 288 16=true := by decide
#print axioms DirectBFSCoverage.rows_018
#print axioms DirectBFSCoverage.inverse_018
#print axioms DirectBFSCoverage.vertical_018
end DirectBFSCoverage
