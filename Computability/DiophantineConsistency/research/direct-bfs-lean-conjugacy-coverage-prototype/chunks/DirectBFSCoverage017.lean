import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_017 : checkRows 272 16=true := by decide
theorem inverse_017 : checkRowInverse 272 16=true := by decide
theorem vertical_017 : checkVertical 272 16=true := by decide
#print axioms DirectBFSCoverage.rows_017
#print axioms DirectBFSCoverage.inverse_017
#print axioms DirectBFSCoverage.vertical_017
end DirectBFSCoverage
