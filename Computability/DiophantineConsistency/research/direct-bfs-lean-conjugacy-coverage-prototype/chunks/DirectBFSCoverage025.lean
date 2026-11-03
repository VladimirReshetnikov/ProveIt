import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_025 : checkRows 400 16=true := by decide
theorem inverse_025 : checkRowInverse 400 16=true := by decide
theorem vertical_025 : checkVertical 400 16=true := by decide
#print axioms DirectBFSCoverage.rows_025
#print axioms DirectBFSCoverage.inverse_025
#print axioms DirectBFSCoverage.vertical_025
end DirectBFSCoverage
