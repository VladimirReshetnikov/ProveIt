import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_021 : checkRows 336 16=true := by decide
theorem inverse_021 : checkRowInverse 336 16=true := by decide
theorem vertical_021 : checkVertical 336 16=true := by decide
#print axioms DirectBFSCoverage.rows_021
#print axioms DirectBFSCoverage.inverse_021
#print axioms DirectBFSCoverage.vertical_021
end DirectBFSCoverage
