import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_020 : checkRows 320 16=true := by decide
theorem inverse_020 : checkRowInverse 320 16=true := by decide
theorem vertical_020 : checkVertical 320 16=true := by decide
#print axioms DirectBFSCoverage.rows_020
#print axioms DirectBFSCoverage.inverse_020
#print axioms DirectBFSCoverage.vertical_020
end DirectBFSCoverage
