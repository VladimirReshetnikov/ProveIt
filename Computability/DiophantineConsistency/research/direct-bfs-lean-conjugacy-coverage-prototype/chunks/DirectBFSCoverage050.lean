import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_050 : checkRows 800 16=true := by decide
theorem inverse_050 : checkRowInverse 800 16=true := by decide
#print axioms DirectBFSCoverage.rows_050
#print axioms DirectBFSCoverage.inverse_050
end DirectBFSCoverage
