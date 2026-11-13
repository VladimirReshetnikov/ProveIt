import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_058 : checkRows 928 15=true := by decide
theorem inverse_058 : checkRowInverse 928 15=true := by decide
#print axioms DirectBFSCoverage.rows_058
#print axioms DirectBFSCoverage.inverse_058
end DirectBFSCoverage
