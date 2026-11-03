import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_057 : checkRows 912 16=true := by decide
theorem inverse_057 : checkRowInverse 912 16=true := by decide
#print axioms DirectBFSCoverage.rows_057
#print axioms DirectBFSCoverage.inverse_057
end DirectBFSCoverage
