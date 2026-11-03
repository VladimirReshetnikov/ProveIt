import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_051 : checkRows 816 16=true := by decide
theorem inverse_051 : checkRowInverse 816 16=true := by decide
theorem inversebounds_051 : (List.range' 816 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_051
#print axioms DirectBFSCoverage.inverse_051
#print axioms DirectBFSCoverage.inversebounds_051
end DirectBFSCoverage
