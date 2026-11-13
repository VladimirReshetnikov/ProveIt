import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_042 : checkRows 672 16=true := by decide
theorem inverse_042 : checkRowInverse 672 16=true := by decide
theorem inversebounds_042 : (List.range' 672 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_042
#print axioms DirectBFSCoverage.inverse_042
#print axioms DirectBFSCoverage.inversebounds_042
end DirectBFSCoverage
