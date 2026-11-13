import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_034 : checkRows 544 16=true := by decide
theorem inverse_034 : checkRowInverse 544 16=true := by decide
theorem inversebounds_034 : (List.range' 544 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_034
#print axioms DirectBFSCoverage.inverse_034
#print axioms DirectBFSCoverage.inversebounds_034
end DirectBFSCoverage
