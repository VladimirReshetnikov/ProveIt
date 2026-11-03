import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_037 : checkRows 592 16=true := by decide
theorem inverse_037 : checkRowInverse 592 16=true := by decide
theorem inversebounds_037 : (List.range' 592 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_037
#print axioms DirectBFSCoverage.inverse_037
#print axioms DirectBFSCoverage.inversebounds_037
end DirectBFSCoverage
