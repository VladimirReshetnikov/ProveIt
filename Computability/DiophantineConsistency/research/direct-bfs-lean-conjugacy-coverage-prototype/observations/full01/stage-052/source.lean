import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_052 : checkRows 832 16=true := by decide
theorem inverse_052 : checkRowInverse 832 16=true := by decide
theorem inversebounds_052 : (List.range' 832 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_052
#print axioms DirectBFSCoverage.inverse_052
#print axioms DirectBFSCoverage.inversebounds_052
end DirectBFSCoverage
