import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_035 : checkRows 560 16=true := by decide
theorem inverse_035 : checkRowInverse 560 16=true := by decide
theorem inversebounds_035 : (List.range' 560 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_035
#print axioms DirectBFSCoverage.inverse_035
#print axioms DirectBFSCoverage.inversebounds_035
end DirectBFSCoverage
