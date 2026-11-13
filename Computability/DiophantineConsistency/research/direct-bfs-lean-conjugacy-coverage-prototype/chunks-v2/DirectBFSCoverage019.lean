import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_019 : checkRows 304 16=true := by decide
theorem inverse_019 : checkRowInverse 304 16=true := by decide
theorem inversebounds_019 : (List.range' 304 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem vertical_019 : checkVertical 304 16=true := by decide
theorem verticalbounds_019 : (List.range' 304 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_019
#print axioms DirectBFSCoverage.inverse_019
#print axioms DirectBFSCoverage.inversebounds_019
#print axioms DirectBFSCoverage.vertical_019
#print axioms DirectBFSCoverage.verticalbounds_019
end DirectBFSCoverage
