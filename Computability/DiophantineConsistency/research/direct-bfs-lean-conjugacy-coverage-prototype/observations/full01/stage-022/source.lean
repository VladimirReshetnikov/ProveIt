import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_022 : checkRows 352 16=true := by decide
theorem inverse_022 : checkRowInverse 352 16=true := by decide
theorem inversebounds_022 : (List.range' 352 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem vertical_022 : checkVertical 352 16=true := by decide
theorem verticalbounds_022 : (List.range' 352 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_022
#print axioms DirectBFSCoverage.inverse_022
#print axioms DirectBFSCoverage.inversebounds_022
#print axioms DirectBFSCoverage.vertical_022
#print axioms DirectBFSCoverage.verticalbounds_022
end DirectBFSCoverage
