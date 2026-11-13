import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_008 : checkRows 128 16=true := by decide
theorem inverse_008 : checkRowInverse 128 16=true := by decide
theorem inversebounds_008 : (List.range' 128 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_008 : checkHorizontal 128 16=true := by decide
theorem horizontalbounds_008 : (List.range' 128 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_008 : checkVertical 128 16=true := by decide
theorem verticalbounds_008 : (List.range' 128 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_008
#print axioms DirectBFSCoverage.inverse_008
#print axioms DirectBFSCoverage.inversebounds_008
#print axioms DirectBFSCoverage.horizontal_008
#print axioms DirectBFSCoverage.horizontalbounds_008
#print axioms DirectBFSCoverage.vertical_008
#print axioms DirectBFSCoverage.verticalbounds_008
end DirectBFSCoverage
