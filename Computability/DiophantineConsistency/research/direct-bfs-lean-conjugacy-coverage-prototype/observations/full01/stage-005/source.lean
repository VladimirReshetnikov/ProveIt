import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_005 : checkRows 80 16=true := by decide
theorem inverse_005 : checkRowInverse 80 16=true := by decide
theorem inversebounds_005 : (List.range' 80 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_005 : checkHorizontal 80 16=true := by decide
theorem horizontalbounds_005 : (List.range' 80 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_005 : checkVertical 80 16=true := by decide
theorem verticalbounds_005 : (List.range' 80 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_005
#print axioms DirectBFSCoverage.inverse_005
#print axioms DirectBFSCoverage.inversebounds_005
#print axioms DirectBFSCoverage.horizontal_005
#print axioms DirectBFSCoverage.horizontalbounds_005
#print axioms DirectBFSCoverage.vertical_005
#print axioms DirectBFSCoverage.verticalbounds_005
end DirectBFSCoverage
