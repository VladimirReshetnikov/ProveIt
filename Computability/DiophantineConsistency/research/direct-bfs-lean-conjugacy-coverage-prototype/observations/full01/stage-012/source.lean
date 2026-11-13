import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_012 : checkRows 192 16=true := by decide
theorem inverse_012 : checkRowInverse 192 16=true := by decide
theorem inversebounds_012 : (List.range' 192 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_012 : checkHorizontal 192 16=true := by decide
theorem horizontalbounds_012 : (List.range' 192 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_012 : checkVertical 192 16=true := by decide
theorem verticalbounds_012 : (List.range' 192 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_012
#print axioms DirectBFSCoverage.inverse_012
#print axioms DirectBFSCoverage.inversebounds_012
#print axioms DirectBFSCoverage.horizontal_012
#print axioms DirectBFSCoverage.horizontalbounds_012
#print axioms DirectBFSCoverage.vertical_012
#print axioms DirectBFSCoverage.verticalbounds_012
end DirectBFSCoverage
