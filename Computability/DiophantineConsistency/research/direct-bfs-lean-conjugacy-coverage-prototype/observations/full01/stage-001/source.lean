import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_001 : checkRows 16 16=true := by decide
theorem inverse_001 : checkRowInverse 16 16=true := by decide
theorem inversebounds_001 : (List.range' 16 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_001 : checkHorizontal 16 16=true := by decide
theorem horizontalbounds_001 : (List.range' 16 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_001 : checkVertical 16 16=true := by decide
theorem verticalbounds_001 : (List.range' 16 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_001
#print axioms DirectBFSCoverage.inverse_001
#print axioms DirectBFSCoverage.inversebounds_001
#print axioms DirectBFSCoverage.horizontal_001
#print axioms DirectBFSCoverage.horizontalbounds_001
#print axioms DirectBFSCoverage.vertical_001
#print axioms DirectBFSCoverage.verticalbounds_001
end DirectBFSCoverage
