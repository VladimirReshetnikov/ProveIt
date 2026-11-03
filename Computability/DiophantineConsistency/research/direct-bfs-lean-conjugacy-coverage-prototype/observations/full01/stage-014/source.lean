import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_014 : checkRows 224 16=true := by decide
theorem inverse_014 : checkRowInverse 224 16=true := by decide
theorem inversebounds_014 : (List.range' 224 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_014 : checkHorizontal 224 16=true := by decide
theorem horizontalbounds_014 : (List.range' 224 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_014 : checkVertical 224 16=true := by decide
theorem verticalbounds_014 : (List.range' 224 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_014
#print axioms DirectBFSCoverage.inverse_014
#print axioms DirectBFSCoverage.inversebounds_014
#print axioms DirectBFSCoverage.horizontal_014
#print axioms DirectBFSCoverage.horizontalbounds_014
#print axioms DirectBFSCoverage.vertical_014
#print axioms DirectBFSCoverage.verticalbounds_014
end DirectBFSCoverage
