import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_011 : checkRows 176 16=true := by decide
theorem inverse_011 : checkRowInverse 176 16=true := by decide
theorem inversebounds_011 : (List.range' 176 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_011 : checkHorizontal 176 16=true := by decide
theorem horizontalbounds_011 : (List.range' 176 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_011 : checkVertical 176 16=true := by decide
theorem verticalbounds_011 : (List.range' 176 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_011
#print axioms DirectBFSCoverage.inverse_011
#print axioms DirectBFSCoverage.inversebounds_011
#print axioms DirectBFSCoverage.horizontal_011
#print axioms DirectBFSCoverage.horizontalbounds_011
#print axioms DirectBFSCoverage.vertical_011
#print axioms DirectBFSCoverage.verticalbounds_011
end DirectBFSCoverage
