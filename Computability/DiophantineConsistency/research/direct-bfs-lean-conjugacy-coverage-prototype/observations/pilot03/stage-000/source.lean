import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_000 : checkRows 0 16=true := by decide
theorem inverse_000 : checkRowInverse 0 16=true := by decide
theorem inversebounds_000 : (List.range' 0 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_000 : checkHorizontal 0 16=true := by decide
theorem horizontalbounds_000 : (List.range' 0 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_000 : checkVertical 0 16=true := by decide
theorem verticalbounds_000 : (List.range' 0 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_000
#print axioms DirectBFSCoverage.inverse_000
#print axioms DirectBFSCoverage.inversebounds_000
#print axioms DirectBFSCoverage.horizontal_000
#print axioms DirectBFSCoverage.horizontalbounds_000
#print axioms DirectBFSCoverage.vertical_000
#print axioms DirectBFSCoverage.verticalbounds_000
end DirectBFSCoverage
