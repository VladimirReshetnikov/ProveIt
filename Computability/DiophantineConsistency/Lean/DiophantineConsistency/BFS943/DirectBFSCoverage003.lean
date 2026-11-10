import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_003 : checkRows 48 16=true := by decide
theorem inverse_003 : checkRowInverse 48 16=true := by decide
theorem inversebounds_003 : (List.range' 48 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_003 : checkHorizontal 48 16=true := by decide
theorem horizontalbounds_003 : (List.range' 48 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_003 : checkVertical 48 16=true := by decide
theorem verticalbounds_003 : (List.range' 48 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_003
#print axioms DirectBFSCoverage.inverse_003
#print axioms DirectBFSCoverage.inversebounds_003
#print axioms DirectBFSCoverage.horizontal_003
#print axioms DirectBFSCoverage.horizontalbounds_003
#print axioms DirectBFSCoverage.vertical_003
#print axioms DirectBFSCoverage.verticalbounds_003
end DirectBFSCoverage
