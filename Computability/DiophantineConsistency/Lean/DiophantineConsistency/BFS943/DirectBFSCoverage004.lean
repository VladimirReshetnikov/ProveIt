import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_004 : checkRows 64 16=true := by decide
theorem inverse_004 : checkRowInverse 64 16=true := by decide
theorem inversebounds_004 : (List.range' 64 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_004 : checkHorizontal 64 16=true := by decide
theorem horizontalbounds_004 : (List.range' 64 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_004 : checkVertical 64 16=true := by decide
theorem verticalbounds_004 : (List.range' 64 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_004
#print axioms DirectBFSCoverage.inverse_004
#print axioms DirectBFSCoverage.inversebounds_004
#print axioms DirectBFSCoverage.horizontal_004
#print axioms DirectBFSCoverage.horizontalbounds_004
#print axioms DirectBFSCoverage.vertical_004
#print axioms DirectBFSCoverage.verticalbounds_004
end DirectBFSCoverage
