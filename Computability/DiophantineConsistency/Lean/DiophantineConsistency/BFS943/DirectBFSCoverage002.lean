import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_002 : checkRows 32 16=true := by decide
theorem inverse_002 : checkRowInverse 32 16=true := by decide
theorem inversebounds_002 : (List.range' 32 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_002 : checkHorizontal 32 16=true := by decide
theorem horizontalbounds_002 : (List.range' 32 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_002 : checkVertical 32 16=true := by decide
theorem verticalbounds_002 : (List.range' 32 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_002
#print axioms DirectBFSCoverage.inverse_002
#print axioms DirectBFSCoverage.inversebounds_002
#print axioms DirectBFSCoverage.horizontal_002
#print axioms DirectBFSCoverage.horizontalbounds_002
#print axioms DirectBFSCoverage.vertical_002
#print axioms DirectBFSCoverage.verticalbounds_002
end DirectBFSCoverage
