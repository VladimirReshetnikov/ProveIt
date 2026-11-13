import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_010 : checkRows 160 16=true := by decide
theorem inverse_010 : checkRowInverse 160 16=true := by decide
theorem inversebounds_010 : (List.range' 160 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_010 : checkHorizontal 160 16=true := by decide
theorem horizontalbounds_010 : (List.range' 160 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_010 : checkVertical 160 16=true := by decide
theorem verticalbounds_010 : (List.range' 160 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_010
#print axioms DirectBFSCoverage.inverse_010
#print axioms DirectBFSCoverage.inversebounds_010
#print axioms DirectBFSCoverage.horizontal_010
#print axioms DirectBFSCoverage.horizontalbounds_010
#print axioms DirectBFSCoverage.vertical_010
#print axioms DirectBFSCoverage.verticalbounds_010
end DirectBFSCoverage
