import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_013 : checkRows 208 16=true := by decide
theorem inverse_013 : checkRowInverse 208 16=true := by decide
theorem inversebounds_013 : (List.range' 208 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_013 : checkHorizontal 208 16=true := by decide
theorem horizontalbounds_013 : (List.range' 208 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_013 : checkVertical 208 16=true := by decide
theorem verticalbounds_013 : (List.range' 208 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_013
#print axioms DirectBFSCoverage.inverse_013
#print axioms DirectBFSCoverage.inversebounds_013
#print axioms DirectBFSCoverage.horizontal_013
#print axioms DirectBFSCoverage.horizontalbounds_013
#print axioms DirectBFSCoverage.vertical_013
#print axioms DirectBFSCoverage.verticalbounds_013
end DirectBFSCoverage
