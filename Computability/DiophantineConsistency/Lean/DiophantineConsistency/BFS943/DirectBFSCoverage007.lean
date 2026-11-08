import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_007 : checkRows 112 16=true := by decide
theorem inverse_007 : checkRowInverse 112 16=true := by decide
theorem inversebounds_007 : (List.range' 112 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem horizontal_007 : checkHorizontal 112 16=true := by decide
theorem horizontalbounds_007 : (List.range' 112 16).all (fun j => decide (DirectBFSConjugacyBase.horizontal.getD j 0 < 250 ∧ DirectBFSConjugacyBase.horizontalInverse.getD j 0 < 250)) = true := by decide
theorem vertical_007 : checkVertical 112 16=true := by decide
theorem verticalbounds_007 : (List.range' 112 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_007
#print axioms DirectBFSCoverage.inverse_007
#print axioms DirectBFSCoverage.inversebounds_007
#print axioms DirectBFSCoverage.horizontal_007
#print axioms DirectBFSCoverage.horizontalbounds_007
#print axioms DirectBFSCoverage.vertical_007
#print axioms DirectBFSCoverage.verticalbounds_007
end DirectBFSCoverage
