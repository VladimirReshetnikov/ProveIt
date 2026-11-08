import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_025 : checkRows 400 16=true := by decide
theorem inverse_025 : checkRowInverse 400 16=true := by decide
theorem inversebounds_025 : (List.range' 400 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem vertical_025 : checkVertical 400 16=true := by decide
theorem verticalbounds_025 : (List.range' 400 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_025
#print axioms DirectBFSCoverage.inverse_025
#print axioms DirectBFSCoverage.inversebounds_025
#print axioms DirectBFSCoverage.vertical_025
#print axioms DirectBFSCoverage.verticalbounds_025
end DirectBFSCoverage
