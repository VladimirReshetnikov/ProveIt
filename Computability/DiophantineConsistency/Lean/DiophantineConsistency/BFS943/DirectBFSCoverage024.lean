import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_024 : checkRows 384 16=true := by decide
theorem inverse_024 : checkRowInverse 384 16=true := by decide
theorem inversebounds_024 : (List.range' 384 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem vertical_024 : checkVertical 384 16=true := by decide
theorem verticalbounds_024 : (List.range' 384 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_024
#print axioms DirectBFSCoverage.inverse_024
#print axioms DirectBFSCoverage.inversebounds_024
#print axioms DirectBFSCoverage.vertical_024
#print axioms DirectBFSCoverage.verticalbounds_024
end DirectBFSCoverage
