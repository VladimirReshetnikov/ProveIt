import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_026 : checkRows 416 16=true := by decide
theorem inverse_026 : checkRowInverse 416 16=true := by decide
theorem inversebounds_026 : (List.range' 416 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem vertical_026 : checkVertical 416 16=true := by decide
theorem verticalbounds_026 : (List.range' 416 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_026
#print axioms DirectBFSCoverage.inverse_026
#print axioms DirectBFSCoverage.inversebounds_026
#print axioms DirectBFSCoverage.vertical_026
#print axioms DirectBFSCoverage.verticalbounds_026
end DirectBFSCoverage
