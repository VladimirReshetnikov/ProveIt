import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_021 : checkRows 336 16=true := by decide
theorem inverse_021 : checkRowInverse 336 16=true := by decide
theorem inversebounds_021 : (List.range' 336 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem vertical_021 : checkVertical 336 16=true := by decide
theorem verticalbounds_021 : (List.range' 336 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_021
#print axioms DirectBFSCoverage.inverse_021
#print axioms DirectBFSCoverage.inversebounds_021
#print axioms DirectBFSCoverage.vertical_021
#print axioms DirectBFSCoverage.verticalbounds_021
end DirectBFSCoverage
