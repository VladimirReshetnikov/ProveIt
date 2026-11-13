import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_018 : checkRows 288 16=true := by decide
theorem inverse_018 : checkRowInverse 288 16=true := by decide
theorem inversebounds_018 : (List.range' 288 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem vertical_018 : checkVertical 288 16=true := by decide
theorem verticalbounds_018 : (List.range' 288 16).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_018
#print axioms DirectBFSCoverage.inverse_018
#print axioms DirectBFSCoverage.inversebounds_018
#print axioms DirectBFSCoverage.vertical_018
#print axioms DirectBFSCoverage.verticalbounds_018
end DirectBFSCoverage
