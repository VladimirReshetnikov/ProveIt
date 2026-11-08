import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_055 : checkRows 880 16=true := by decide
theorem inverse_055 : checkRowInverse 880 16=true := by decide
theorem inversebounds_055 : (List.range' 880 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_055
#print axioms DirectBFSCoverage.inverse_055
#print axioms DirectBFSCoverage.inversebounds_055
end DirectBFSCoverage
