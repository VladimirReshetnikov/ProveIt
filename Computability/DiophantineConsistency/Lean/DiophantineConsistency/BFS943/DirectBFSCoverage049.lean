import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_049 : checkRows 784 16=true := by decide
theorem inverse_049 : checkRowInverse 784 16=true := by decide
theorem inversebounds_049 : (List.range' 784 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_049
#print axioms DirectBFSCoverage.inverse_049
#print axioms DirectBFSCoverage.inversebounds_049
end DirectBFSCoverage
