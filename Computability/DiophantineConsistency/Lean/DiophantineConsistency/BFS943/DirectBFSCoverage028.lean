import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_028 : checkRows 448 16=true := by decide
theorem inverse_028 : checkRowInverse 448 16=true := by decide
theorem inversebounds_028 : (List.range' 448 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_028
#print axioms DirectBFSCoverage.inverse_028
#print axioms DirectBFSCoverage.inversebounds_028
end DirectBFSCoverage
