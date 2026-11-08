import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_046 : checkRows 736 16=true := by decide
theorem inverse_046 : checkRowInverse 736 16=true := by decide
theorem inversebounds_046 : (List.range' 736 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_046
#print axioms DirectBFSCoverage.inverse_046
#print axioms DirectBFSCoverage.inversebounds_046
end DirectBFSCoverage
