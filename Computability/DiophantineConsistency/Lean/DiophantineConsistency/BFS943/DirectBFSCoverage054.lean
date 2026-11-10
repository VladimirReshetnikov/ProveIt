import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_054 : checkRows 864 16=true := by decide
theorem inverse_054 : checkRowInverse 864 16=true := by decide
theorem inversebounds_054 : (List.range' 864 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_054
#print axioms DirectBFSCoverage.inverse_054
#print axioms DirectBFSCoverage.inversebounds_054
end DirectBFSCoverage
