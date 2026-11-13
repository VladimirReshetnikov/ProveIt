import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_044 : checkRows 704 16=true := by decide
theorem inverse_044 : checkRowInverse 704 16=true := by decide
theorem inversebounds_044 : (List.range' 704 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_044
#print axioms DirectBFSCoverage.inverse_044
#print axioms DirectBFSCoverage.inversebounds_044
end DirectBFSCoverage
