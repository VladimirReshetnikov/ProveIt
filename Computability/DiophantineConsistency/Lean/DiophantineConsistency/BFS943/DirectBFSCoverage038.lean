import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_038 : checkRows 608 16=true := by decide
theorem inverse_038 : checkRowInverse 608 16=true := by decide
theorem inversebounds_038 : (List.range' 608 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_038
#print axioms DirectBFSCoverage.inverse_038
#print axioms DirectBFSCoverage.inversebounds_038
end DirectBFSCoverage
