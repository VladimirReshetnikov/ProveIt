import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_036 : checkRows 576 16=true := by decide
theorem inverse_036 : checkRowInverse 576 16=true := by decide
theorem inversebounds_036 : (List.range' 576 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_036
#print axioms DirectBFSCoverage.inverse_036
#print axioms DirectBFSCoverage.inversebounds_036
end DirectBFSCoverage
