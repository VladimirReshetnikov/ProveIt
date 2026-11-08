import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_041 : checkRows 656 16=true := by decide
theorem inverse_041 : checkRowInverse 656 16=true := by decide
theorem inversebounds_041 : (List.range' 656 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_041
#print axioms DirectBFSCoverage.inverse_041
#print axioms DirectBFSCoverage.inversebounds_041
end DirectBFSCoverage
