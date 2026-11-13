import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_039 : checkRows 624 16=true := by decide
theorem inverse_039 : checkRowInverse 624 16=true := by decide
theorem inversebounds_039 : (List.range' 624 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_039
#print axioms DirectBFSCoverage.inverse_039
#print axioms DirectBFSCoverage.inversebounds_039
end DirectBFSCoverage
