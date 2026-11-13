import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_056 : checkRows 896 16=true := by decide
theorem inverse_056 : checkRowInverse 896 16=true := by decide
theorem inversebounds_056 : (List.range' 896 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_056
#print axioms DirectBFSCoverage.inverse_056
#print axioms DirectBFSCoverage.inversebounds_056
end DirectBFSCoverage
