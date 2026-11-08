import DiophantineConsistency.BFS943.DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_050 : checkRows 800 16=true := by decide
theorem inverse_050 : checkRowInverse 800 16=true := by decide
theorem inversebounds_050 : (List.range' 800 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_050
#print axioms DirectBFSCoverage.inverse_050
#print axioms DirectBFSCoverage.inversebounds_050
end DirectBFSCoverage
