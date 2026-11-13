import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_053 : checkRows 848 16=true := by decide
theorem inverse_053 : checkRowInverse 848 16=true := by decide
theorem inversebounds_053 : (List.range' 848 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_053
#print axioms DirectBFSCoverage.inverse_053
#print axioms DirectBFSCoverage.inversebounds_053
end DirectBFSCoverage
