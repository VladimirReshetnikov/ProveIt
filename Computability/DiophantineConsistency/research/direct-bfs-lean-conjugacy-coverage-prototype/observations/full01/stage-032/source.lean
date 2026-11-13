import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_032 : checkRows 512 16=true := by decide
theorem inverse_032 : checkRowInverse 512 16=true := by decide
theorem inversebounds_032 : (List.range' 512 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_032
#print axioms DirectBFSCoverage.inverse_032
#print axioms DirectBFSCoverage.inversebounds_032
end DirectBFSCoverage
