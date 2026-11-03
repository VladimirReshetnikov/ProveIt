import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_047 : checkRows 752 16=true := by decide
theorem inverse_047 : checkRowInverse 752 16=true := by decide
theorem inversebounds_047 : (List.range' 752 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_047
#print axioms DirectBFSCoverage.inverse_047
#print axioms DirectBFSCoverage.inversebounds_047
end DirectBFSCoverage
