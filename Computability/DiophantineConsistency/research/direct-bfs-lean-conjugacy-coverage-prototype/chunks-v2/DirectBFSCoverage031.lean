import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_031 : checkRows 496 16=true := by decide
theorem inverse_031 : checkRowInverse 496 16=true := by decide
theorem inversebounds_031 : (List.range' 496 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
#print axioms DirectBFSCoverage.rows_031
#print axioms DirectBFSCoverage.inverse_031
#print axioms DirectBFSCoverage.inversebounds_031
end DirectBFSCoverage
