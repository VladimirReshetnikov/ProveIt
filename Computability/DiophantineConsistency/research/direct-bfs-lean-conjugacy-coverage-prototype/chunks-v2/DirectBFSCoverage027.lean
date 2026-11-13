import DirectBFSConjugacyChunk
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverage
open DirectBFSConjugacyChunk
theorem rows_027 : checkRows 432 16=true := by decide
theorem inverse_027 : checkRowInverse 432 16=true := by decide
theorem inversebounds_027 : (List.range' 432 16).all (fun j => decide (DirectBFSConjugacyBase.rowMap.getD j 0 < 943 ∧ DirectBFSConjugacyBase.rowInverse.getD j 0 < 943)) = true := by decide
theorem vertical_027 : checkVertical 432 7=true := by decide
theorem verticalbounds_027 : (List.range' 432 7).all (fun j => decide (DirectBFSConjugacyBase.vertical.getD j 0 < 439 ∧ DirectBFSConjugacyBase.verticalInverse.getD j 0 < 439)) = true := by decide
#print axioms DirectBFSCoverage.rows_027
#print axioms DirectBFSCoverage.inverse_027
#print axioms DirectBFSCoverage.inversebounds_027
#print axioms DirectBFSCoverage.vertical_027
#print axioms DirectBFSCoverage.verticalbounds_027
end DirectBFSCoverage
