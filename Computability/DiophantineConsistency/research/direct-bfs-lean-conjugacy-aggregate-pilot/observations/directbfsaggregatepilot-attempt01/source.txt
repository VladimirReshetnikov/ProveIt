import DirectBFSCoverage000
import DirectBFSCoverage001

set_option autoImplicit false
set_option Elab.async false
namespace DirectBFSAggregatePilot
open DirectBFSConjugacyChunk DirectBFSCoverage

theorem rows_first_32 : checkRows 0 32=true := by
  have h0 := rows_000
  have h1 := rows_001
  unfold checkRows at h0 h1 ⊢
  have hr : List.range' 0 32=List.range' 0 16++List.range' 16 16 := by
    simpa using (List.range'_append_1 (s:=0) (m:=16) (n:=16)).symm
  rw [hr,List.all_append,h0,h1]
  rfl

#print axioms DirectBFSAggregatePilot.rows_first_32
end DirectBFSAggregatePilot
