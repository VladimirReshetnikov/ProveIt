import PA194AX11HCandidateDrain
import PA194AX11HCompareRows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace PA194AX11HCopyPaths
open PA194AX11HCandidateDrain PA194AX11HCompareRows

theorem path1 : CandidateIncrements 3652 3653 [1,6] :=
  .inc _ _ _ _ (by decide) s3653
    (.inc _ _ _ _ (by decide) s3654 (.jump _ (by decide) s3655))
theorem path2 : CandidateIncrements 3656 3657 [4] :=
  .inc _ _ _ _ (by decide) s3657 (.jump _ (by decide) s3658)
#print axioms path1
#print axioms path2
end PA194AX11HCopyPaths
