import GRHArticle.SingularModuli.Prime17DiagonalData

/-!
# All trace rows of the level-17 diagonal.
-/

namespace GRHArticle.SingularModuli.Prime17Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem traceCheck0 : TraceCheck 0 := by decide +kernel
theorem traceCheck1 : TraceCheck 1 := by decide +kernel
theorem traceCheck2 : TraceCheck 2 := by decide +kernel

end GRHArticle.SingularModuli.Prime17Data
