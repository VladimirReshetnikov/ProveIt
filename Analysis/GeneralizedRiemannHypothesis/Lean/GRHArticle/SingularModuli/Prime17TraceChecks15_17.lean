import GRHArticle.SingularModuli.Prime17DiagonalData

/-!
# All trace rows of the level-17 diagonal.
-/

namespace GRHArticle.SingularModuli.Prime17Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem traceCheck15 : TraceCheck 15 := by decide +kernel
theorem traceCheck16 : TraceCheck 16 := by decide +kernel
theorem traceCheck17 : TraceCheck 17 := by decide +kernel

end GRHArticle.SingularModuli.Prime17Data
