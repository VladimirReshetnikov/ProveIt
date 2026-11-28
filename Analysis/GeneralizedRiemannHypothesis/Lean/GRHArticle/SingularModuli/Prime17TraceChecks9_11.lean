import GRHArticle.SingularModuli.Prime17DiagonalData

/-!
# All trace rows of the level-17 diagonal.
-/

namespace GRHArticle.SingularModuli.Prime17Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem traceCheck9 : TraceCheck 9 := by decide +kernel
theorem traceCheck10 : TraceCheck 10 := by decide +kernel
theorem traceCheck11 : TraceCheck 11 := by decide +kernel

end GRHArticle.SingularModuli.Prime17Data
