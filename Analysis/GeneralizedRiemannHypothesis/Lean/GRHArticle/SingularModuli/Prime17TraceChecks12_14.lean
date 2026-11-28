import GRHArticle.SingularModuli.Prime17DiagonalData

/-!
# All trace rows of the level-17 diagonal.
-/

namespace GRHArticle.SingularModuli.Prime17Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem traceCheck12 : TraceCheck 12 := by decide +kernel
theorem traceCheck13 : TraceCheck 13 := by decide +kernel
theorem traceCheck14 : TraceCheck 14 := by decide +kernel

end GRHArticle.SingularModuli.Prime17Data
