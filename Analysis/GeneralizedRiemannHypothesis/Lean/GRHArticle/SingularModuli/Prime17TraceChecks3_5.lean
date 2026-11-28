import GRHArticle.SingularModuli.Prime17DiagonalData

/-!
# All trace rows of the level-17 diagonal.
-/

namespace GRHArticle.SingularModuli.Prime17Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem traceCheck3 : TraceCheck 3 := by decide +kernel
theorem traceCheck4 : TraceCheck 4 := by decide +kernel
theorem traceCheck5 : TraceCheck 5 := by decide +kernel

end GRHArticle.SingularModuli.Prime17Data
