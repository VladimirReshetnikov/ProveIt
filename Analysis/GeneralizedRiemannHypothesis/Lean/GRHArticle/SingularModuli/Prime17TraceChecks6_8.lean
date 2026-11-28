import GRHArticle.SingularModuli.Prime17DiagonalData

/-!
# All trace rows of the level-17 diagonal.
-/

namespace GRHArticle.SingularModuli.Prime17Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem traceCheck6 : TraceCheck 6 := by decide +kernel
theorem traceCheck7 : TraceCheck 7 := by decide +kernel
theorem traceCheck8 : TraceCheck 8 := by decide +kernel

end GRHArticle.SingularModuli.Prime17Data
