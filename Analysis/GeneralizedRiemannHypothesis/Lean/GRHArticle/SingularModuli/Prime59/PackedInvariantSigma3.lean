import GRHArticle.SingularModuli.Prime59.PackedInputs

namespace GRHArticle.SingularModuli.Prime59

open IntegerPolynomialExpression

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def packed1586Sigma3 : ℤ := integer_checkpoint% (packedLeafChunks 1586 sigma3Chunks)

theorem packed1586Sigma3_eq : packed1586Sigma3 = packedLeafChunks 1586 sigma3Chunks := by decide +kernel

end GRHArticle.SingularModuli.Prime59
