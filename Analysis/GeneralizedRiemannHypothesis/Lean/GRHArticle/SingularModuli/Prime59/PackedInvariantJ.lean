import GRHArticle.SingularModuli.Prime59.PackedInputs

namespace GRHArticle.SingularModuli.Prime59

open IntegerPolynomialExpression

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def packed1586J : ℤ := integer_checkpoint% (packedInvariant 1586)

theorem packed1586J_eq : packed1586J = packedInvariant 1586 := by decide +kernel

end GRHArticle.SingularModuli.Prime59
