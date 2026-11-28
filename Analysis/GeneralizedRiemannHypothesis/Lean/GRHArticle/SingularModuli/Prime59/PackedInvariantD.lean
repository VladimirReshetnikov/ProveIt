import GRHArticle.SingularModuli.Prime59.PackedInputs

namespace GRHArticle.SingularModuli.Prime59

open IntegerPolynomialExpression

set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def packed1586D : ℤ := integer_checkpoint% (packedDiscriminant 1586)

theorem packed1586D_eq : packed1586D = packedDiscriminant 1586 := by decide +kernel

end GRHArticle.SingularModuli.Prime59
