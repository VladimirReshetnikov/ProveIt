import GRHArticle.SingularModuli.Prime59.PackedInputs
import GRHArticle.SingularModuli.Prime59.DiscriminantWidth

namespace GRHArticle.SingularModuli.Prime59

open IntegerPolynomialExpression

set_option maxRecDepth 100000
set_option maxHeartbeats 0


private def evaluatedDifference (w : ℕ) : ℤ :=
  (coefficients [0,1]).packedEval w * packedDiscriminant w -
    (packedLeafChunks w linearChunks +
      (coefficients [100]).packedEval w * packedLeafChunks w sigma3Chunks ^ 2 +
      (coefficients [8000]).packedEval w * packedLeafChunks w sigma3Chunks ^ 3 -
      (coefficients [147]).packedEval w * packedLeafChunks w sigma5Chunks ^ 2)

private theorem evaluatedDifference_eq (w : ℕ) :
    evaluatedDifference w = discriminantDifference.packedEval w := by
  unfold evaluatedDifference discriminantDifference ModularInvariantPrefixCertificate.discriminantExpr
  rewrite [packedDiscriminant_eq, packedLeafChunks_eq w linearChunks, linearChunks_flatten,
    packedLeafChunks_eq w sigma3Chunks, sigma3Chunks_flatten,
    packedLeafChunks_eq w sigma5Chunks, sigma5Chunks_flatten]
  rfl

private theorem residue :
    evaluatedDifference 161 % ((1 <<< (161*(invariantPrecision+1)) : ℕ) : ℤ) = 0 := by
  decide +kernel

theorem discriminantCheck :
    ModularInvariantPrefixCertificate.DiscriminantCheck invariantPrecision sigma3 sigma5 discriminant := by
  change discriminantDifference.checkZeroPrefixChunked (invariantPrecision+1)
  apply (checkZeroPrefixChunked_iff _ _).mpr
  unfold checkZeroPrefix
  dsimp only
  rewrite [discriminantWidth]
  rewrite [← evaluatedDifference_eq]
  exact residue

end GRHArticle.SingularModuli.Prime59
