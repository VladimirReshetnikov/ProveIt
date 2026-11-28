import GRHArticle.SingularModuli.Prime59.PackedInvariantJ
import GRHArticle.SingularModuli.Prime59.PackedInvariantD
import GRHArticle.SingularModuli.Prime59.PackedInvariantSigma3
import GRHArticle.SingularModuli.Prime59.PackedInputs
import GRHArticle.SingularModuli.Prime59.InvariantWidth

namespace GRHArticle.SingularModuli.Prime59

open IntegerPolynomialExpression

set_option maxRecDepth 100000
set_option maxHeartbeats 0


private def evaluatedDifference (w : ℕ) : ℤ :=
  packedDiscriminant w * packedInvariant w -
    ((coefficients [1]).packedEval w +
      (coefficients [240]).packedEval w * packedLeafChunks w sigma3Chunks)^3

private theorem evaluatedDifference_eq (w : ℕ) :
    evaluatedDifference w = invariantDifference.packedEval w := by
  unfold evaluatedDifference invariantDifference ModularInvariantPrefixCertificate.eisensteinCubeExpr
  rewrite [packedDiscriminant_eq, packedInvariant_eq,
    packedLeafChunks_eq w sigma3Chunks, sigma3Chunks_flatten]
  rfl

private theorem residue :
    evaluatedDifference 1586 % ((1 <<< (1586*invariantPrecision) : ℕ) : ℤ) = 0 := by
  unfold evaluatedDifference
  rewrite [← packed1586D_eq, ← packed1586J_eq, ← packed1586Sigma3_eq]
  decide +kernel

theorem invariantCheck :
    ModularInvariantPrefixCertificate.InvariantCheck invariantPrecision sigma3 discriminant invariant := by
  change invariantDifference.checkZeroPrefixChunked invariantPrecision
  apply (checkZeroPrefixChunked_iff _ _).mpr
  unfold checkZeroPrefix
  dsimp only
  rewrite [invariantWidth]
  rewrite [← evaluatedDifference_eq]
  exact residue

end GRHArticle.SingularModuli.Prime59
