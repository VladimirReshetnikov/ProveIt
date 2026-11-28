import GRHArticle.SingularModuli.Prime59.InputPrefixes
import GRHArticle.SingularModuli.Prime59.DivisorInputs
import GRHArticle.SingularModuli.ModularInvariantPrefixCertificate
import GRHArticle.SingularModuli.HeckeFoldedMagnitudeBound

namespace GRHArticle.SingularModuli.Prime59

open IntegerPolynomialExpression

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def invariantDifference : IntegerPolynomialExpression :=
  sub (mul (coefficients discriminant) (coefficients invariant))
    (ModularInvariantPrefixCertificate.eisensteinCubeExpr sigma3)

theorem invariantWidth : invariantDifference.magnitudeBound.log2 + 1 = 1586 := by
  rewrite [← magnitudeBoundFolded_eq]
  decide +kernel

end GRHArticle.SingularModuli.Prime59
