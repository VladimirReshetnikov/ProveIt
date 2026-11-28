import GRHArticle.SingularModuli.Prime59.InputPrefixes
import GRHArticle.SingularModuli.Prime59.DivisorInputs
import GRHArticle.SingularModuli.ModularInvariantPrefixCertificate
import GRHArticle.SingularModuli.HeckeFoldedMagnitudeBound

namespace GRHArticle.SingularModuli.Prime59

open IntegerPolynomialExpression

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def discriminantDifference : IntegerPolynomialExpression :=
  sub (mul (coefficients [0,1]) (coefficients discriminant))
    (ModularInvariantPrefixCertificate.discriminantExpr sigma3 sigma5)

theorem discriminantWidth : discriminantDifference.magnitudeBound.log2 + 1 = 161 := by
  rewrite [← magnitudeBoundFolded_eq]
  decide +kernel

end GRHArticle.SingularModuli.Prime59
