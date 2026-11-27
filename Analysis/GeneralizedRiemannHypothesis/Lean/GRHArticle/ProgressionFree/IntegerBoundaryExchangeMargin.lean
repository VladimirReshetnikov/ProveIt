import GRHArticle.ProgressionFree.IntegerBoundaryPrimeProduct
import GRHArticle.ProgressionFree.IntegerBoundaryPrimeSieve
import GRHArticle.ProgressionFree.IntegerBoundaryDensityBridge

/-!
# Numerical margin in the exchange of rational and integral ratio conventions

Use the finite Euler-product lower bound and the prime-square upper bound
at the same cutoff. The wheel estimate after the finite sieve yields a
slightly larger margin than the one printed in the article.
-/

namespace GRHArticle.ProgressionFree

theorem integerBoundaryExchange_margin :
    (135206:ℝ)/10^9 < integerSmoothDensityFactor 6619 * integerExchangeGain - integerPrimeSquareTail 6619 := by
  have hc := mul_le_mul_of_nonneg_right integerSmoothDensityFactor_6619_lower integerExchangeGain_pos.le
  have ht := integerPrimeSquareTail_6619_upper
  norm_num [integerExchangeGain] at hc ht ⊢
  linarith only [hc,ht]

end GRHArticle.ProgressionFree
