import FabiusFunction.FabiusLogScale
import FabiusFunction.FabiusLogMainDefect
import FabiusFunction.FabiusDyadicLogBounds
import FabiusFunction.FabiusLogSquaredAsymptotic
import FabiusFunction.FabiusFlatness
import FabiusFunction.FabiusSharpAsymptotic
import FabiusFunction.FabiusSharpExactReduction
import FabiusFunction.FabiusFullAsymptoticExpansion
import FabiusFunction.FabiusLambertAllOrderSmallArgument
import FabiusFunction.FabiusRecurrenceSequence
import FabiusFunction.FabiusQBinomialFormula
import FabiusFunction.FabiusFirstSaddleCorrection
import FabiusFunction.FabiusSaddleCoefficientRecurrence
import FabiusFunction.PeriodicSmooth
import FabiusFunction.SaddleExpansionAlgebra
import FabiusFunction.SaddleAllOrders
import FabiusFunction.NegativeLaplaceVerticalSmooth

/-!
# Claim-level audit of the local *Fabius Asymptotic* draft

The TeX source in `Papers/Fabius Asymptotic/` contains no `theorem`, `lemma`,
`proposition`, or `corollary` environments.  This public aggregate therefore
tracks its numbered equations and substantive prose claims rather than a list
of formally named source results.

The exact logarithmic delay identity, the elementary logarithm expansions,
and the coarse log-squared asymptotic are proved.  The explicit sharp main
term proposed by the draft is also substituted into the delay equation and
its residual is determined: it has a nonzero multiple of
`(log t / t)^2` as its leading term.  In particular, the draft's later
replacement of this residual by `O(t^-2)` is formally disproved.

No theorem in this development asserts the draft's unsupported periodic-in-`t`
remainder or derives a sharp expansion from that invalid argument.  A separate
Laplace-product, Mellin, and quantitative saddle analysis does prove the
correct sharp formula: its genuine nonconstant periodic correction is sampled
at the lower-Lambert phase, and the literal elementary expression printed in
the linked Math Stack Exchange discussion is proved to be missing that term.
The public aggregate also exposes the generic formal exponential recurrence,
the concrete periodic saddle jets, arbitrary-order Gaussian integration
machinery, and branch-safe vertical Taylor estimates used to refine this
formula to all orders.  For every `N`, the exact lower-Lambert expansion has
an `O(lambda^-N)` remainder; the lower-Lambert phase itself also has a
separate all-orders expansion in `-log x` and `log (-log x)`.
The related Mathematica Stack Exchange quotient is also proved not to be an
endpoint asymptotic equivalent.  The finite q-binomial/Thue--Morse formula
for every inverse-dyadic Fabius value is formalized as well, including its
centered signed power sum and the case `n = 0`.  See `PAPER_COVERAGE.md` for
the exact claim matrix.
-/
