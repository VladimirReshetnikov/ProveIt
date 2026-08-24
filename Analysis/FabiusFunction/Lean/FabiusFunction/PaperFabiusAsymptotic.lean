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
import FabiusFunction.FabiusRawQBinomialFormula
import FabiusFunction.FabiusGlobalQBinomialSeries
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
conjectured at
https://math.stackexchange.com/questions/3283519/conjectured-formula-for-the-fabius-function
is formalized in its full scope: for every `m,n : ℕ`, including zero and
unreduced dyadic representations, the source's half-shifted rational sum is
the signed global Fabius value at `m / 2^n`.  No assumption `m ≤ 2^n` is
needed for that theorem.  Under `m ≤ 2^n`, a separate corollary identifies
the same sum with every bounded function satisfying `IsFabius`.  The formula
is invariant both under equal representations of a nonnegative dyadic
rational (in particular `(m,n) ↦ (2m,n+1)`) and under every common rational
translation of its inner powers.  Explicitly, for every `q : ℚ` the fully
displayed sum containing `(j - m * 2^k + q)^(n+k)` computes the same dyadic
value; this includes both the centered and source-faithful `+1/2` versions.
For `m = 1`, dyadic reflection also gives the arbitrary-`q` raw-coordinate
form with inner power `(r+q)^(n+k)` and denominator `(-2)^(n^2)`.
The corresponding infinite binary-reduction formula is proved after restoring
its missing scale-zero term.  For every `x ≥ 0` and every real or complex
translation `q`, the literal nested series is absolutely convergent and equals
the signed global Fabius extension.  On `[0,1]` it equals the bounded Fabius
function.  Polynomial constancy, rather than density alone, makes the
extension from rational to real and complex `q` exact.
See `PAPER_COVERAGE.md` for the exact claim matrix.
-/
