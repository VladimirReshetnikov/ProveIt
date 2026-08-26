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
import FabiusFunction.FabiusInverseDyadicClosedForm
import FabiusFunction.FabiusQBinomialFormula
import FabiusFunction.FabiusQBinomialScalarFormula
import FabiusFunction.FabiusDyadicQBinomialScalar
import FabiusFunction.FabiusRawQBinomialFormula
import FabiusFunction.FabiusRawQBinomialScalar
import FabiusFunction.FabiusGlobalQBinomialSeries
import FabiusFunction.FabiusParityPowerSeries
import FabiusFunction.FabiusDiscreteLimitIntegration
import FabiusFunction.FabiusFirstSaddleCorrection
import FabiusFunction.FabiusSaddleCoefficientRecurrence
import FabiusFunction.PeriodicSmooth
import FabiusFunction.SaddleExpansionAlgebra
import FabiusFunction.SaddleAllOrders
import FabiusFunction.NegativeLaplaceVerticalSmooth

set_option autoImplicit false

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
The inverse-dyadic recurrence is additionally solved as a finite weighted
path sum.  Equivalently, `F(2⁻ⁿ)` is an explicit product-sum over all
ordered compositions of `n`; the empty composition makes this closed formula
valid at `n = 0` as well.
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
rational (in particular `(m,n) ↦ (2m,n+1)`) and under every common translation
of its inner powers.  The finite expressions are constant polynomials over
`ℚ`, so their evaluation is valid in any field over `ℚ`, with explicit real,
complex, and Gaussian-rational endpoints.  Thus the fully displayed sum
containing `(j - m * 2^k + q)^(n+k)` computes the same dyadic value for every
real or complex `q`; this includes the centered and source-faithful `+1/2`
versions.  For `m = 1`, dyadic reflection likewise gives the raw-coordinate
form with inner power `(r+q)^(n+k)` and denominator `(-2)^(n^2)` for every
real or complex `q`.
The corresponding infinite binary-reduction formula is proved after restoring
its missing scale-zero term.  For every `x ≥ 0` and every real or complex
translation `q`, the literal nested series is absolutely convergent and equals
the signed global Fabius extension.  On `[0,1]` it equals the bounded Fabius
function.  Polynomial constancy, rather than density alone, makes the
extension from rational to real and complex `q` exact.
The related parity-power series is also corrected and proved.  Its all-`x`
version starts at scale `m = 0`, uses the signed integer exponent
`((n + 2) * (n - 1)) / 2`, and sums to the signed global Fabius extension
for every `x ≥ 0`.  On `[0,1]` it gives the bounded Fabius function.  The
source's original one-indexed series remains valid on the half-open interval
`0 ≤ x < 1`; no all-`x` claim is made for that indexing.
A separate generalized `DiscreteLimit` theorem proves that, for every real
`x ≥ 0` and fixed `q : ℂ`, the proposed finite q-binomial/Thue--Morse
approximants converge to the signed global Fabius extension; on `[0,1]` they
converge to the bounded Fabius function.  Public specializations include
Gaussian-rational, rational, and arbitrary real shifts, so irrational real
translations are covered directly.  The natural-valued range length is proved
equivalent to the source's inclusive Wolfram `Floor` cutoff, including the
empty case.  A finite approximant need not be independent of `q`: the proof
instead reindexes it exactly as a Toeplitz average of centered finite splines,
then combines uniform spline convergence with a decaying complex Taylor-shift
bound.  Exact finite-remainder q-binomial telescopes and infinite `tsum`
theorems identify the resulting q-independent limit, rather than the
individual finite rows, with the binary-reduction series above.
See `PAPER_COVERAGE.md` for the exact claim matrix.
-/
