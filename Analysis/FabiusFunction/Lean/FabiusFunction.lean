import FabiusFunction.Paper05442
import FabiusFunction.Paper06487
import FabiusFunction.PaperFabiusAsymptotic
import FabiusFunction.PaperKFoldThueMorse
import FabiusFunction.NegativeLaplace
import FabiusFunction.PeriodicCorrection
import FabiusFunction.MellinBose
import FabiusFunction.MellinFinitePart
import FabiusFunction.BoseFinitePartIntegral
import FabiusFunction.PeriodicMean
import FabiusFunction.PeriodicRegularity
import FabiusFunction.LaplacePeriodicSecondOrder
import FabiusFunction.FabiusTranslatedLegendreSeries
import FabiusFunction.FabiusLegendreLeastSquares
import FabiusFunction.Monotonicity
import FabiusFunction.Regularity
import FabiusFunction.Convexity
import FabiusFunction.EffectiveFlatness
import FabiusFunction.SharpFlatness
import FabiusFunction.FabiusInverse
import FabiusFunction.GlobalBounds
import FabiusFunction.BoundedDerivatives
import FabiusFunction.NowhereAnalytic
import FabiusFunction.ElementaryFunction
import FabiusFunction.NotElementary
import FabiusFunction.FabiusComputableSpline
import FabiusFunction.FabiusSaddleJetClosedForm
import FabiusFunction.FabiusSaddleExponentClosedForm
import FabiusFunction.FabiusSaddleJetStirling
import FabiusFunction.FabiusSecondSaddleCorrection

/-!
# Fabius function

Public import surface for the bounded Fabius function, its signed global
extension, exact dyadic arithmetic, and the complete proved formalizations of
arXiv:1702.05442 and arXiv:1702.06487v3.  It also exposes claim-level audits
of the two local TeX drafts on Fabius asymptotics and K-fold Thue--Morse
summation, including corrected results and formal counterexamples to their
false claims.  The public surface also includes the exact negative-Laplace
product, its Gamma--zeta periodic correction, and the unconditional corrected
sharp small-argument asymptotic.
It also exposes the exact Fourier--Legendre expansion of Rvachev's up
function, with absolute uniform convergence on `[-1,1]`, and its translated
monomial representation of the signed global Fabius function on `[0,2]`.
Every finite even Legendre partial sum is also proved to be the unique
least-squares best polynomial approximation in its degree class.
The inverse-dyadic recurrence also has a finite nonrecursive solution as an
explicit weighted sum over ordered compositions.

The regularity layer adds the sharp global shape of the two functions: the
single differential equation `F'(x) = 2 up(2x - 1)` valid on all of `ℝ`, the
optimal Lipschitz constant `2` for both `F` and `up`, strict monotonicity of
`F` on `[0,1]` together with the resulting bijection of `[0,1]` onto itself,
the exact support `(-1,1)` of `up` and its strict unimodality, convexity of
`F` on `(-∞,1/2]` and concavity on `[1/2,∞)`, the effective flatness bound
`F(x) ≤ 2^C(n+1,2) x^n` on `2^n x ≤ 1`, the sharp uniform derivative bounds
`|F^(k)| ≤ 2^C(k+1,2)` with the value attained, and the exact real-analytic
locus: `F` is analytic at `x` if and only if `x ∉ [0,1]`.

The regularity layer also inverts the bijection `F : [0,1] → [0,1]`.  The
inverse is continuous and monotone on all of `ℝ` once totalized by the
endpoint values, and the flatness bounds transport through it into lower
bounds `y ≤ 2^C(n+1,2) · F⁻¹(y)^n`: the inverse is steeper than every root at
the origin, with `F⁻¹(y)/y → ∞` as `y → 0⁺`.

The small-argument asymptotic layer is completed by closed forms for the
objects that previously existed only as recursions.  The differential
recurrence for the periodic saddle jets is solved: the `n`-th jet is a
harmonic-number constant plus a sum of the first `n+1` derivatives of the
centered periodic correction, weighted by the coefficients of
`∏ k ∈ Finset.Icc 1 n, (X - k)`, that is, by signed Stirling numbers of the
first kind.  The saddle exponent coefficients likewise collapse to one power
of `I` multiplying a jet term and a universal jet-free tail.  Together these
make every coefficient of the all-orders expansion an explicit finite
expression with rational coefficients in `1 / log 2` and the derivatives of
the periodic correction, rather than the output of a recursion.  See
`docs/Small_Argument_Asymptotics/`.

Finally, the canonical bounded Fabius function is proved computable in the
Grzegorczyk sense: a primitive-recursive centered-spline evaluator preserves
computable dyadic names, and the explicit recursive modulus `d(n)=2n` gives
effective uniform continuity.
-/
