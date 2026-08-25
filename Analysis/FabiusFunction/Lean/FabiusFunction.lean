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
import FabiusFunction.GlobalBounds
import FabiusFunction.NowhereAnalytic

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
-/
