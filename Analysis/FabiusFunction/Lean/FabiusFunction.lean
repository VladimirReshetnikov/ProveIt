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
-/
