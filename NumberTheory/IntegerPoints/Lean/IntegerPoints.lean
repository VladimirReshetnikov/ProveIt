import IntegerPoints.Basic
import IntegerPoints.ExponentialSums
import IntegerPoints.ZhaiCao
import IntegerPoints.Wu
import IntegerPoints.Consequences
import IntegerPoints.Vaughan
import IntegerPoints.Srinivasan
import IntegerPoints.ExponentPairs
import IntegerPoints.WeylVanDerCorput
import IntegerPoints.LargeSieve
import IntegerPoints.KuzminLandau
import IntegerPoints.VanDerCorput
import IntegerPoints.Lemma1
import IntegerPoints.Lemma3
import IntegerPoints.ExponentPairHalf
import IntegerPoints.SineIntegral
import IntegerPoints.Perron
import IntegerPoints.BombieriIwaniec
import IntegerPoints.FouvryIwaniec
import IntegerPoints.AProcess
import IntegerPoints.AProcessTheorem
import IntegerPoints.Lemma9Tools
import IntegerPoints.Lemma9Core
import IntegerPoints.Lemma9Sum
import IntegerPoints.Lemma9
import IntegerPoints.GKStatements
import IntegerPoints.FouvryIwaniecStatements
import IntegerPoints.Kolesnik
import IntegerPoints.HeathBrown
import IntegerPoints.HuxleyStatements
import IntegerPoints.IwaniecMozzochi
import IntegerPoints.Hirschhorn
import IntegerPoints.LittlewoodWalfisz
import IntegerPoints.BerndtKimZaharescu
import IntegerPoints.GKLemma31
import IntegerPoints.GKLemma32
import IntegerPoints.GKLemma33
import IntegerPoints.GKLemma34
import IntegerPoints.Sawtooth
import IntegerPoints.EulerMaclaurin
import IntegerPoints.Poisson
import IntegerPoints.PoissonBounds
import IntegerPoints.PoissonIntegrals
import IntegerPoints.PoissonTail
import IntegerPoints.GKLemma35
import IntegerPoints.GKLemma36
import IntegerPoints.GKLemma37
import IntegerPoints.GKEq234
import IntegerPoints.GKTheorem21
import IntegerPoints.GKHighCurvature
import IntegerPoints.GKTheorem22
import IntegerPoints.FiniteHilbert
import IntegerPoints.GKAppendixATheorem2
import IntegerPoints.GKSec33LGeHalf
import IntegerPoints.GKSec33KNonneg
import IntegerPoints.GKSec33Boundary
import IntegerPoints.GKLemma39Class
import IntegerPoints.GKProcessWords

/-!
Integer points in circles: formal statements of the results of Zhai–Cao
(Acta Arith. 90, 1999) and Wu (Monatsh. Math. 135, 2002) on the primitive
circle problem under the Riemann Hypothesis, with machine-checked proofs of a
substantial analytic and arithmetic subset: the implications between the main
theorems, the region-coverage
argument deriving Wu's Theorem 1 from his Propositions 1–4, the Vaughan
identity of Lemma 4.1, Srinivasan's optimisation lemma, the Weyl–van der
Corput inequality, Wu's large-sieve Lemma 2.1, the Kuz'min–Landau
inequality, the van der Corput second-derivative test, and Zhai–Cao's
Lemma 1 derived from the last two, and Zhai–Cao's Lemma 3 (Krätzel's
counting lemma), and the exponent pair `(1/2, 1/2)`; `IntegerPoints.SineIntegral` proves the
Dirichlet integral `∫₀^∞ sin v/v dv = π/2` with the tail bound `2/y`, the
analytic input for the truncated Perron formula, and `IntegerPoints.Perron`
proves Zhai–Cao's Lemma 2 from it; `IntegerPoints.BombieriIwaniec` proves
Zhai–Cao's Lemma 5 by Fourier inversion of a trapezoid weight;
`IntegerPoints.FouvryIwaniec` proves Zhai–Cao's Lemma 6 (the Fouvry–Iwaniec
counting lemma) by gcd classes and the box principle; `IntegerPoints.AProcess`
proves Graham–Kolesnik's Lemma 3.7 (closure of the class `F` under
differencing) and `IntegerPoints.AProcessTheorem` proves Theorem 3.8, the
A-process `(k, l) ↦ (k/(2k+2), (k+l+1)/(2k+2))` on exponent pairs;
`IntegerPoints.Lemma9` (with `Lemma9Tools`, `Lemma9Core`, `Lemma9Sum`) proves
Zhai–Cao's Lemma 9 by Heath-Brown's method from Lemmas 1 and 6.
`IntegerPoints.GKLemma31` through `IntegerPoints.GKLemma37` prove
Graham–Kolesnik's Lemmas 3.1–3.7, including both curvature forms of the
stationary-phase Lemma 3.4, the B-process transformation of Lemma 3.6, and
the exact book form of the differencing Lemma 3.7.
`IntegerPoints.GKEq234` proves the Weyl–van der Corput inequality in the
integer-shift form used in §3.3.
`IntegerPoints.GKTheorem21` proves the reciprocal-scale exponential-sum bound
quoted from Graham–Kolesnik Theorem 2.1 and invoked in §3.3.
`IntegerPoints.GKHighCurvature` supplies the reusable second-derivative bound
used by `IntegerPoints.GKTheorem22` to prove both invoked forms of Theorem 2.2.
`IntegerPoints.FiniteHilbert` proves the sharp finite Hilbert inequality from
finite Parseval and the centered-sawtooth Fourier coefficients;
`IntegerPoints.GKAppendixATheorem2` applies it to prove the reciprocal-phase
mean-square lower bound quoted from Graham--Kolesnik Appendix A, and
`IntegerPoints.GKSec33LGeHalf` uses that lower bound to prove the §3.3
restriction `l ≥ 1/2` from the exponential-sum estimate alone;
`IntegerPoints.GKSec33KNonneg` uses factorial resonances to prove `k ≥ 0`
and the boundary implication `k = 0 → l ≥ 1`;
`IntegerPoints.GKSec33Boundary` combines the square-root exponent-pair bound,
the exact Lemma-3.6 transform, and a factorially resonant dual sum to prove
the remaining boundary implication `(k, 1/2) exponent pair → k = 1/2`;
`IntegerPoints.GKLemma39` proves the quantitative inverse-function estimate
for every derivative order through `P`, including the endpoint frequencies,
and `IntegerPoints.GKLemma39Class` packages it as the dyadically restricted
Graham--Kolesnik class used by the B-process;
`IntegerPoints.GKBProcessTheorem` assembles those ingredients to prove
Theorem 3.10, the B-process `(k, l) ↦ (l - 1/2, k + 1/2)`, and
`IntegerPoints.GKProcessWords` combines it with the A-process to prove that
every finite word in `A` and `B` sends `(0, 1)` to an exponent pair.
Every statement is a `Prop`-valued definition; proved ones have a companion
`…_holds` theorem.
-/
