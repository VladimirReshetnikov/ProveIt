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

/-!
Integer points in circles: formal statements of the results of Zhai–Cao
(Acta Arith. 90, 1999) and Wu (Monatsh. Math. 135, 2002) on the primitive
circle problem under the Riemann Hypothesis, with proofs of the elementary
parts: the implications between the main theorems, the region-coverage
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
Zhai–Cao's Lemma 9 by Heath-Brown's method from Lemmas 1 and 6.  Every statement is a `Prop`-valued definition; proved ones
have a companion `…_holds` theorem.
-/
