# Thue-Morse

The Thue-Morse side of the corpus, consolidated (2026-08-28) into the
single volume [`Thue_Morse_Atlas_and_Frontiers.tex`](Thue_Morse_Atlas_and_Frontiers/Thue_Morse_Atlas_and_Frontiers.tex)
([PDF](Thue_Morse_Atlas_and_Frontiers/Thue_Morse_Atlas_and_Frontiers.pdf),
137 pp):

- **Part I** — *A Unified Formula Atlas for the Thue–Morse Sequence*
  (formerly `Thue_Morse_Formula_Atlas/`);
- **Part II** — *A Finite-Block Calculus for the
  Fabius–Rvachev–Thue–Morse System* (block bridges, the zeta–Lambert
  tail calculus, q-Richardson weights; formerly
  `Fabius_Rvachev_Thue_Morse_Frontier_Results/`, its figures and
  reproducibility bundle under `assets/`).

## Diagonal polynomials of repeated Thue–Morse summation (three arrivals, 2026-09-03)

Three independently written articles on one question arrived together and
are filed as separate members, not yet compared or merged into the volume:

- [`thue_morse_diagonal_polynomials/`](thue_morse_diagonal_polynomials/) —
  *Diagonal Polynomials and Dyadic Block Geometry in Repeated Thue–Morse
  Summation* (24 pp A4; 14 theorems; Wolfram Language table code, Python
  verification, one profile figure).
- [`thue_morse_diagonal_polynomials-2/`](thue_morse_diagonal_polynomials-2/) —
  *Diagonal Polynomial Laws in Odd Iterated Thue–Morse Summation* (37 pp A4;
  11 theorems, 1 conjecture; Riordan-array structure and 2-adic Bell
  recurrences; exact Python and Wolfram Language implementations).
- [`thue_morse_diagonal_polynomials_article_and_code/`](thue_morse_diagonal_polynomials_article_and_code/) —
  *Diagonal Polynomials and Dyadic Block Geometry in Repeated Thue–Morse Prefix
  Summation* (33 pp A4; 10 theorems, 10 propositions; denominator laws and
  rational roots; generated CSV tables and a verification report).

The shared object is the table `s(n,k)` built from the signed Thue–Morse
prefix row by the weighted recurrence `s(n,k) = Σ_{j<k} (k−j) s(n−1,j)`; all
three identify it with the odd iterated prefix sums, `s(n,k) = σ_{2n+1}(k−n−1)`,
and derive the polynomial on every diagonal from the generating identity
`Σ_m D_m(x) z^m = TM(z²)/(1−z)^{2x}`, `TM(z) = Π_j (1 − z^{2^j})`. None of the
three loads `docs/fabius-notation.tex`. Comparison, canonical selection,
proof checking, numerical reproduction, and Lean crosswalking are deferred;
the volume's own Prouhet and prefix-sum material is the natural merge target.

Both parts carry extensive inline Lean crosswalks. As of 2026-08-28,
`ThueMorseComplexProductBridge.lean` supplies the finite-product core in total
complex form at every level: the sinc and negative-Laplace block equalities
include the removable origin, with quotient normalizations away from zero and
simp laws for the normalized origin values, together with the exact finite
Fourier--Laplace rotation between the two prefixes.
`UniformDigitThueMorseBridge.lean` identifies the characteristic function of
the finite centered digit prefix with the normalized sinc prefix, substitutes
that equality into the total Thue--Morse block formula, and solves back for the
characteristic function away from frequency zero.  These are finite-prefix
identities, not an infinite-product or random-tail limit. The analytic-logarithm,
certified-remainder, and measure-refinement results named in the volume also
have formal counterparts; the remaining roadmap obligations stay explicitly
labeled.

The local analytic companion `ThueMorseCornerIntegral.lean` has one
definition and four theorems: `centeredBoxIntegral`,
`centeredBoxIntegral_zero`, `centeredBoxIntegral_succ`,
`symmetricMixedDifference_range_eq_centeredBoxIntegral`, and
`symmetricMixedDifference_univ_eq_centeredBoxIntegral`.  It proves the
repeated-integral clause of the continuous Thue--Morse corner theorem without
replacing the manuscript's local regularity by a global assumption.  On an
open order-connected set containing the full symmetric segment, local
`ContDiffOn` regularity lets interval FTC peel one centered difference at a
time; induction then identifies the Boolean corner sum with the nested box
integral of the iterated derivative.  Together with
`ThueMorseSymmetricDifference.lean`, this makes `thm:TM-corner` Exact by
composition.  Zero half-steps and depth zero are included; the analytic leaf
is real-valued and does not prove the separate Walsh conditional-expectation
corollary.

The current reciprocal-Gamma jet/tower overlay preserves that historical
status and pins the first tranche to `0ba35abd4`.  The exhaustive five-theorem
API of `ReciprocalGammaJets.lean` is `deriv_Gamma_inv_neg_nat`,
`hasDerivAt_Gamma_inv_neg_nat`, `hasDerivAt_Gamma_inv_zero`,
`analyticOrderAt_Gamma_inv_neg_nat`, and `tendsto_Gamma_inv_div_add_nat`.
It gives the exact first jet `(-1)^r r!`, simple analytic order, and punctured
local coefficient of the entire reciprocal Gamma function at every `-r`; it
does not assign a derivative to raw Gamma at a pole.

At the same commit, the first eight public declarations of
`ThueMorseGammaTower.lean` are
`hasDerivAt_dirichletMellinContinuation_neg_nat`,
`deriv_dirichletMellinContinuation_neg_nat`, `thueMorseGammaLog`,
`thueMorseGammaTower`, `thueMorseGammaLog_eq_mellin`,
`thueMorseGammaLog_eq_integral`, `thueMorseGammaLog_dyadic`, and
`thueMorseGammaTower_dyadic`.  The current integrated tree adds the ninth,
`ofReal_exp_mpLimit_eq_gammaTower_div`.  The two definitions are total for real
`a`; the Mellin, integral, dyadic, and ratio theorems require positive
parameters.  GammaLog is the chosen derivative coordinate, not a proved
`Complex.log` identity.  The source-only
`ThueMorseGammaTowerDifferential.lean` leaf adds no definitions and exactly
three theorems: `hasDerivAt_mellin_mellinKernel_parameter`,
`hasDerivAt_thueMorseGammaLog_succ`, and
`iteratedDeriv_thueMorseGammaLog`.  For every complex Mellin exponent and
positive real damping parameter the first theorem proves differentiation
under the integral with the exponent shift `s ↦ s + 1`; the other two give
`L_(r+1)'(a) = (r+1)L_r(a)` and the full falling-factorial iterated law for
`k ≤ r`.  Thus `p2:thm:gamma-tower` is Exact when its displayed logarithm is
read, as above, as the chosen GammaLog coordinate.  Every differential theorem
retains `0 < a`; no principal-`Complex.log` identity or nonpositive-parameter
extension is asserted. The accepted first-merge receipt, now historical, is root
`10557L/482022B/8cef828c3d92a0017e22463ac90878a5e3a98e1138059d5f4793d47c04a88404`,
two-file aggregate
`10841L/493857B/79a43711c6989336166d6b2ed1faa306cc985b8d70557025ab139791d455723c`,
passes `139/144/144`, PDF
`144pp/1740015B/deb63fe66fc8f020bb072acbc4301e9b7c9f0559b165cbae2c076f261405c5be`,
and final log
`1503L/59417B/1219dbc87bc4f9920c40b24659182220b14e7908a45a9eb33d0f19390148c64b`.
Every recorded prohibited-log, A4/rotation, PDF 1.5, encryption, font/subsetting,
Libertinus, Type-3, and visual gate passed at that checkpoint. The former
143-page PDF remains an earlier historical render. The accepted current
source/PDF receipt is in the [authoritative receipt
register](../MANIFEST.md#current-post-merge-publication-receipts).

`CentralBinomialValuation.lean` supplies the atlas's direct central-binomial
crosswalk.  Its exhaustive public API is
`padicValNat_two_centralBinom`,
`thueMorseSign_eq_neg_one_pow_centralBinom`, and
`padicValNat_two_centralBinom_eq_zero_iff`: the valuation of `C(2n,n)` is
`binaryWeight n`, its parity gives the Thue--Morse sign, and it vanishes only
at `n = 0` (positive powers of two have valuation one).

`BinaryDigitFloor.lean` supplies the exact floor-difference form of a binary
digit.  Its exhaustive public API is `div_two_pow_succ_eq_div_div`,
`sub_two_mul_div_two`, `div_two_pow_sub_two_mul_div_two_pow_succ`, and
`testBit_toNat_eq_div_sub_two_mul_div`: dyadic quotients compose, parity is the
remainder after twice the quotient, and the `j`-th bit indicator is the
difference of two consecutive dyadic quotients.  These are total identities on
natural-number inputs; they do not assert a real-floor or analytic extension.

The member drafts were absorbed content-preservingly (labels, citation
keys, and asset paths mechanically prefixed per part; wrapper metadata
and section-counter handling normalized; no mathematical content
altered) and their directories deleted; provenance with SHA-256 hashes
is recorded in the volume itself, and git history is the archive.

The consolidated volume directory is the only document build root.  The
relocated Part II bundle under `assets/` contains figures and
reproducibility material only; it no longer contains a standalone TeX or
PDF manuscript.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
