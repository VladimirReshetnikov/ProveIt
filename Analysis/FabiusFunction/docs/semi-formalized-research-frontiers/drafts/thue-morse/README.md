# Thue-Morse

The Thue-Morse side of the corpus, consolidated (2026-08-28) into the
single volume [`Thue_Morse_Atlas_and_Frontiers.tex`](Thue_Morse_Atlas_and_Frontiers/Thue_Morse_Atlas_and_Frontiers.tex)
([PDF](Thue_Morse_Atlas_and_Frontiers/Thue_Morse_Atlas_and_Frontiers.pdf);
the 144-page `b899` publication and 137-page predecessor are historical; the
accepted merged-source render is in the [merge-28de4e51 receipt
register](../MANIFEST.md#merge-28de4e51-publication-receipts)):

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
  verification, one profile figure). Its current 1,763-line, 56,530-byte
  source has SHA-256
  `eee5751653bb19ec04042f51ded34d74bf8862f5b06b49d47e68ea78bb689c45`.
  Three serial halt-on-error passes from absent auxiliaries produced
  23 pages/768,048 bytes, 24 pages/778,598 bytes, and a final 24-page,
  778,595-byte PDF with SHA-256
  `8db0c4e0a4fcf682bd3e1311f7d8197ea04dcca56e102236b52494267d99cbbe`.
  The final log, metadata, A4/rotation-zero, all-page render/text, and
  representative visual gates passed; all 22 font rows are embedded/subset,
  seven are Libertinus, none is Type 3, and generated sidecars are absent.
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
three loads `docs/fabius-notation.tex`. Cross-package comparison, canonical
selection, proof checking, numerical reproduction, and Lean crosswalking remain
deferred; the first package alone now has the synchronized publication receipt
above. The volume's own Prouhet and prefix-sum material is the natural merge
target.

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
extension is asserted. The local and incoming 144-page receipts are both
historical after the merged TeX source changed. The local first-merge tuple is
root
`10557L/482022B/8cef828c3d92a0017e22463ac90878a5e3a98e1138059d5f4793d47c04a88404`,
two-file aggregate
`10841L/493857B/79a43711c6989336166d6b2ed1faa306cc985b8d70557025ab139791d455723c`,
passes `139/144/144`, PDF
`144pp/1740015B/deb63fe66fc8f020bb072acbc4301e9b7c9f0559b165cbae2c076f261405c5be`,
and final log
`1503L/59417B/1219dbc87bc4f9920c40b24659182220b14e7908a45a9eb33d0f19390148c64b`.
The incoming `b899` source had 10,553 lines / 481,614 bytes / SHA-256
`cced4128c359ec467baaf1a55c21c68424397f783a39ea7fe2af5a94975b9dd5`;
passes 139/144/144 produced a 1,739,884-byte PDF with SHA-256
`1c81863b0976017fab1b7f5972c50cd541b3ffb05306bf85994548a56a782fc0`.
Both checkpoints passed their recorded gates. The former 137- and 143-page
artifacts remain earlier history, and a merged-source receipt is pending.

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

## Six further arrivals (2026-09-04)

Six more independently written Thue–Morse articles arrived on 2026-09-04
(intake commit `cc21b6e81`) and are filed as separate members, not compared,
deduplicated, or merged into the volume:

- [`Thue_Morse_Boundary_Corrections/`](Thue_Morse_Boundary_Corrections/) —
  *Exact Boundary Corrections for Thue–Morse Diffraction* (25 pp A4;
  1,690 source lines; 14 theorems).  Identifies the entire sub-cutoff error of
  the finite diffraction measure with one signed Stern sequence and derives a
  corrected positive density exact through the bandwidth, with sharp
  negative-Sobolev rates.
- [`Thue_Morse_Dyadic_Completion/`](Thue_Morse_Dyadic_Completion/) —
  *A Dyadic Completion of the Thue–Morse Product* (30 pp A4; 2,223 source
  lines; 10 theorems, 4 open questions).  Completes the Laplace product by the
  Fabius uniform-sum transform, gets `K(2t) = K(t)/t`, and concludes that every
  positive shift of the Thue–Morse Dirichlet function has infinitely many
  nonreal zeros in the left half-plane.
- [`Thue_Morse_New_Directions/`](Thue_Morse_New_Directions/) —
  *Thue–Morse Beyond the Atlas: Boundary Defects, Nonlinear Prouhet Geometry,
  and Flat Automatic q-Products* (30 pp A4; 2,067 source lines; 9 theorems).
  Exact dyadic correlation defects from one finite boundary functional, a
  hypergraph-covering reading of the cancellation order, and an all-order
  Lambert-`W` saddle expansion for the automatic geometric product.
- [`Thue_Morse_Rational_Resonances/`](Thue_Morse_Rational_Resonances/) —
  *Rational Resonances and Coalescing Roots of the Thue–Morse Polynomials*
  (30 pp Letter; 1,427 source lines; 11 theorems).  Local profiles in windows
  of width `2^-m` about each rational frequency, the Fabius Laplace transform
  at dyadic roots, a hierarchy of double-scaling limits, and a cyclotomic
  product identity.
- [`Thue_Morse_Research/`](Thue_Morse_Research/) — *New Deductions from
  Thue–Morse Cancellation* (26 pp A4; 1,927 source lines; 11 theorems).
  All-orders `C^k` spline corrections without removing knot neighborhoods, the
  exact polynomiality of finite spline values in `4^-m` at a fixed dyadic
  argument, an exact differential conversion formula for repeated summation,
  and the moments `2^r(r+1)` of the Fourier-energy density.
- [`thue_morse_research_article/`](thue_morse_research_article/) —
  *Thue–Morse Mellin Renormalization and Gamma-Tower Uniqueness*
  (24 pp Letter; 1,551 source lines; 6 theorems).  The same dyadic completion,
  with an all-orders expansion at the negative-integer zeros and a
  classification of the completely monotone solutions of the dyadic equation.

Two overlaps are already visible and are the natural first work on this batch.
`Thue_Morse_Dyadic_Completion/` and `thue_morse_research_article/` build the
same completion of the Thue–Morse Laplace product by the Fabius transform and
draw consequences for the same Dirichlet function; they are the obvious
consolidation pair.  Separately, the exact-polynomiality-in-`4^-m` result of
`Thue_Morse_Research/` is the mechanism of the three recurrence-free
dyadic-value articles filed in the same batch under
[`../inverse-and-sampling/dyadic-up-extraction/`](../inverse-and-sampling/dyadic-up-extraction/).

Directory names are the archive stems throughout: one archive shipped no
wrapping directory, and `thue_morse_research_article.zip` wrapped
`thue_morse_research/`, which Windows would not distinguish from its sibling
`Thue_Morse_Research/`.  Submitted `SHA256SUMS` ledgers were verified in full
and then retired under repository policy; historical bytes remain recoverable
from Git.  Eight CSV tables in two of the packages received the repository's
CRLF-to-LF normalization at commit.  No source loads
`docs/fabius-notation.tex`.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
