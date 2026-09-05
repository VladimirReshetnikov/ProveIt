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
- **Part III** — *Diagonal Laws of Repeated Thue–Morse Summation*
  (the polynomial on every diagonal of the repeated weighted summation
  table, its Riordan-array and Sheffer structure, exact denominators and
  rational roots, the complete half-integer zero criterion, the dyadic
  block geometry of every summation order, the exact crosswalk to the
  Lean approximation polynomials, and exact algorithms; folded in on
  2026-09-05 from the companion `Thue_Morse_Diagonal_Laws/`, itself the
  same-day consolidation of the three `thue_morse_diagonal_polynomials*`
  arrivals of 2026-09-03; its verification bundle and figures are under
  `assets/diagonal-laws/`).

## Diagonal laws (three arrivals, 2026-09-03; merged and folded 2026-09-05)

Three independently written articles on one question arrived together on
2026-09-03 and were filed here as separate members
(`thue_morse_diagonal_polynomials/`, `thue_morse_diagonal_polynomials-2/`,
`thue_morse_diagonal_polynomials_article_and_code/`).  On 2026-09-05 they
were merged editorially into one companion volume,
`Thue_Morse_Diagonal_Laws/` (64 pp), and later the same day that companion
was folded into the atlas as **Part III**, its prefix chapter replaced by
references to Part I's exact-prefix, iterated-prefix, terminal-zero-run and
signed-reversal theorems, and its notation moved onto the repository's
notation catalogue (`ThueMorseSign`, `BinaryDigitSum`, `TwoAdicValuation`,
`Floor`/`Ceiling`, `RisingFactorial`, `UnsignedStirlingFirstKind`,
`CoefficientExtraction`, the number-system commands, `RvachevUp` and
`FabiusBounded`; Part I's `S^{(k)}_n` for the iterated prefix; two declared
local hats for the Sheffer normalizations).  The catalogue gained entries
for the iterated prefixes, the summation table `s_{n,k}`, the diagonal
polynomials `D_r` and the dyadic block polynomials `Q_h`, with the Lean
crosswalk of the approximation side.  The shared object is the table built
from the signed Thue–Morse prefix row by `s_{n,k} = Σ_{j<k} (k−j)
s_{n−1,j}`; Part III proves `s_{n,k} = S^{(2n+1)}_{k−n−1}`, the polynomial
on every diagonal from `Σ_r D_r(x) z^r = E(z²)/(1−z)^{2x}`, the Riordan-array
structure and a general subdiagonal theorem, the Sheffer half-step, 2-adic
ruler/Bell, translation, differential and addition laws and the diagonal
Mahler equation, the primitive normalization with the exact common
denominator and the rational-root restriction to `½ℤ`, the complete
nonnegative half-integer zero criterion, the negative half-lattice formula
and an infinite family of negative integer roots, the complete finite-block
theorem for every summation order and its row specialization, the exact
identification of the row blocks with the Lean approximation polynomials
`p_{2n}` whose corrected samples converge to `up` and to the Fabius function
(cited by declaration name), and exact algorithms including an
`O(n² log r)` prefix-moment evaluator.  The three verification programs and
generated data are unchanged under `Thue_Morse_Atlas_and_Frontiers/assets/diagonal-laws/`.
The three arrival directories and the companion directory are deleted; Git
history retains them.  No Lean proof was added; Part III's closing section
lists the formalization targets.

Parts I and II carry extensive inline Lean crosswalks, and Part III cites the prefix and approximation modules by declaration name. As of 2026-08-28,
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

## Frontier-deductions companion volume (2026-09-04/05)

Six independently written Thue–Morse articles arrived on 2026-09-04 and were
filed here as separate members.  They were then merged editorially into one
companion volume, filed beside the atlas rather than folded into it because
the atlas is under concurrent editing:

- [`Thue_Morse_Frontier_Deductions/`](Thue_Morse_Frontier_Deductions/) —
  *Thue–Morse Frontier Deductions: Boundary Corrections, Dyadic Completion
  and Mellin Renormalization, Rational Resonances, Spline and Lattice
  Corrections, and Nonlinear Prouhet Geometry* (199 pp A4; 9,800 source
  lines; a common preliminaries chapter, five parts with 67 chapters, nine
  appendices).  Part I: the signed Stern boundary term of finite diffraction,
  its positive two-level cancellation, the distributional first correction
  with sharp Sobolev thresholds, the analytic defect through two-colored
  binary partitions, the amplitude family, and the finite boundary functional
  for correlations of every order.  Part II: the completion `K = PΦ` with
  `K(2t) = K(t)/t`, its entire Mellin transform and nonconstant periodic
  factor, horizontal strings of nonreal Dirichlet zeros, the all-orders
  scaling law with an explicit tube constant, signed remainders at the
  half-shift, lognormal twins, the classification of completely monotone
  dyadic solutions, beyond-all-orders nonuniqueness, and the boundary-slope
  characterization of the gamma tower.  Part III: rational-frequency
  profiles, twisted moments, the Gaussian–Fabius coalescing-root hierarchy,
  the cyclotomic aggregation identity `∏ H_{ζ^a} = U(qz)/U(z)`, and the
  regularity classification of digit laws.  Part IV: global all-orders spline
  corrections with exact constants, exact dyadic stabilization and Richardson
  reconstruction, the lattice-to-spline conversion and local-limit
  expansion, and the energy-moment twins.  Part V: the covering-family
  identity with hafnians and matching polynomials, and the flat product
  `Φ_q(z)` with its Lambert-W saddle expansion and Woods–Robbins boundary
  layer.  The six verification programs are retained unchanged under its
  `verification/`.

The six arrival directories (`Thue_Morse_Boundary_Corrections/`,
`Thue_Morse_Dyadic_Completion/`, `thue_morse_research_article/`,
`Thue_Morse_Rational_Resonances/`, `Thue_Morse_Research/`,
`Thue_Morse_New_Directions/`) were deleted after a residue audit; Git history
retains them.  The volume answers three questions the atlas leaves open
(the strong spline-correction conjecture of its Part II, the normalization
of the automatic Barnes hierarchy, and Allouche's exhaustion question for the
zeros of `Σ ε_n (n+1)^{-s}`, answered negatively) as consequences of its
proofs; folding those answers and the rest of the volume into the atlas, and
Lean crosswalking, are follow-ups.  The exact-polynomiality-in-`4^-m`
mechanism of Part IV is the same as in the recurrence-free dyadic-value
volume under
[`../inverse-and-sampling/dyadic-up-extraction/`](../inverse-and-sampling/dyadic-up-extraction/);
the two volumes cite each other and are not merged.  None of the volume's
proofs is a Lean verification.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.
