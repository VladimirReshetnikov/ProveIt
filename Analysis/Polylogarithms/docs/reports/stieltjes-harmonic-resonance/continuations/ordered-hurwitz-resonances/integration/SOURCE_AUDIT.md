# Source audit and mathematical status

## Snapshot and scope

This continuation uses ProveIt commit
`4c1286161c425eca957b4b9f7cd436c37a4c98f3`, dated 10 October 2026.
Its source anchors are the [canonical polylogarithm manuscript](https://github.com/VladimirReshetnikov/ProveIt/tree/4c1286161c425eca957b4b9f7cd436c37a4c98f3/Analysis/Polylogarithms/docs/manuscript)
and the [incoming reports](https://github.com/VladimirReshetnikov/ProveIt/tree/4c1286161c425eca957b4b9f7cd436c37a4c98f3/docs/incoming)
at that same commit. The accompanying `source_snapshot.json` records the
source inventory.

The survey covered the canonical manuscript and its status records,
together with the seven incoming packages named `Coincident_Stieltjes`,
`Dougall_Resonance`, `Endpoint_Regularization`, `Exact_Identities`,
`Resonance_Coordinate_Transport`, `Resonant_Jets`, and
`Twisted_Stieltjes_Harmonic_Laurent`, all dated 2026-10-10. Mathematical
review concentrated on the ordered Hurwitz germs, their directional
finite parts, coincident Stieltjes products, the relevant resonance
formulas, and the Gaussian conjecture status. This is a targeted audit,
not a re-verification of every theorem in those sources or in ProveIt.

Two precise source questions determine the article's main scope:

- *Resonant Gamma Jets and Directional Zeta Identities*,
  `sections/08-audit-research.tex`, further-research questions Q1 and Q3:
  the ordered depth-three germ with independent exponents, its
  intersecting poles and transverse-ray constants, followed by
  tangential curves and the curve coefficients needed for a finite part.
- *Coincident-Point Stieltjes Calculus*, `article/article.tex`, subsection
  “Cubic coincident moments and higher-depth coordinates”: a specified
  finite part for the digamma cube and an all-index cubic closure.
  That question explicitly allows higher-depth coordinates and does not
  assume linear closure in ordinary Stieltjes constants.

The older suggestion to develop a Dougall family is already addressed
by the incoming Dougall and coordinate-transport reports. This package
does not present a repeated derivation of those results as a new advance.

## Prior-art boundary

**Ordered multiple zeta germs.** Laurent expansions at integer points
are established research. Matsumoto, Onozuka and Wakabayashi treat
Euler–Zagier Laurent coefficients, and Saha's Theorem 2 gives the
canonical ordered decomposition at the all-one point. The article
credits that structure and supplies a tail-defect realization for an
arbitrary positive common Hurwitz shift. Its concrete conclusions for
the present programme are the explicit slope evaluations, the
depth-three directional formula with one named harmonic coefficient,
and the sharp curve-jet theorem. These statements are not accompanied
by a claim that ordered regularization itself was discovered here.

Primary references:
[Saha, Selecta Mathematica 28 (2022), article 6](https://doi.org/10.1007/s00029-021-00719-1),
[author preprint](https://arxiv.org/abs/1902.04389);
[Matsumoto–Onozuka–Wakabayashi, Mathematische Zeitschrift 295 (2020), 623–642](https://doi.org/10.1007/s00209-019-02337-2),
[author preprint](https://arxiv.org/abs/1601.05918).

**Harmonic Stieltjes constants.** The harmonic Hurwitz convention is
compared with that of Kargın, Dil, Cenkci and Can. Their inclusive inner
sum and the strict ordered sum used here differ by one ordinary
Hurwitz-zeta term. The article gives the resulting coefficient
conversion explicitly; it does not identify the two conventions
without that correction. See their
[2023 paper](https://doi.org/10.1016/j.jmaa.2023.127302) and
[author preprint](https://arxiv.org/abs/2304.03517).

**Cubic products and Tornheim functions.** The triple-Hurwitz Fourier
kernel is classical, as is the Crandall/Mellin method based on a product
of polylogarithms. Espinosa–Moll provide direct prior art for the former;
Borwein–Dilcher and Bailey–Borwein develop the latter and related
derivative evaluations. Onodera studies values and first and second
derivatives at nonpositive integers. Consequently the low diagonal
Tornheim jets in the article are recovered identities, not claims of
first evaluation. The contribution here is the complete specified
spatial subtraction, its all-index extension, and the explicit
digamma-cube reduction to one diagonal third derivative.

Primary references:
[Espinosa–Moll, Journal of Number Theory 116 (2006), 200–229](https://doi.org/10.1016/j.jnt.2005.04.008),
[author preprint](https://arxiv.org/abs/math/0505647);
[Borwein–Dilcher, Ramanujan Journal 45 (2018), 413–432](https://doi.org/10.1007/s11139-017-9890-9);
[Bailey–Borwein, Experimental Mathematics 27 (2018), 370–376](https://doi.org/10.1080/10586458.2017.1295687),
[author preprint](https://www.davidhbailey.com/dhbpapers/omega-numerics.pdf);
[Onodera, International Journal of Number Theory 17 (2021), 2327–2360](https://doi.org/10.1142/S1793042121500913).
The Borwein–Dilcher and Onodera priority checks used publisher
abstracts/previews; a complete proof audit of those two papers is not
claimed. Recent work on points of indeterminacy is also acknowledged:
[Sathyanarayana–Sharan (2026)](https://doi.org/10.1016/j.aam.2026.103075),
[author preprint](https://arxiv.org/abs/2510.10093).

This bibliography is a focused comparison with relevant prior work,
not an exhaustive determination of publication priority.

## Exact status of the results

| Source target or extension | Result in this package | Qualification |
|---|---|---|
| Ordered depth-three germ with independent exponents | Explicit polar decomposition, normally convergent remainder, and every transverse directional finite part | The remaining ordering dependence is carried by a named harmonic Stieltjes coefficient; no arithmetic independence is asserted. |
| One initial slope and a common trailing slope, at arbitrary depth | Every nonpositive Laurent coefficient reduces to finitely many ordinary Hurwitz and Stieltjes jets | All prefix slopes must be nonzero. Values on a polar ray are not supplied by substituting into a rational continuation. |
| Tangential analytic curves through the intersection | Exact finite-part formula, pole order equal to the sum of the prefix valuations, and a sharp curve-jet requirement | The required curve-jet order is the sum of those valuations plus their maximum, under the stated nonzero leading-coefficient hypotheses. |
| Cubic coincident Stieltjes products | A holomorphic completion generating every Stieltjes index and every nonnegative integer argument-derivative order | Coefficients are extracted from the completed germ, not from unspecified partial derivatives of singular Tornheim summands. |
| Unit-coordinate digamma cube | Exact reduction to the third derivative at zero of the one-variable continuation of `T(s,s,s)` | Further reduction of this derivative to ordinary constants remains open here. |

## Corrections, review, and remaining questions

**No newly established source erratum is claimed.** No concrete false
claim was confirmed in the source arguments reviewed for this package.
The exact comparison between a directional spectral Laurent constant
and a spatial Hadamard finite part explains a normalization difference;
it is not attributed as an error to a source that was not shown to make
that identification. The strict/inclusive harmonic conversion is
likewise a reconciliation of definitions.

The canonical short `S6` and revised `S8` identities remain conjectural.
Numerical proximity, existing shuffle comparisons, and separators in
restricted formal relation spaces do not prove or disprove those
period equalities. This article changes none of their recorded statuses.
It also makes no claim of a minimal arithmetic basis or of
nonreducibility of the harmonic coefficient or `tau'''(0)`.

The proposed proofs received independent AI review of the analytic
arguments and coefficient algebra. Separate calculations checked
the ordered identities, endpoint terms, and the cubic coefficient.
This is additional internal mathematical review, not external peer
review and not a proof-assistant formalization. The attached exact
finite checks and independent numerical diagnostics support the
proofs; floating-point residuals are neither interval enclosures nor
substitutes for the all-index convergence arguments.

Further work should focus on explicit relations among the remaining
ordered harmonic coefficients, higher positive Laurent jets, arithmetic
reductions of the specified diagonal Tornheim third derivative, and
exact certificates for the unchanged Gaussian conjectures. Those tasks
remain distinct from the finite-part and completion theorems proved here.
