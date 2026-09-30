# Source audit and scope

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit inspected: `e1afd75e35a4de734d5aa47aec5cdb917b82ed3e`.

Principal source:

`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/common_digit_fabius_zonoids_frontier_report/common_digit_fabius_zonoids.tex`

Pinned URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/e1afd75e35a4de734d5aa47aec5cdb917b82ed3e/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/representations/common_digit_fabius_zonoids_frontier_report/common_digit_fabius_zonoids.tex

Title: *Common-Digit Fabius Zonoids: Exact volumes, hyperbolic-secant geometry,
Bernoulli Gaussianization, and parameter jets*. Dated 30 August 2026, with
subsequent editorial notes. The source's author metadata identifies an
AI-generated research report; the GitHub owner is not assumed to be its sole
author.

The repository root README, Fabius README, and the draft manifest were used
for navigation. The principal comparison was against the common-digit
report, not an exhaustive audit of every repository file.

## Relevant baseline and unresolved direction

The report defines the same common-digit geometric-uniform family and
contains its support geometry, joint cumulants, covariance formula, and
hyperbolic Gaussianization. These are not claimed as new here.

Its section “Inverse-Fabius copula endpoint laws,” including the label
`conj:copula-endpoints`, proposes endpoint boundary transseries and suggests
conditional extreme-event laws. The present work studies joint corner
probabilities, their sharp logarithmic asymptotics, and threshold-conditioned
extremes. It does not claim the whole boundary-transseries conjecture is
resolved and does not differentiate probability asymptotics to infer an
unproved density theorem.

The same source contains an editorial correction to a scalar
polynomial-geometric small-ball conjecture. The present manuscript does not
rely on the uncorrected scalar conjecture and does not claim priority for
its scalar specialization.

## Classical external references

1. J. Fabius, “A probabilistic example of a nowhere analytic C-infinity
   function,” Z. Wahrscheinlichkeitstheorie verw. Gebiete 5 (1966), 173–174.
   DOI: 10.1007/BF00536652. CWI precursor: https://ir.cwi.nl/pub/8160
2. J. Arias de Reyna, “An infinitely differentiable function with compact
   support: Definition and properties,” arXiv:1702.05442.
   https://arxiv.org/abs/1702.05442
3. A. Prékopa, “On logarithmic concave measures and functions,” Acta Sci.
   Math. (Szeged) 34 (1973), 335–343.
   https://acta.bibl.u-szeged.hu/14411/
4. A. W. Ledford and J. A. Tawn, “Statistics for near independence in
   multivariate extreme values,” Biometrika 83 (1996), 169–187.
   DOI: 10.1093/biomet/83.1.169.
5. P. Tankov, “Tails of weakly dependent random vectors,” J. Multivariate
   Anal. 145 (2016), 73–86. DOI: 10.1016/j.jmva.2015.12.008.
   https://arxiv.org/abs/1402.4683

These references were checked for appropriate attribution. The paper does
not claim that a focused source search rules out every earlier equivalent
result in weighted small deviations, random series, or extreme-value theory.

## Contribution and trust boundary

The envelope rate, independent-simplex correction, copula cancellation,
power-ray regular-variation proof, continuum exponent, optimal mesh, and
noncommuting-limit deduction are developed in this manuscript. Classical
ingredients are explicitly acknowledged. Mathematical correctness is
supported by the written proofs; this is not a claim of peer review or a
proof-assistant certificate.

`verify.py` uses exact Fraction arithmetic for its finite envelope and
probability-certificate assertions. Its large-parameter tables and decimal
logarithms are ordinary floating-point evaluations, not outward-rounded
interval bounds. All limit theorems require the proofs in the manuscript.
