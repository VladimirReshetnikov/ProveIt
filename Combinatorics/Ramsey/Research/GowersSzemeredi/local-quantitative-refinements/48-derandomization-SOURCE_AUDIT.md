# Sources, provenance, and claim boundaries

## Research target

The target is the conditional sampling underlying Gowers's Lemma 9.3 and
an explicit algorithmic question in a prior ProveIt research manuscript.
The contribution is an exact counting/derandomization layer, extended to
uniform prescribed cardinality and arbitrary fixed linear systems.

## Primary mathematical source

W. T. Gowers, *A new proof of Szemeredi's theorem*, Geometric and Functional
Analysis 11 (2001), 465-588; DOI 10.1007/s00039-001-0332-9.
The original PDF was consulted through the University of Maryland mirror:
https://www.cs.umd.edu/~gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf
Printed pages 516-517, covering Lemma 9.3 and its sampling proof, were inspected
visually. The article also records the relevant pages and bibliographic data.

## Prior companion research

*Polynomial-loss restriction in Gowers's Szemeredi argument: Fejer filters,
density-sensitive moments, and finite-field systems*, research note prepared
for the ProveIt project, dated 6 October 2026.
Inspected Library filename: `gowers_polynomial_restriction.tex`.
Its source audit pin is `dca9f06383ccdfc2ed208ccb7c9882214fdb09ac`.

The consulted portions include the kernel and signal estimates, bounded-affine
exceptional tuples, exact generic survival probabilities, the signed
restriction certificate, the weighted polynomial-retention theorem, the
existence/running-time discussion, and further-research item 9 (efficient
certification and extraction).

The Fejer retention bound is credited to this prior companion. The present
article includes a proof of the needed special case and shows that the slack
preserves its constant during rationalization. No additional improvement of
that retention exponent is claimed. This companion is an unrefereed research
manuscript; reading it does not establish formal status or literature priority.
No source manuscript or third-party paper is redistributed in this package.

## Repository comparison

Inspected snapshot: `0b4890a1cd1b5417bcf0724db27e35b77bfa96bc`.
Relevant file:
https://github.com/VladimirReshetnikov/ProveIt/blob/0b4890a1cd1b5417bcf0724db27e35b77bfa96bc/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs09Restriction.lean
Inspected content includes imports, the module description, and the
height-zero arrangement / sixteen-tuple interface. A broader review of the
Ramsey research README and prior Library manuscripts was used to avoid
repeating already developed local topics. It was not an exhaustive
line-by-line audit of the entire repository. No repository mutation or
whole-repository compilation was performed.

## Context and prior art

The method of conditional expectations is classical. Raghavan's JCSS paper
(1988), DOI 10.1016/0022-0000(88)90003-7, is cited for this background; its
primary institutional publication metadata was checked. Its full content is
not represented as having been reviewed for inventory-priority purposes.

The arXiv record of Leng-Sah-Sawhney, *Improved bounds for Szemeredi's theorem*,
2402.17995v2 (29 February 2024), was checked to distinguish modern global bounds
from the local constructive question. The article does not claim a current
best global bound and does not attempt a complete survey.

Targeted literature and prior-file searches did not establish priority for
the precise inventory/response/support-profile package. Accordingly the
article gives proofs and comparisons but does not assert an exhaustive
novelty finding. The construction uses familiar finite generating-function
and conditional-expectation ideas in an explicit algorithmic application.

## Computational and analytic verification

`data/verification_results.json` is produced by the shipped standard-library
suite. Most comparisons are exact rational/integer comparisons to independent
subset enumeration, tuple enumeration, or deterministic convolution. The
trigonometric smoke check alone uses floating point, and is labelled as
supplementary: certification uses rational intervals and the proved remainder
bounds. High-order checks include order eight, but on small finite groups.
These are regression tests, not a proof of the universal theorems.

The PDF was compiled and checked for unresolved references, overfull boxes,
page rendering, and text-boundary violations. See `data/build_validation.json`
for the final measured build details.

## Deliberate limits

- Full Fejer phase search is counted; the fixed-filter rounding cost is not
  advertised as an end-to-end complexity bound.
- Dense ambient storage can be much larger than a sparse input description.
- Uniform fixed-size sampling is not heterogeneous Bernoulli sampling
  conditioned on cardinality.
- Signed rounding does not automatically enforce separate spectral bounds.
- No new Lean theorem, global Szemeredi record, or general polynomial-time
  algorithm in the binary modulus length is claimed.
