# Source and status audit

Checked on 20 September 2026. Mathematical claims in the article are proved
there unless explicitly attributed as previously known. This file records
the sources used to select and identify the problem; it is not a claim of
an exhaustive literature search.

## 1. Primary conjecture and suggested witness

Bishal Deb and Alan D. Sokal,
*Higher-order Stirling cycle and subset triangles: Total positivity,
continued fractions and real-rootedness*, arXiv:2507.18959v1 (2025).

- Versioned record: https://arxiv.org/abs/2507.18959v1
- HTML: https://arxiv.org/html/2507.18959v1
- PDF: https://arxiv.org/pdf/2507.18959v1
- Identifier: https://doi.org/10.48550/arXiv.2507.18959

The fetched arXiv record listed v1, submitted 25 July 2025. Conjecture
1.4(d) appears on printed page 10 (zero-based PDF page 9). It asserts the
r=1,2 positive cases and the r>=3 failure for the subset row polynomials.
The following discussion expressly identifies the positive cases as known.
Appendix C, printed page 50 (zero-based PDF page 49), proposes the same
shift-one 3-by-3 determinant used in the short certificate here. Both pages
were inspected as rendered PDF images as well as parsed text, to check the
indices, quantifiers, and distinction from part (c).

The attribution in the article is intentionally narrow: we supply a
uniform leading-coefficient formula, a proof of its sign, and an all-shifts
extension. We do not claim the candidate minor was previously unknown.

## 2. Previously known Ward case

Andrew Elvey Price and Alan D. Sokal,
*Phylogenetic trees, augmented perfect matchings, and a Thron-type continued
fraction (T-fraction) for the Ward polynomials*, Electronic Journal of
Combinatorics 27(4), P4.6 (2020).

- Journal: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v27i4p6
- DOI: https://doi.org/10.37236/9571
- Preprint: https://arxiv.org/abs/2001.01468v2

The journal and arXiv records were checked for authors, title, bibliographic
information, and the continued-fraction result. The direct statement that
this yields the needed r=2 coefficientwise Hankel positivity is recorded
by Deb and Sokal on page 10. No new proof of that positive result is asserted.

## 3. Supplied manifest

`inputs/manifest.tex`, supplied by the user, dated 20 September 2026.
The entry “A sharp order-five threshold for higher-order Stirling subset
log-concavity” concerns part (c) of Conjecture 1.4. The present article
instead concerns part (d). The manifest explicitly describes its entries
as AI-assisted, unrefereed research claims whose proofs were not audited
when compiling the catalogue. No stronger evidential status is assumed.

## 4. Search scope and limitation

Targeted searches included the paper identifier with `1.4(d)`, the title
with `Hankel`, `proof`, and `conjecture`, and searches for the proposed
factorization and higher-order Stirling subset Hankel negative coefficients.
The results inspected did not provide an intervening proof of the uniform
negative assertion or the all-shifts theorem. The primary version remained
a conjectural source for the targeted range.

This supports the choice of a published conjectural target, but it does
not exclude unindexed work, private communications, or a proof embedded in
material not returned by the searches. No secondary problem database is
used as proof of openness or correctness. No third-party article PDFs are
redistributed in this package.
