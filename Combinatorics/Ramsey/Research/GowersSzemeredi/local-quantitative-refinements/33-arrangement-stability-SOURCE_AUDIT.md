# Source audit and provenance

Date: 2026-10-06. Repository: `VladimirReshetnikov/ProveIt`.

## Pinned crosswalk

Commit: `9f83dbe0f15205c10b1e6efc6af69b09969f8e03`.

The branch metadata returned this commit with timestamp
`2026-10-06T22:37:47Z`. The branch was changing during preparation.
Exploratory reads were not all at this pin; the final crosswalk uses the
following confirmed content identities.

| Path under Combinatorics/Ramsey | Blob SHA | Scope |
|---|---|---|
| Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex | 41085a0efde8c1932e86e80c791984f52841c22e | Corrected arrangement definitions and Section 12/13 interfaces |
| Research/GowersSzemeredi/local-quantitative-refinements/README.md | b0edfc23a3624a09c7a2087a336d447a4378622c | Existing themes, source inventory and status; not a proof input |

The pinned Gowers read at lines 2470--2501 confirms the arrangement
order and respect relation, and the Lemma 12.5 interface. Earlier reads
from the same confirmed Gowers blob covered lines 2360--2470
(Lemmas 12.2--12.4), 2500--2580 (selection and Section 13 opening), and
2610--2740 (the bilinear-piece context). Other exploratory reads examined
approximate-homomorphism material in Section 10.

The public 2001 paper was also read, including the page images at journal
pages 539--540. Journal page 540 (zero-indexed PDF page 75) directly
confirms that a Gowers `d`-arrangement has `2d` vertical edge occurrences
and `4d` point occurrences. Thus the article's `s=16` is exactly a Gowers
8-arrangement, with full cyclic ambient count `N^32`.

The repository's research README was inspected to avoid merely repeating
its main density-transfer, phase-partition, cube-count, transport-rigidity
and moment-amplification themes. This was a scoped review of the
inventory and selected source material, **not** a line-by-line audit of
every pending or integrated manuscript. No exhaustive nonduplication or
literature-priority claim follows from this review.

## Primary literature

W. T. Gowers, *A new proof of Szemeredi's theorem*, GAFA 11 (2001),
465--588, DOI `10.1007/s00039-001-0332-9`. The article's direct supplement
to Lemma 12.3 retains the original power term `theta^7` and adds
`4 theta - 3`; it does not lower the power exponent uniformly.

M. Blum, M. Luby and R. Rubinfeld, *Self-testing/correcting with applications
to numerical problems*, JCSS 47(3) (1993), 549--595,
DOI `10.1016/0022-0000(93)90044-W`. Attribution is to the classical
self-correction paradigm. All constants actually used here are proved
in the manuscript rather than imported as an unchecked citation.

W. T. Gowers and L. Milicevic, *An inverse theorem for Freiman
multi-homomorphisms*, arXiv:2002.11667, v3 (2021). Used for comparison of
scope, not as a theorem input.

L. Milicevic, *An inverse theorem for certain directional Gowers uniformity
norms*, Publications de l'Institut Mathematique 113(127) (2023), 1--56,
DOI `10.2298/PIM2327001M`. The author-maintained publication list confirms
the journal metadata. Used as related context only.

J. Leng, A. Sah and M. Sawhney, *Improved bounds for Szemeredi's theorem*,
arXiv:2402.17995v2 (2024). Used to distinguish a local arrangement result
from the separate global quantitative Szemeredi problem. No claim that
an exhaustive survey of the latest global bounds was performed.

## Claim boundaries

The manuscript's exact cycle-deficit inequality, its moment supplement,
its auxiliary-label correction estimates, the row-gauge decoding theorem,
the local polynomials, the sharp examples, and the erasure result all
have proofs in the TeX. Finite tests support auditing but do not replace
those proofs. General priority, referee approval, and Lean verification
are not certified. The new research questions are explicitly proposed
here and are not all claimed to be previously published open problems.

No third-party paper PDFs or source files are redistributed in this
package. The GitHub repository was read, not modified.
