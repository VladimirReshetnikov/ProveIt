# Source and priority audit

## Gowers's paper: the precise target

W. T. Gowers, *A new proof of Szemerédi's theorem*, Geometric and Functional
Analysis 11 (2001), 465--588.

DOI: https://doi.org/10.1007/s00039-001-0332-9
Publisher record: https://link.springer.com/article/10.1007/s00039-001-0332-9

The bibliography and publication details were checked against the publisher
record. The mathematical passage used here was read in the repository's edited
transcription:

https://github.com/VladimirReshetnikov/ProveIt/blob/main/Combinatorics/Ramsey/Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex

Observed blob: `41085a0efde8c1932e86e80c791984f52841c22e`.
Content-addressed API resource:
https://api.github.com/repos/VladimirReshetnikov/ProveIt/git/blobs/41085a0efde8c1932e86e80c791984f52841c22e

Relevant range: the energy paragraph immediately before Theorem 7.2 and the
following statements of Theorem 7.2 and Proposition 7.3 (observed source lines
1160--1245). Gowers states the maximum M_m and its arithmetic-progression equality
case. The present all-defect theorem refines that endpoint, not the full general
hypothesis of the Balog--Szemerédi extraction.

## Prior ProveIt energy material

The local-refinements README was inspected to identify overlap with earlier
reports:

https://github.com/VladimirReshetnikov/ProveIt/blob/main/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md

Observed blob: `1ec635141ba5b9fb2ceff2a4a1ac59107de9587b`.

The following source-45 energy proof review was read in full:

https://github.com/VladimirReshetnikov/ProveIt/blob/main/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/45-rigidity-gaps-review_energy.md

Observed blob: `7984f49e51f4cfb0e9cd44f8385b5302bc75242f`.
Content-addressed API resource:
https://api.github.com/repos/VladimirReshetnikov/ProveIt/git/blobs/7984f49e51f4cfb0e9cd44f8385b5302bc75242f

This document already records:

- the endpoint energy recurrence and ordered triple defect identity;
- the first gap D(A) >= m-2 for non-progressions;
- the complete second-level classification for m >= 5;
- the unit-Schur-defect lemma for n >= 4;
- the third-level lower bound D(A) >= 2m-6 outside the earlier classes;
- a sharpness construction and a torsion-free transfer argument;
- the published inverse-Pollard provenance of the first gap.

It does not supply the all-r partition classification or the complete third-
and fourth-level equality proofs developed here. This comparison is to the
materials actually inspected, not a claim to have searched every file, every
historical revision, or every external paper. The prior review is itself an
internal AI proof check, not a human referee report or a formal verification.
The present manuscript reproves the background, so none of the main arguments
imports the correctness of that review as an axiom.

The repository was changing during inspection. The content identifiers above
are the audit anchors; no uniform snapshot of the whole repository is claimed.

## Published inverse Pollard theory

E. Nazarewicz, M. O'Brien, M. O'Neill, C. Staples,
*Equality in Pollard's theorem on set addition of congruence classes*,
Acta Arithmetica 127 (2007), no. 1, 1--15.

Primary publisher PDF:
https://www.impan.pl/shop/en/publication/transaction/download/product/82135

Theorem 3 on printed page 2 was read and visually checked in the PDF. Its
four alternatives include the size-(t+1) case, which must not be confused with
an unrestricted exception for (A,-A). The first-gap implication is explained
in Appendix A of the new manuscript. It uses no claim of novelty for that gap.
The PDF parser loses some complement bars elsewhere in the paper; the new
article does not rely on those garbled formulas.

## Publication priority and the limits of the search

Searches for additive-energy extremal levels and near-maximal Schur-triple
structure did not identify a primary source establishing the exact all-defect
normal form or the complete third-/fourth-level statements in this manuscript.
The results included substantial irrelevant material, and this was not a
comprehensive literature review. Thus:

- all central results are supported by their written proofs;
- additions are identified relative to the inspected repository materials;
- publication priority is expressly unestablished;
- no claim to solve a named longstanding external open problem is made;
- no new global numerical Ramsey or Szemerédi bound is claimed.

The final ZIP contains only the newly written manuscript and its supporting
files, not copies of third-party papers or repository manuscripts.
