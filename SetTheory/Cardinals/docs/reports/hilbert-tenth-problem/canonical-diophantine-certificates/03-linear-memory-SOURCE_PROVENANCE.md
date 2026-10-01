# Source provenance and claim status

Inspection date: September 30, 2026.

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: e8bb0931d67f80d9fce87a8cddb0f661ff19f956

The following documents were read through the GitHub connection at that revision:

- README.md (repository map and research context).
- Computability/HilbertTenthProblem/README.md.
- Computability/HilbertTenthProblem/Lean/STATUS.md (relevant beginning/shared
  interfaces and reported pending obligations).
- Computability/CombinatoryLogic/README.md.

Only statements pertinent to Diophantine representations, trace interfaces, and
combinatory operational semantics are used. Repository documentation reports
are not substituted for a fresh kernel audit. No full repository build, complete
source-code audit, or new Lean/Rocq verification was performed.

## Primary literature

The article's bibliography records full citations and stable identifiers:

- Jones and Matiyasevich, register-machine exponential Diophantine representation,
  JSL 49 (1984), DOI 10.2307/2274135.
- Carneiro, A Lean formalization of Matiyasevič's Theorem, arXiv:1802.01795.
- Ben-Sasson, Chiesa, Genkin, Tromer, Virza, SNARKs for C (2013),
  https://eprint.iacr.org/2013/507; extended RAM memory-consistency discussion.
  The PDF's relevant memory-sorting page was inspected as an image as well as
  through its extracted text.
- Batcher, Sorting networks and their applications (1968),
  DOI 10.1145/1468075.1468121.
- Ajtai, Komlós, Szemerédi, An O(n log n) sorting network (1983),
  DOI 10.1145/800061.808726.
- Matiyasevich, Towards finite-fold Diophantine representations (2010),
  DOI 10.1007/s10958-010-0179-4.

Some publisher endpoints restricted direct retrieval; available primary author,
preprint, publisher abstract, and proceedings records were used. The article
proves its new construction directly and labels the externally used AKS theorem.
The source investigation does not establish exhaustive literature coverage or
priority. Failed broad searches were not treated as evidence of novelty.

## Original artifacts in this archive

The two compilers, mathematical exposition, sparse polynomial exports, and
regression tests were produced for this request. The exact test receipts are in
artifacts/. No source-paper PDFs, third-party code, or font files are included.

## Mathematical scope

All witness coordinates are natural numbers including zero. Polynomial
coefficients and subtraction are interpreted over the integers. Allowing
unrestricted integer witnesses changes the comparison and bound semantics.
The single-fold statement is for each fixed finite horizon/log length; the
number of variables grows with that parameter.
