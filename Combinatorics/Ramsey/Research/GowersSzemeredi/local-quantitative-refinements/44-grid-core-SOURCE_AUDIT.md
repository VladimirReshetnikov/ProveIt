# Source and claim audit

## Inspected repository

Repository: VladimirReshetnikov/ProveIt.
Scope: Combinatorics/Ramsey.
Pinned commit: `8c12c906e4ab5a00001a65de3c882f935a15661a`.
The GitHub response reports UTC commit time `2026-10-07T00:11:50Z`; the
manuscript follows the session's 6 October 2026 date. These refer to the
same source inspection across the UTC/local date boundary.

Relevant source:
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean`.
Inspected Git blob: `5d91dce37bbca59fc76dfd30ec3a485d72ba583c`.
The exact fields used are `arrangementMoment`,
`GeneralArrangement.IsDegenerate`, `degenerateGeneralArrangementCount`, and
the proposition statements for Lemmas 15.4 and 15.5.

The interface was read through the connected GitHub tool. It excludes modular
scalar multiples of the intrinsic parity array and includes every coordinate
monomial. The current manuscript preserves both conventions. A proposition
in a source file is not evidence that this manuscript's new claims have been
formalized.

Gowers transcription inspected:
`Combinatorics/Ramsey/Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex`,
blob `41085a0efde8c1932e86e80c791984f52841c22e`.
The primary published pages 562–563 were also visually inspected in the
public paper PDF.

## Earlier research read from the user's Library

### Baseline A

*The Codimension-One Degeneracies of Gowers Arrangements: An asymptotically
sharp replacement for Lemma 15.4 and explicit random-selection thresholds*.
AI-assisted research manuscript prepared for Vladimir Reshetnikov, 6 October
2026. Library TeX entry: `arrangement_degeneracy.tex`.

Library file identifier:
`file_000000008b60823099765e87960f5ee1`.

Already present: first-order hyperplane classification, exact H_d, single
non-parity witness bounds, and questions about the second coefficient.

### Baseline B

*Sharp Degeneracy Bounds for Gowers Arrangements: Hyperplane obstructions,
second-order structure, and an exact finite-field count*.
AI-assisted draft prepared for Vladimir Reshetnikov and ProveIt, 6 October 2026.
Library TeX: `article(20261006-231449).tex`.
Corresponding PDF: `article(20261006-231446).pdf`.
Library TeX identifier: `file_00000000278c81f6ae3ca8cb70673f86`.

Already present: all-characteristic direction inventories, the core
classification with a dimension-dependent large-characteristic cutoff,
pairwise core-intersection bounds, a cubic non-core remainder, the second
coefficient expressed in terms of b2(d,p), the explicit d=2 coefficient,
and an exact eight-vertex specialization.

Explicit questions answered here:
1. Find a closed form, recurrence, or efficient exact algorithm for b2(d,p)
   in the stable large-characteristic regime, especially d=8.
2. Classify core profiles in intermediate characteristics
   5 <= p <= 2*k+2 and determine the sharp threshold for the existing family.

The new article does not reclaim the earlier core count or d=2 coefficient
as new. The main distinct contributions are the fixed-grid algorithm, the
exact core products, removal of the intermediate-characteristic restriction,
uniform rank-two incidence cutoff, d=8 evaluation, and deficit asymptotic.

These Library drafts are named and cited in the article but not republished
in the archive. Their Library filenames do not establish public repository
paths, and no such paths are invented.

## Primary external sources

W. T. Gowers, *A new proof of Szemeredi's theorem*, GAFA 11 (2001), 465–588.
DOI: 10.1007/s00039-001-0332-9.
Public copy:
https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf
Target: Section 15, particularly the degeneracy definition and Lemma 15.4.

C. A. Athanasiadis, *Characteristic polynomials of subspace arrangements and
finite fields*, Advances in Mathematics 122 (1996), 193–233.
Publisher: https://www.sciencedirect.com/science/article/pii/S0001870896900596
Used for attribution of the classical finite-field viewpoint, not as an
unproved input for the new grid theorem.

R. P. Stanley, *An introduction to hyperplane arrangements*, in Geometric
Combinatorics, IAS/Park City Math. Ser. 13, AMS (2007), 389–496.
Author's page: https://math.mit.edu/~rstan/arrangements/arr.html
Classical background and terminology; the required identities are proved.

H. Kamiya, A. Takemura, H. Terao, *The characteristic quasi-polynomials of the
arrangements of root systems and mid-hyperplane arrangements*, Progress in
Mathematics 283 (2010), 177–190.
https://arxiv.org/abs/0707.1381
Related modular-arrangement context. No identification of its characteristic
polynomials with this balanced arrangement is asserted.

## Proof and computational boundaries

The all-d grid theorem is a weighted double count, not numerical
interpolation. The eight-shape compression has a complete finite rational
coefficient check over all 512 grid supports. Exact walk recurrences give
the d=8 value. Independent normal-pair checks were executed for d=2,3,4.
No full enumeration of all arrangements was run. No Lean build was run.
No source or formalization ledger was modified. The package establishes
local research claims; neither global Ramsey-bound propagation nor
historical-priority certification is supplied.
