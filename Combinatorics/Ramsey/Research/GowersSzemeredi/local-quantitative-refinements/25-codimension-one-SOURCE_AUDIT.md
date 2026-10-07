# Source audit and research boundaries

Audit date: 6 October 2026. This file separates inspected source material from
results developed in this manuscript. No repository write was performed.

## 1. Primary mathematical source

W. T. Gowers, *A new proof of Szemerédi's theorem*, Geometric and Functional
Analysis **11** (2001), 465–588.

Public PDF consulted:
https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

The PDF's printed pages 562–565 (zero-based PDF pages 97–100) were inspected,
including page images. Relevant passages are:

- The full ternary coefficient definition of a degenerate arrangement and its
  distinguished signed parity relation.
- Lemma 15.3: the sharp fibre estimate for a nonconstant multilinear polynomial.
- Lemma 15.4: at most `k * 3^(2d*2^k) * N^((2d+1)k+2d-2)` degenerate arrangements.
- The observation following Lemma 15.4 that the counting proof could discard
  some final-coordinate monomials. The present proof retains those equations.
- Lemma 15.5: the random Riesz-product selection mechanism and the survival
  advantage `1 + 2^(1-n)`, with n the number of labels.

The manuscript does not claim to improve Lemma 15.3 for an arbitrary isolated
multilinear polynomial; that bound can be sharp. Its improvement uses the full
simultaneous arrangement moment system.

## 2. Pinned ProveIt formal interface

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit:
`568d1802e99404c0710be33cceb401d25211f445`

File:
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean`

Blob:
`5d91dce37bbca59fc76dfd30ec3a485d72ba583c`

Permalink:
https://github.com/VladimirReshetnikov/ProveIt/blob/568d1802e99404c0710be33cceb401d25211f445/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean

Read via the GitHub connector, including the definitions and statements around
source lines 295–400 and 400 onward. The decisive interfaces were:

- `IsTernaryCoefficient`, `IsModularMultiple`;
- `arrangementParityCoefficient`, `arrangementMoment`;
- `GeneralArrangement.IsDegenerate`, `degenerateGeneralArrangementCount`;
- `lemma_15_4`, `lemma_15_5`, `arrangementSelectionExponent`.

The manuscript preserves the **modular scalar multiple** exclusion and **all**
coordinate monomial moments, including the empty monomial. The affine
Boolean-to-centred-sign change is invertible in odd characteristic and preserves
labelled parameter counts. The finite-field extension is proved in the
manuscript; the inspected formal interface itself uses `ZMod N`.

The existing Lemma 15.4 permits d=1, whereas the new codimension-two argument
requires d>=2. The article explicitly gives the d=1 obstruction. The new exact
hyperplane count also needs characteristic>2d. Do not substitute the new theorem
for the old one without retaining these assumptions.

## 3. Existing research scope

The README at the following location was inspected on `main`:
https://github.com/VladimirReshetnikov/ProveIt/blob/main/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md

It described prior density-extraction, phase-partition, energy, restriction,
cube-counting, and floor-pattern refinements. The present project focuses on
Section 15 degeneracy geometry and exact selection parameters. This scope audit
is not an assertion that every manuscript or pending intake file was fully read.
The README was not used as a mathematical premise for any theorem here.

## 4. Background reference

C. A. Athanasiadis, *Characteristic polynomials of subspace arrangements and finite
fields*, Advances in Mathematics **122** (1996), 193–233.
https://www.sciencedirect.com/science/article/pii/S0001870896900596

This is cited only as classical background for the proposed further work on the
intersection lattice and characteristic polynomial. The main arguments here
are self-contained and do not depend on a result from that paper.

## 5. What this manuscript develops

- Minimal-Walsh-layer pivot rank `k-s` for simultaneous moment equations.
- The sharp non-parity single-witness probability
  `q^-2 + (q-1)*q^(-2d)` at fixed nonzero sides.
- The exact parity hyperplane count
  `(T_(2d) - 2*binomial(2d,d) + 1)/2`, after the full affine quotient, not merely
  identification of opposite coefficient patterns.
- Classification of all codimension-one components, and explicit two-sided
  first-order asymptotics for the complete degeneracy count.
- A genuine second-order residual witness outside every listed hyperplane.
- Explicit finite-field, arbitrary-d arrangement selection, including correct
  treatment of repeated labelled vertices.

No claim of established literature priority, independent review, or formal
verification is made. No new global quantitative Szemerédi bound is asserted.

## 6. Computation boundaries

`code/verify.py` uses exact integer, rational, and prime-field arithmetic.
The small-witness tests enumerate all non-parity sign classes at k=1,d=2,
not all arrangements: the spatial-base counts are obtained by exact ranks.
Seeded tests of identities and pivot ranks supplement the general proofs.
The selection process is not simulated. No Lean toolchain is run.

`code/compare_cutoffs.py` evaluates proven sufficient thresholds and prints
approximate base-10 logarithms for the article's table. Those rounded decimal
values are illustrations and are not used to prove any theorem.

The PDF was compiled locally, checked for unresolved references and overfull
boxes, and visually inspected after rendering all pages.
