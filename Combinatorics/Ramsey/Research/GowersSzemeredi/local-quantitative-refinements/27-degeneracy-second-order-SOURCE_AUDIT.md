# Source audit

Date of inspection: 6 October 2026.

## Primary paper

W. T. Gowers, *A new proof of Szemeredi's theorem*, Geometric and Functional
Analysis **11** (2001), 465–588. DOI: 10.1007/s00039-001-0332-9.

Public PDF consulted:
https://www.cs.umd.edu/~gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

The original page images were inspected for Lemma 15.4 (printed page 563,
zero-based PDF page 98) and the subsequent exceptional-budget application
(printed page 565, zero-based PDF page 100). The preceding definition and
Walsh lemmas are on printed pages 561–562.

The source has the count `k * 3^(2*d*2^k) * N^((2*d+1)*k+2*d-2)`.
The all-squarefree-moments definition is the one strengthened here. The remark
allowing a weaker definition in the original proof is not transferred to the
new bounds.

## Repository interface

Repository:
https://github.com/VladimirReshetnikov/ProveIt/tree/main/Combinatorics/Ramsey

Inspected file:
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean`

Returned content blob:
`5d91dce37bbca59fc76dfd30ec3a485d72ba583c`

Relevant names include `GeneralArrangement`, `arrangementParityCoefficient`,
`arrangementMoment`, `GeneralArrangement.IsDegenerate`,
`degenerateGeneralArrangementCount`, `lemma_15_4`, and `lemma_15_5`.

The statement file describes proposition-valued definitions. This audit does not
infer current repository-wide formalization status from that fact, and does not
claim any new result in the delivered article has been formalized.

Edited transcription:
`Combinatorics/Ramsey/Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex`

Returned blob: `41085a0efde8c1932e86e80c791984f52841c22e`.

Original PDF blob in that directory:
`db4a37e25a5b7800c925d08f1d38eae9aee8d923`.

The research directory and its local-quantitative-refinements README were
inspected to avoid repeating existing topics. The repository changes rapidly;
these blob identifiers are source snapshots, not an assertion that `main` is
frozen. No repository-wide nonduplication or literature-priority certification
is claimed.

## Background reference

R. P. Stanley, *An introduction to hyperplane arrangements*, in *Geometric
Combinatorics*, IAS/Park City Mathematics Series 13, AMS, 2007, pp. 389–496.
Author's page: https://math.mit.edu/~rstan/arrangements/arr.html

This is cited for the language of intersection posets and finite-field counting.
All hyperplane counting statements needed in the article are proved directly.

## Claim classification

- Classical setup and old bound: attributed to Gowers.
- Hyperplane classification, coefficient-direction counts, rank stratification,
  cubic bounds, and second-order formulas: proofs supplied in the article as
  proposed research contributions, without a priority assertion.
- Exact eight-vertex formula: proof plus finite rational incidence certificate;
  independent finite-field tests corroborate but do not replace that proof.
- Global improvement to Szemeredi's theorem: not claimed.
- Lean verification / independent review: not claimed.
- Further research questions: proposed here; not presented as an inventory of
  previously published open problems.
