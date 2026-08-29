# Corpus audit and provenance boundary

## Pinned snapshot

The report's repository audit is pinned to:

- repository: `VladimirReshetnikov/ProveIt`
- commit: `cc0be20ab445b3f284cb884ebc3c1fc0cd6c54f4`
- date: 28 August 2026
- scope: every `*.tex` below `Analysis/FabiusFunction/docs`, recursively
- inventory at that snapshot: 67 TeX documents

The source chapter and attached draft were audited locally as:

- `rvachev.tex` / `rvachev.pdf` — the Russian Chapter 3 source and surviving
  printed pages;
- `Atomic_Functions_Rvachev_Report.tex` — the attached earlier English report,
  treated as historical input rather than automatically novel material.

## Corpus layers

The recursive audit separated the following layers so that duplicate copies
were not mistaken for independent corroboration:

1. living primary exposition, glossary, non-elementarity article, and Lean
   walkthrough;
2. the canonical frontier volume and living thematic frontier reports;
3. the separately retained Fourier-decay comparison corpus;
4. vendored paper sources;
5. frozen archive copies and superseded drafts, interpreted through the
   repository's provenance and consolidation manifests.

The living corpus at the pinned snapshot already contains the material of the
attached earlier report, notably its general-base atomic densities, Cantor-gap
geometry, derivative equimeasurability and norm formulas, local-degree law,
and `Fup_n` central-limit program.  The final report therefore labels those
results as inherited/current-corpus results instead of presenting them as new.

## Nonduplication procedure

Candidate new results were checked by title-, formula-, and keyword-level
search against the recursive TeX inventory, followed by targeted comparison
with the closest current reports.  In particular, searches were made for the
characteristic q-Gaussian derivative Gram kernel and determinant, Jacobi-theta
Riesz bounds for the derivative tower, the distribution and heavy tail of the
leading local gap jet, and a proved differentiated all-orders Edgeworth
expansion for the `Fup_n` hierarchy.

No equivalent statements were located in the pinned corpus.  This establishes
only corpus-relative nonduplication.  It does not establish worldwide
historical priority; the report states that limitation explicitly.

## Translation policy

The Russian OCR is reliable in much of the prose but damaged in several
superscripts, factorials, summation indices, and binary subscripts.  The report
uses the printed PDF where it resolves the OCR, reconstructs invariant formulas
from adjacent equations when that is mathematically forced, and records
remaining ambiguities instead of inventing exact strings.  Source equation
numbers are retained in a crosswalk appendix.

## Numerical boundary

Numerics are evidence and diagnostics, not substitutes for proofs.  The Python
script checks:

- the `h_3` fixed-point equation and central plateau;
- the exact geometric local-degree distribution;
- q-Gaussian Gram determinant and pivot identities through order 40;
- Jacobi-theta spectral bounds;
- successive `Fup_n` Edgeworth errors and their predicted orders.

Every random calculation uses a fixed seed; density inversions are
deterministic FFT computations.  Exact identities used as theorems are proved
in the LaTeX report independently of the numerical checks.
