# Source audit and comparison baseline

Inspection date: 6 October 2026.

## Repository reference

Repository: `VladimirReshetnikov/ProveIt`.
Observed `refs/heads/main` commit:

`327773149bd272239f1f6c0015f76d5097512c88`

The partition module was explicitly fetched at that commit. Other compared
content is identified below by the exact blob hashes returned by the connector;
no assertion is made that every separate read was an atomic snapshot of `main`.
The moving branch is not treated as a permanent content identifier.

## Compared files

### Edited paper transcription

Path:
`Combinatorics/Ramsey/Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex`

Returned blob:
`41085a0efde8c1932e86e80c791984f52841c22e`

Relevant inspected ranges: lines 1–200 and 210–325, especially the edited
Lemma 2.3 and Corollaries 2.4–2.5. The latter range includes editorial comments
explaining finite rounding corrections and the strengthened weighted-averaging
argument in the proof of Corollary 2.5.

Source directory:
https://github.com/VladimirReshetnikov/ProveIt/tree/main/Combinatorics/Ramsey/Papers/sz-thm-gowers-proof

The directory also listed a PDF with blob
`db4a37e25a5b7800c925d08f1d38eae9aee8d923`.
That PDF's bytes are not redistributed in this package. Comparison of the
edited local statements uses the inspected TeX, not an assumed identity with
the historical printed paper.

### Partition construction

Path:
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs02Partition.lean`

Returned blob:
`291b1494ab5af839456dcac35f4bb447d4c90844`

The commit-pinned read included lines 580–780, covering the rounding and
residue-chunk construction used by the corrected Lemma 2.3. It exposes the
mechanism of blocks with lengths at least L and less than 2L.

https://github.com/VladimirReshetnikov/ProveIt/blob/327773149bd272239f1f6c0015f76d5097512c88/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs02Partition.lean

### Density-increment proof

Path:
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs02DensityIncrement.lean`

Returned blob:
`85b5c3ad8769b9769e1939ae5c05f0757f0678b5`

Relevant inspected ranges: lines 1–150 and 360–560. These include the balanced
function, bounds for nonzero Fourier coefficients by both the set and its
complement, the large-scale proof, and the final exported theorem.
The proof obtains alpha/4 and the stronger length before weakening its
conclusion. This is explicitly acknowledged in the article's comparison.

https://github.com/VladimirReshetnikov/ProveIt/blob/main/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs02DensityIncrement.lean

### Phase-partition interface

The directory listing identified `Proofs02PhasePartition.lean`; the density
file imports it and invokes `corollary_2_4_holds`. This establishes the relevant
interface. The report does not claim a complete audit of that file or of the
entire Gowers formalization.

## Quantitative comparisons

All Fourier magnitudes below use the same parameter alpha; the repository's
unnormalized hypothesis is `|Fourier(A)(r)| >= alpha*N`.

1. Corrected Lemma 2.3 has minimum length `sqrt(rs/M)/4`, maximum
   `sqrt(rs/M)`, and image diameter at most s. The article improves the
   minimum to `sqrt(rs/M)/3` with the same other conditions, and proves the
   universal coefficient is optimal.
2. Corrected Corollary 2.4 has minimum `sqrt(alpha*r/(128*pi))`, maximum
   `sqrt(alpha*r/(4*pi))`, and retained absolute block correlation
   `alpha*r/2`. The article replaces the first denominator by `36*pi` and
   the last factor by `3*alpha/4`, leaving the maximum unchanged.
3. Exported Corollary 2.5 has minimum `sqrt(alpha^3*N/(128*pi))` and increment
   `alpha/8`. The inspected large-scale proof already yields
   `sqrt(alpha*N/(128*pi))` and `alpha/4`. The article improves beyond this
   stronger proof-level baseline; it does not claim the already-existing
   improvement as new work.

These comparisons refer to the specified local statements, not to a complete
search for overlapping material elsewhere in ProveIt.

## External primary literature

W. T. Gowers, *A new proof of Szemeredi's theorem*, Geometric and Functional
Analysis 11 (2001), 465–588.

James Leng, Ashwin Sah, and Mehtaab Sawhney, *Improved Bounds for Szemeredi's
Theorem*, arXiv:2402.17995v2, 29 February 2024:
https://arxiv.org/abs/2402.17995

The arXiv record, paper text, and relevant rendered PDF pages were inspected.
The article uses this paper for context and to avoid suggesting that an
improvement over the 2001 headline bound would automatically be a new global
record. Its quantitative theorem is not an ingredient in the proofs here.
The comparison is not an exhaustive literature-priority or current-ranking
survey.

## Validation levels

- **Mathematical results:** complete ordinary proofs are supplied in the
  article, including explicit finite hypotheses, integer rounding, the
  capped-constant obstruction, the algebraic simultaneous-approximation
  obstruction, and the nonorthogonal Gram correction.
- **Exact computational checks:** rational/integer finite constructions,
  coverage, properness, common differences, lengths, circular widths, and
  tolerance allocation.
- **Numerical diagnostics:** 80-digit Fourier correlation and spectral
  inequalities. Conservative rational widths are used in the constructions,
  but the transcendental input is not certified by interval arithmetic.
- **Lean:** no new compilation or kernel verification, and no complete
  repository audit. The integration plan is a roadmap, not a checked patch.
- **Novelty:** proved local strengthenings and local optimality statements;
  historical priority and a new global Szemeredi bound are not asserted.

Only the generated article, its source, original companion code, test outputs,
and audit documentation are included. No third-party paper, repository source,
or font file is bundled.
