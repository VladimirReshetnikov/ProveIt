# Source provenance

Research date: 6 October 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `2e0553b0c8a6c9c93221156cc83e95d68ee8bb07`.
The GitHub branch response records this commit at 2026-10-06T20:44:22Z.
The public source was inspected through the GitHub connector. No write action
was performed. The repository was not cloned or compiled for this article.

Inspected files relevant to the paper:

1. Edited paper source:
   https://github.com/VladimirReshetnikov/ProveIt/blob/2e0553b0c8a6c9c93221156cc83e95d68ee8bb07/Combinatorics/Ramsey/Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex
   Blob: `41085a0efde8c1932e86e80c791984f52841c22e`.
   Section 7 was read for the original constants and the repository's
   correction to the proof of Lemma 7.5.

2. Section 6–7 statements:
   https://github.com/VladimirReshetnikov/ProveIt/blob/2e0553b0c8a6c9c93221156cc83e95d68ee8bb07/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections06_07.lean
   Blob: `57b79242466ca9ddf5c36c76b828d7c5557f58ca`.
   In particular, lines 135–235 include Proposition 7.3, the dense-intersection
   interface, Lemma 7.5, and Corollary 7.6.

3. Dependent random choice proof:
   https://github.com/VladimirReshetnikov/ProveIt/blob/2e0553b0c8a6c9c93221156cc83e95d68ee8bb07/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs07DRC.lean
   Blob: `70ed4e09fbe3c32daeed9c9314c79bd36bab2a16`.
   The first 240 lines were read for `Fin 5`, the score, and the sample-counting
   identities relevant to the proposed parameterization.

4. Balog–Szemerédi reduction proof:
   https://github.com/VladimirReshetnikov/ProveIt/blob/2e0553b0c8a6c9c93221156cc83e95d68ee8bb07/Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs07BalogSzemeredi.lean
   Blob: `d9fc2744c223c3ba9368f397f9c91fde1aa5677d`.
   The initial definitions and energy lemmas were read for the popular-sum
   convention and the dependency on `lemma_7_4_holds`.

These are focused source inspections, not a full audit of every file in the
directory. The article does not infer successful compilation from them.

## Primary mathematical sources

- W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588.
  DOI: https://doi.org/10.1007/s00039-001-0332-9
  PDF: https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf
  The original page 503 (PDF page index 38) was visually inspected for the
  statements of Proposition 7.3 and Lemma 7.4.

- Jacob Fox and Benny Sudakov, *Dependent Random Choice*, arXiv:0909.3271v2.
  https://arxiv.org/abs/0909.3271
  General background; the article proves its own selection identities.

- Giorgis Petridis, *New Proofs of Plünnecke-type Estimates for Product Sets
  in Groups*, Combinatorica 32 (2012), 721–733; arXiv:1101.3507v3.
  https://arxiv.org/html/1101.3507v3
  Minimal-growth argument and Plünnecke–Ruzsa inequalities, explicitly
  attributed and proved in the article.

- Christian Reiher and Tomasz Schoen, *Note on the Theorem of Balog,
  Szemerédi, and Gowers*, Combinatorica 44 (2024), 691–698;
  arXiv:2308.10245v2.
  https://arxiv.org/html/2308.10245v2
  Theorem 1.2 supplies the explicitly imported constant
  2^33 epsilon^(-9) K^4. Lemma 2.1 gives a related one-neighbourhood
  score/pruning argument; that method is not claimed as newly invented here.

- James Leng, Ashwin Sah, and Mehtaab Sawhney, *Improved Bounds for
  Szemerédi's Theorem*, arXiv:2402.17995v2.
  https://arxiv.org/html/2402.17995v2
  Used only as a published modern benchmark for global quantitative bounds,
  not as a dependency of the local proofs and not as a claim of current
  best-possible status.

## Original material and attribution

The package contains the newly prepared article and its test program, not
copies of the cited papers or repository source files. Established methods
are attributed. Mathematical derivation of an inequality here does not by
itself establish publication priority for its formulation.
