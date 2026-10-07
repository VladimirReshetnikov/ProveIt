# Source and novelty audit

## Public primary sources

**W. T. Gowers (2001), A new proof of Szemerédi's theorem.** Geometric and Functional Analysis 11, 465–588. DOI 10.1007/s00039-001-0332-9.

- Public paper: https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf
- Inspected: Section 17; page image containing Proposition 17.2, printed page 578.
- Use: motivation and the squared derivative-Fourier-energy phase-removal interface.
- Important distinction: the printed proposition says degree k, whereas its construction and the repository's corrected statement use degree k+1. The present manuscript does not copy the printed degree verbatim.

**Jonathan Tidor (2022), Quantitative bounds for the U4-inverse theorem over low characteristic finite fields.** Discrete Analysis 2022:14, 17 pages. DOI 10.19086/da.38591.

- https://arxiv.org/abs/2109.13108
- Inspected: Definition 3.1, Proposition 3.5, and the support-coefficient integration discussion.
- Use: established nonclassical integration criterion. The Boolean support-indexed primitive is reproved for self-contained use. The underlying integration theorem is not claimed as new.

**James Leng, Ashwin Sah, Mehtaab Sawhney (2024), Improved Bounds for Szemerédi's Theorem.** arXiv:2402.17995.

- https://arxiv.org/abs/2402.17995
- Use: brief context for the separate global quantitative problem. No theorem in the manuscript depends on this paper. The present result is not asserted to improve its global bounds.

## Immediate project baseline

**Source 47: Exact Boolean Obstruction Energies: Derivative periods, sharp quartic–sextic integration, and dimension-free higher-degree extremizers.** Research manuscript prepared with ChatGPT for Vladimir Reshetnikov and ProveIt; dated 6 October 2026.

- Read from the user's Library, TeX name `article(20261007-014512).tex`.
- Library file identifier: `file_00000000d338823088cc20d1261ef1b7`.
- Related PDF: `article(20261007-014511).pdf`.
- Repository audit: `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/47-boolean-energies-SOURCE_AUDIT.md`.
- Prior manuscript's own comparison revision: `5c9a442d263632fdcd4e9690154c12c2dcc70b53`.

The comparison specifically uses the source-47 statements of:

- exact canonical energy `1-(d+1)/2^d` in all degrees;
- universal upper bound `1-min(d+1,7)/2^d`, exact through degree six;
- the remaining degree-seven interval `[120/128,121/128]` and the question whether the answer is `15/16`;
- the pure-defect / codimension-one frozen radical / canonical-class equivalence;
- exact slicing, derivative periods, and the constrained pure-power estimate;
- the reduction for one-dimensional defect images, which is a different invariant from the present contraction rank.

The new article does **not** re-present the already resolved quartic stabilization problem as open. Initial repository inspection exposed that older question, but the later source-47 manuscript was located and used as the actual baseline.

**Source 43: Sharp Boolean Phase Integration from Gowers Derivative Spectra.** Preceding project manuscript, dated 6 October 2026.

- Inspected repository support file: `43-boolean-phase-FORMALIZATION.md`.
- Cubic rank law and the projective shear framework are credited as background via source 43 and their full treatment in source 47.
- The current paper supplies complete proofs rather than assume an unreviewed result without reconstruction.

## Inspected repository interface

Repository: https://github.com/VladimirReshetnikov/ProveIt

The following file was fetched at the known revision:

```text
revision: 0d93c1eac2e20c313e7ed0cb7cb74ff705b00101
path: Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections17_18.lean
blob: 18495f50475835ca1c497d85b0052215f865b8ca
```

The inspected statement `proposition_17_2` assumes prime cyclic modulus, factorial invertibility, and `IsMultilinear sigma`, with a phase of degree at most `k+1`. The separate definition of `IsMultilinear` in `Definitions.lean` was also located: it is a sum over Boolean exponent patterns and includes a constant term, so it is multiaffine, not the homogeneous tensor notion in this manuscript.

The interface pin is not a claim of an atomic repository-wide snapshot. Repository search results changed as the branch advanced. No repository-wide build was performed, and the source-47 comparison revision is distinct from this formal-interface revision.

## New claims relative to those sources

- Counting nonintegrable contractions gives an all-degree induction and closes the source-47 higher-degree gap.
- The all-degree extremal tensor classification, the uniform separation of noncanonical classes, and the flag enumeration follow from that induction and the credited rank-one classification.
- The complete radical is the exact minimal quotient kernel modulo integrable tensors.
- The map from the frozen radical to integrable `(d-2)`-tensors gives the sharp dimension bound, with an explicit equality construction for every degree and rank.
- A prescribed-radical quotient space has the full direct-sum normal form stated in Theorem 7.4.

The elementary gauge, cube, integrability, cubic spectral, rank-one, and canonical results are background. Robust selector margins are direct corollaries; they are not a tensor-learning algorithm.

## Limits of the audit

The search was targeted, not exhaustive. No priority claim against the entire literature is warranted. The two preceding project manuscripts are unrefereed and AI-assisted; repository inclusion does not make them formally verified. This package includes neither their full text nor third-party papers. Its arbitrary-dimensional claims rest on the mathematical proofs in `article.tex`, not on the finite verifier or source attribution alone.
