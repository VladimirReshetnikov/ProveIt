# Source and research provenance

Prepared on 7 October 2026 in response to Vladimir Reshetnikov's request for
serious research connecting `openai/math` and `VladimirReshetnikov/ProveIt`.
The article, proofs, exact witness and verifier were developed in this session.
No human coauthor or independent referee has been asserted.

## Inspected repository snapshots

### openai/math

Head inspected:

```text
adc7f1241b42e322a6451854ab7e4b4c146bf78a
```

Selected sources:

- `overview.tex`, especially catalogue entries 159, 160 and 170.
- `preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/README.md`.
- The same preprint's `build/main.tex` and `build/sections/00-introduction.tex`.

Pinned source root:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a

The global arithmetic-progression statement is reported as that manuscript's
claim. This package does not independently verify it and does not use it as a
hypothesis or lemma.

### VladimirReshetnikov/ProveIt

Head inspected:

```text
f0ac99f2a3690e12852abb19d1ccc167a02aaf31
```

Selected source:

```text
Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md
```

Pinned source root:
https://github.com/VladimirReshetnikov/ProveIt/tree/f0ac99f2a3690e12852abb19d1ccc167a02aaf31

The research compilation is not treated as evidence that all its statements
have been formally proved. No repository write or status change was performed.
The review is focused; it is not an audit of every result in either repository.

## Direct predecessor in project-associated materials

File: `finite_cover_phase_repair.tex`, dated 7 October 2026.

Title: *Finite-cover polarization and optimal repair of multilinear phase
obstructions: Lossless subgroup comparison and the first low-characteristic
obstruction in Gowers's phase-removal step.*

Its author line is “Research manuscript prepared for the ProveIt project.”
The manuscript was retrieved from the user's Library. It was not assumed to
have a public repository path. Its Conjecture 11.4 is the precise problem
resolved here; Questions 14.1 and 14.4 motivate the positivity certificate
and stability discussion. Its exact cube census and its former bound are
independently reconstructed by the new verifier.

The new package preserves attribution for the prior structural reductions.
It does not bundle or silently edit the predecessor.

## Established mathematical sources

- W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588;
  DOI 10.1007/s00039-001-0332-9.
- Jonathan Tidor, *Quantitative Bounds for the U^4-Inverse Theorem over Low
  Characteristic Finite Fields*, Discrete Analysis 2022:14;
  DOI 10.19086/da.38591; arXiv:2109.13108.
- Terence Tao and Tamar Ziegler, *The inverse conjecture for the Gowers norm
  over finite fields in low characteristic*, Annals of Combinatorics 16 (2012),
  121–188; arXiv:1101.1469.
- Tanja Eisner and Terence Tao, *Large values of the Gowers–Host–Kra seminorms*,
  arXiv:1012.3509.
- James Leng, Ashwin Sah and Mehtaab Sawhney, *Improved Bounds for Szemerédi's
  Theorem*, arXiv:2402.17995v2 (2024).

The general nonclassical integration criterion is established prior work, not
an open problem claimed to be settled for the first time here. The new claims
are the identified sharp endpoint, its exact certificate, the equality
classification and the stated stability/global-threshold consequences.
A broad literature-priority guarantee is not made.
