# Source audit and scope

Inspection date: 7 October 2026.

## Pinned snapshots

OpenAI mathematics repository:

    adc7f1241b42e322a6451854ab7e4b4c146bf78a

The commits endpoint reported the commit at 2026-10-06T21:58:50Z. This is the snapshot used for the catalogue and progression-manuscript comparison.

ProveIt:

    bbde2b873b2dc7b48af1730926452bdda18bf9c8

The commits endpoint reported the commit at 2026-10-07T17:53:29Z. The live repository continued to change during the work; later search results were used for navigation only, not silently substituted for this snapshot.

## OpenAI sources actually inspected

Repository: https://github.com/openai/math

- `README.md`: collection scope and verification-stage qualification; reported 722 manuscripts and 372 families.
- `overview.tex`: catalogue excerpts including entries 159 (quasipolynomial progressions), 160 (van der Waerden growth), 161 (Sidorenko), and neighboring subjects. These are catalogue-level claims, not independently validated proofs.
- The contents listings for `preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/` and `build/` established the source layout.
- `build/main.tex`: full driver and abstract.
- `build/sections/00-introduction.tex`: lines 1–220, blob `f68b7a6a7c0e0a9a864de51b12aa8d952d05104b`.
- `build/sections/01-setup.tex`: lines 1–220, blob `9d6af736019f72b0504b97381a9037450e53b5b0`.

These reads support the article's account of the claimed stretched-exponential density saving, triangular polynomial cells, strict/padded certificates, fresh-rank requirements, and descending width-precision dependence. The mathematical results of this package do not assume that claimed density bound. The entire progression proof, its foundations, and its Lean status were not independently audited. Attempts to open its raw PDF through the web reader failed; the mathematical comparison used the available TeX sources instead.

## ProveIt sources actually inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned reads:

- `Combinatorics/Ramsey/FORMALIZATION_STATUS.txt`, lines 1–125, blob `3019e17a3e41be96d1adccebf84a9e766a3ad24b`.
- `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/30-fixed-radius-bohr-SOURCE_AUDIT.md`, full file, blob `ea818e377eaf18b512c40e0081674ed78e5197ad`.
- `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/code/30-fixed-radius-bohr-verify.py`, lines 1–220, blob `673cac9cad2583409d6c209e49e92f32fd602864`.
- Directory listings for the Ramsey tree and local-refinement collection, plus search excerpts of the collection README for navigation and package identification.

The status file reports 113 exact companions, seven open catalogue statements, 755 reachable modules, and 4,836 public audited theorems. Those are repository-reported facts, not a fresh build performed for this package. It explicitly distinguishes qualitative Szemeredi by a non-Gowers route from the open quantitative Gowers route. It records the vendored OpenAI bridge used for the qualitative theorem and the Freiman/Balog–Szemeredi companions.

The earlier fixed-radius source audit records the angular normalization, the older Lemma 10.10 coefficient, and the corrected division by rank in Corollary 10.11. This package does not change that correction or assert a stronger full Theorem 10.13.

The prior exact companion contains the disjoint escape-tube inequality and the product/CRT spike construction. Its product model has rank `2s+1`, size `2L-2+3^s`, boundary `3^s`, and normalized ratio tending to `3^s/2`. Its composite-cyclic realization has the same asymptotic lower obstruction. These explicitly inspected formulas are the basis for the sqrt(3)-to-2 comparison. We do not infer absence of other constructions from an incomplete search.

The combined `article.tex` fetch returned no text. Accordingly this work does not claim to have reviewed that entire combined article or every pending research package. The prime-order polynomial-bound question is stated precisely and answered in the delivered manuscript; its status as a named or broadly recognized open literature problem is not claimed.

## Published primary sources

W. T. Gowers, *A new proof of Szemeredi's theorem*, GAFA 11 (2001), 465–588.

https://www.cs.umd.edu/~gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

The source was read as parsed text and as page images, including PDF pages indexed 64 and 65 (printed pages 529 and 530). These establish the Section 10 local-translation interface. The manuscript does not rely on the printed Corollary 10.11 parameter without its repository correction.

Ben Green, *A Szemeredi-type regularity lemma in abelian groups, with applications*, arXiv:math/0310476v2, 21 October 2004.

https://arxiv.org/abs/math/0310476
https://arxiv.org/pdf/math/0310476

Sections 3–4 were inspected, including a rendered image of PDF page indexed 7. They discuss Bohr boundary irregularity, Bourgain's regular-radius method, Tao's averaging viewpoint, and smoothed Bohr neighborhoods. These supply historical context, not a premise needed for the main construction.

## Limits of this review

The review was focused on additive-combinatorial interfaces after catalogue-level topic selection. It was not a verification of all purported breakthroughs in either repository. Targeted web searches did not establish priority for the new explicit family. The existing escape-tube upper bound is attributed, not presented as new. The conventional proofs of the new construction require only the Chinese remainder theorem, elementary rational inequalities, finite counting and elementary limits. Exact Python checks are supplementary and are not Lean kernel checks.
