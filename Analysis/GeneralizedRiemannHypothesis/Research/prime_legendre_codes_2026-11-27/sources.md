# Source inspection and provenance

Accessed 27 November 2026 via the GitHub connector. All reads were read-only.

Repository: https://github.com/VladimirReshetnikov/ProveIt

The two requested directories were listed first; the following Git object identifiers were returned for their principal source subtrees. These content identifiers are more precise than a moving branch name. The later branch metadata query returned `main` at `adc82b6b50abae288ff08ae8c63e2c4aa43ac8af` (2026-11-27T20:01:20Z); this was a separate query after the file reads, not a guarantee that every earlier read was at that exact branch head.

## Vendored proof

Base: `Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/`

- Vendor README blob `a04f66a62af93fc0757f2aa573f3b053fde51bfa`.
- `grh/` tree `2e133df63d7f4da6b3059c4195324f8e9187ba73`.
- Vendored upstream revision, as recorded by the README: `72fead102f663d5c7a407964a13dc0cf9d977207` (25 November 2026). The README reports that all 818 imported files are byte-identical to the upstream revision; this assertion was not independently rehashed.
- `grh/README.md` blob `68cd862687bac1dadf3f14dc7266365e5c8b1ec4`.
- `grh/src/Statements.lean` blob `1cd1bce93344065936b2b392b23306254e0785ef`.
- `grh/src/Main.lean` blob `1adf4187a938510363cdb0dde0a6d628ff39c600`.
- `grh/src/New/Main.lean` blob `fc0ae69627d2e66c3d1d57815d42f0aac5823432`.
- `grh/src/New/Reduction/Zeros/Criterion.lean` blob `5c06362a50e044d491423fb3d830bae6a50c0075`.
- `grh/src/New/Reduction/OneSidedBound.lean` blob `99e5240de112527b739068b692e5007720d310c1` (introductory excerpt inspected).
- `grh/scripts/PrintAxioms.lean` blob `ec5adcfd7baeff36130db9a763720ba1a6567c57`.

Relevant exports: `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`, `LFunction_eq_zero_re : DirichletLZerosOnLine`, and `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`. The proof uses the zero-free half-plane criterion and functional-equation reflection. These are sufficient for the ordinary GRH character-sum explicit formula; no generalization to other L-functions is imported. The new work does not use or audit the full arithmetic proof.

The vendored README reports Lean 4.35.0, Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), and independent kernel exports/checks. The root ProveIt build does not build this package. No local Lean executable was available, and the build/checks were not repeated.

## Merged article

Base: `Analysis/GeneralizedRiemannHypothesis/Article/`

- `README.md`: `7f3286088c94a8df3d8b9846112ea83dbbbbfa25`.
- `article.tex`: `2d95d3db42756d4dcea77ecd304c92ded01ad7c6`.
- `sections/` tree: `5ea418a24081239fe126bb25757cd4897d31e74a`.
- `sections/intro.tex`: `b68b38b12772e23ffae3a25a1d449881435a4e5c`.
- `sections/src.tex`: `f69668b2f95261630bb1282c2cc1f9c172b7e530`.
- `sections/dir.tex`: `da58d506e24a05e1b888da2802398f277d9ea727`.
- `sections/rec.tex`: `da56d6ad5a1a699e335dcfd327bcdc9492c64017`.
- `sections/zer.tex`: `1f1e31367ea4fdd259786e3997d46ecd279d5cbc`.
- `sections/gra.tex`: `48797ee87d3cb1c92114438476950d4a976fea0d`.
- `sections/spn.tex`: `886e8716472aa82fd45ff68da03be946e9dbd3da`.

The TeX sources, rather than the compiled 723-page article PDF, were used for this analysis. The relevant passages read include the exact scope of the input theorem (`src:thm:dgrh`), the smoothing interface, the prime-bias lemma (`dir:lem:bias`), squarefree product and partition results (`dir:thm:quotient`, `dir:thm:factorization`), majority signs (`dir:sec:signs`), and the weighted prime-window distinguishing theorem (`rec:thm:ofinite`). Headings and coding/rank keywords were screened in dir, rec, zer, gra, spn, gpp, gpi, cost and tors. The full article and the entirety of its mathematical claims were not independently audited.

## External comparison

- Montgomery and Vaughan, *Multiplicative Number Theory I: Classical Theory* (2007), Theorem 13.7 and Chapters 10/13. The classical GRH prime character-sum bound was verified against the indexed theorem text. The smooth window bound in the new report is also proved by the standard contour argument.
- Guruswami, Rudra and Sudan, *Essential Coding Theory*, January 31, 2022 version, Theorem 4.2.1: https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/prev-ver/web-coding-book-Jan31-2022.pdf .
- Search for Legendre-symbol matrices and GV/dual distance returned standard fixed-prime quadratic-residue cyclic codes (e.g. https://gap-packages.github.io/guava/doc/chap5_mj.html) and determinant results, not the specific varying-prime construction. This is a targeted search, not an exhaustive novelty or priority investigation.
- Upstream public repository: https://github.com/lsernau/grh-lean . The status is taken from its and the vendor's documentation. This note does not claim to independently establish RH or GRH.

## New contribution vs. inherited tools

Inherited: Dirichlet GRH, explicit formula, prime number theorem, Fourier analysis over a binary cube, the classical entropy thresholds. New synthesis: the bidirectional varying-prime construction with near-quadratic prime cutoff and simultaneous code/dual distances; the uniform all-rectangle rank estimate applied to that arithmetic family; the fixed-prefix construction using a reverse quadratic-character obstruction to short dependencies and Fourier convolution to rule out long ones. Novelty relative to examined material is provisional.
