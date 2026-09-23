# Sources, repository comparison, and scope

Research date: 22 September 2026. The delivery fixes all repository comparisons to the revision below, rather than to a moving main branch.

## Repository evidence

Repository: https://github.com/VladimirReshetnikov/Surreal

Revision: `465a54b479a1ee842cbf7db1689a7d2f6bfe25e1`.

The pin was retrieved through the connected GitHub recursive-tree action. Targeted reads used the connected GitHub tool. The inspection included the root README, the documentation catalogue, directory listings, and the following substantive scope documents:

- `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/README.md`
- `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/10-nonlinear-rigidity-SOURCES_AND_SCOPE.md`
- `docs/surcomplex/entire-functions-at-arbitrary-rank/README.md`
- `docs/surreal/tail-spans-and-differential-transcendence/README.md`

The `docs/new` directory listing contained only a README at this pin. The root source tree and the docs listings were consulted for navigation, not treated as proof of the absence of a theorem.

This was NOT a complete line-by-line audit of the long manuscripts, Lean declarations, archived deliveries, branches, or historical commits. The results below are compared against the explicitly inspected current scope statements. No blanket claim that an equivalent result cannot occur elsewhere in the repository is made.

### The exact question

The holonomic README says the source-10 manuscript's Question 15.1 is now **Question 19.1**, label `hol:q:nonlinear`, after merging. It explicitly says that first-order nonlinear rigidity is proved, while unrestricted higher orders with vanishing residue corner polynomial remain open. It also identifies the equation

`z^2 f f'' + z f f' - z^2 (f')^2 = 0`

as a vanishing-corner example with polynomial solutions of every degree.

The new article answers that question for **all finite differential orders when the value group has no order unit**. Its conclusion extends to M = Frac(E): differential-algebraic members are rational. It does not assert an all-group solution of the question, and does not call it an independently verified historical conjecture.

### Existing results explicitly credited

The holonomic report already has the all-scale coefficient criterion, the series sum omega^(-omega^n) z^n, its domain warning, first-order independence, and polynomial Painleve exclusions. These are not claimed as new examples or methods.

The entire-functions report already has polynomial intersection obstructions under noncofinal scalar extension, coarsened support methods, and the countable-cofinality/no-order-unit distinction. The polynomial half of Theorem 1.1 is a coefficient-field version of this elementary obstruction. The meromorphic descent argument is the substantive additional step.

The tail-span report already has continuum-sized differential-independent families and uses almost-disjoint binary-prefix sets. Its coefficient fields, analytic category, and derivations differ. This delivery uses independent exponent monomials to obtain strongly entire functions on a fixed full Hahn field and proves independence over that entire field as constants. Neither continuum cardinality nor almost-disjoint combinatorics alone is claimed novel.

## Primary literature consulted

### Hahn and surreal interpretation

Vincenzo Mantova and Mickael Matusinski, *Surreal numbers with derivation, Hardy fields and transseries: a survey*, arXiv:1608.03413v2 (2016).

https://arxiv.org/html/1608.03413v2

The HTML normal-form and omega-map discussion in Section 2.2 was inspected. These classical facts supply the last interpretive step, not the new descent theorem. The distinction from scalar surreal derivations is retained throughout.

### Classical coefficient recurrences

Adolf Hurwitz, *Sur le developpement des fonctions satisfaisant a une equation differentielle algebrique*, Annales scientifiques de l'Ecole Normale Superieure, series 3, volume 6 (1889), 327–332.

https://doi.org/10.24033/asens.326

The primary NUMDAM bibliographic page and the historical attribution in the following paper were consulted. No claim of a complete fresh reading of Hurwitz's original French proof is made.

Vichian Laohakosol, Kannika Kongsakorn, and Patchara Ubolsri, *Coefficients of differentially algebraic series*, Journal of the Australian Mathematical Society, Series A 48 (1990), 402–412.

https://doi.org/10.1017/S1446788700029955

The publisher PDF's parsed text was inspected, and pages 404, 408, and 409 were also viewed as screenshots to check the displayed hypotheses and recurrence formulas. Lemma 3 and the adjoining proof are important precedents for isolating a high coefficient through a polynomial in its index. The current article supplies its own formal tail-linearization proof over arbitrary characteristic-zero fields, using this coefficient-field principle as classical background rather than a priority claim.

Christian Krattenthaler and Tanguy Rivoal, *Arithmetic properties of the Taylor coefficients of differentially algebraic power series*, arXiv:2502.09259v1 (2025).

https://arxiv.org/html/2502.09259v1

The abstract and bibliographic information were consulted, and the HTML version was located. It is cited as modern arithmetic context, not as a theorem whose full proof was checked or imported. No arithmetic denominator bound is needed for our results.

### Differential algebra and non-Archimedean comparison

Rida Ait El Manssour, Anna-Laura Sattelberger, and Bertrand Teguia Tabuguia, *D-Algebraic Functions*, arXiv:2301.02512v3.

https://arxiv.org/html/2301.02512v3

Abstract and HTML framework were consulted for context. The particular closure and finite-system consequences used here have short proofs in the article; no software from that project is used or bundled.

Pei-Chu Hu and Yong-Zhi Luan, *Non-Archimedean meromorphic solutions of functional equations*, arXiv:1311.5291v1 (2013).

https://arxiv.org/html/1311.5291v1

Its introduction, field hypotheses, and stated nonlinear context were consulted. The setting of a complete algebraically closed field with a nontrivial non-Archimedean absolute value is distinguished from general ordered-group-valued Hahn fields. No claim is made to replace that paper's results or resolve all rank-one questions.

## What the search does and does not support

The inspected sources did not identify the exact meromorphic coefficient-field intersection theorem together with the universal no-order-unit nonlinear deduction, nor the exact full-constant-field strongly entire branch construction. This supports presenting them as **proposed contributions with proofs**, not certified historical firsts.

Some targeted searches returned irrelevant results or inaccessible pages. No exhaustive MathSciNet/zbMATH audit, full-book search, or complete citation-network search was performed. A failed search is not used as evidence that no prior theorem exists.

The article is a mathematical research attempt with detailed arguments. It has not been independently refereed or Lean-verified. Third-party texts and fonts are not included in the archive.
