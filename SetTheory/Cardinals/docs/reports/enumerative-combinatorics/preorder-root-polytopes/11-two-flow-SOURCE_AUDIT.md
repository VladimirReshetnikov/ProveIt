# Source and novelty audit

Prepared 30 September 2026.

## Exact repository target

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `6d04e1e385f2fe7d1cfbdbd8fd8d4e45bd6b6c72`

Commit timestamp returned by the repository API: `2026-09-30T20:19:44Z`.

Inspected report:

    SetTheory/Cardinals/docs/reports/enumerative-combinatorics/
    preorder-root-polytopes/article.tex

Blob: `920246d173bfbc708bcfdd6d67e0a6fc358cb3dc`.

The target passage was re-fetched at the pinned commit, not only from a search-index snapshot. The source interval 9510–9555 contains the “Sampling boundary” box immediately after “Sampling after fixing the support size.” It states that the existing samplers return support sets or auxiliary matchable support pairs, rather than full integer vectors in the demand set or preorder polytope, and calls for an efficiently invertible, restriction-compatible correspondence.

The corresponding README and the broader Part V sampling discussion were also inspected. The repository already has substantial counting, log-concavity, and matroid-lift results. None of those existing results is being presented here as a new discovery.

The identified question is a question in this specific report at this snapshot. This was not an exhaustive audit of every file, every historical version, or every incoming ZIP in ProveIt. No repository write or commit was performed.

## Primary literature inspected

### Suho Oh

“Generalized Permutohedra, h-Vectors of Cotransversal Matroids and Pure O-Sequences,” Electronic Journal of Combinatorics 20(3) (2013), #P14.

- DOI: https://doi.org/10.37236/2769
- Journal: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v20i3p14
- Preprint inspected: https://arxiv.org/abs/1005.5586v3

The journal records publication on 9 August 2013. Section 4 of the inspected preprint, particularly Remark 4.4 and Proposition 4.5, supplies the abstract positive-lattice-point/base correspondence and leaf-count description via zonotopal mixed cells. Pages 6–7 were inspected as page images as well as parsed text.

**Priority consequence:** the existence of the correspondence, and the counting identity derived from it, are not new results of the delivered article. Its contribution is an explicit integer-margin algorithmic realization with exact certificates and the stated further refinements.

### Anari–Liu–Oveis Gharan–Vinzant

“Log-concave polynomials II: High-dimensional walks and an FPRAS for counting bases of a matroid,” Annals of Mathematics 199(1) (2024), 259–299.

- DOI: https://doi.org/10.4007/annals.2024.199.1.4
- Journal: https://annals.math.princeton.edu/2024/199-1/p04
- Version used for theorem numbering: https://arxiv.org/html/1811.01816v3

Theorem 1.1 gives the down-up walk spectral/mixing result. Its matroid application is an explicit imported dependency. The article derives its particular start-mass bound and decoding/error-transfer consequences; it does not claim a new universal matroid sampler.

### Ohsugi–Tsuchiya

“Reflexive polytopes arising from bipartite graphs with gamma-positivity associated to interior polynomials,” Selecta Mathematica 26 (2020), article 59.

- DOI/full text: https://doi.org/10.1007/s00029-020-00588-0

This provides graph-polynomial context and explicitly uses Oh's correspondence. It was not used as a black box to infer the invertibility of the new algorithms.

### Loho–Smith

“Matching fields and lattice points of simplices,” Advances in Mathematics 370 (2020), 107232.

- DOI: https://doi.org/10.1016/j.aim.2020.107232
- Published-version record and abstract: https://arxiv.org/abs/1804.01595v4

Their work includes degree-vector/lattice-point correspondences, matching fields, and reconstruction from tree data. The retrieved record establishes substantial related prior work. The entire 38-page paper was not audited for every possible algorithmic overlap. This is one reason the delivered manuscript does not claim worldwide first priority for a min-cost-flow realization.

### Chapoton–Athanasiadis

“Polytopes and posets associated to preorders,” arXiv:2605.26916v1 (2026).

- Primary record: https://arxiv.org/abs/2605.26916v1

The primary record dates submission to 26 May 2026. The delivered article states the preorder inequalities it uses and proves the needed demand-set identification directly, rather than relying on a broad claim from an abstract.

## What is proposed as the constructive contribution

- The two explicit integer margin systems, equal-tree inverse proof, and polynomial bit complexity.
- A smaller core flow, followed by independent reduced-cost attachments of all unselected suppliers.
- Exact optimality and decoding certificates.
- Supplier restriction/insertion additivity and receiver restrictions outside the support.
- Finite perturbation, cost-chamber, and gauge laws for this realization.
- Full-coordinate implementation of the repository's sampler, with exact total-variation transfer.
- Explicit obstructions to stronger symmetry and locality interpretations.

These statements are proved in the article and tested where algorithmic. “Proved here” does not mean that every statement or argument has been established to be globally new. The important concrete repository deliverable is the missing efficient full-coordinate decoder and inverse.

## Suggested placement if the manuscript is incorporated

This continues a named question of the existing `preorder-root-polytopes` report. It should therefore be treated as an addition to that report, not as a rival standalone report or as formal Lean code. Placement and any merge remain the repository owner's actions. This package does not modify the repository.
