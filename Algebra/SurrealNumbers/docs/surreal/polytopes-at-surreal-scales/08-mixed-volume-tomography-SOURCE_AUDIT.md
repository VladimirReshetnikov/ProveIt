# Source and priority audit

Date: 30 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned snapshot tree identifier returned by GitHub:
`6996fee43cc97b6c16351def7507d59a95bf62f0`.

The root README was read on the main branch during the same inspection. The surreal-project and report READMEs were fetched at the pinned identifier:

- `Algebra/SurrealNumbers/README.md`
- `Algebra/SurrealNumbers/docs/README.md`
- `Algebra/SurrealNumbers/docs/surreal/euclidean-three-space/README.md`

They establish the repository's reported subject matter and its distinction between research reports and exact Lean mappings. This was not a repository build, an independent axiom audit, or an exhaustive search of every source file. An absence claim about similar arguments elsewhere in the repository would exceed this inspection.

## Primary mathematical references

1. Michael Joswig, Georg Loho, Benjamin Lorenz, Benjamin Schröter, *Linear programs and convex hulls over fields of Puiseux fractions*, arXiv:1507.08092v2; MACIS 2015, LNCS 9582 (2016), 429–445. Ordered-field polyhedral background. The introduction and its real-closed transfer discussion were inspected. https://arxiv.org/abs/1507.08092

2. Artem Chernikov, Alex Mennen, *Combinatorial properties of non-archimedean convex sets*, arXiv:2109.04591v2; Pacific J. Math. 323 (2023), 1–30. The introduction, valuation-ring convexity definition, module connection, and finite-generated versus spherical-complete distinction were inspected. Their convexity is not the order-convexity defining the polytopes in this manuscript. https://arxiv.org/abs/2109.04591

3. Kiumars Kaveh, Peter Makhnatch, *Invariant factors as limit of singular values of a matrix*, arXiv:1811.07706v2; Arnold Math. J. 8 (2022), 561–571. This is relevant prior work for the singular-value connection; the manuscript supplies its own finite Cauchy–Binet proof for the required valuation identity. https://arxiv.org/abs/1811.07706

4. Petter Brändén, June Huh, *Lorentzian polynomials*, Annals of Mathematics 192 (2020), 821–891, DOI 10.4007/annals.2020.192.3.4; arXiv:1902.03719v8. The journal entry and preprint background establish the volume-polynomial and tropical setting. No claim is made to replace or reprove their general Lorentzian theory. https://annals.math.princeton.edu/2020/192-3/p04

5. Rolf Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, second expanded edition, Cambridge University Press, 2014, DOI 10.1017/CBO9781139003858. Standard reference for real mixed volumes and Alexandrov–Fenchel. Bibliographic metadata were checked; the book was not audited chapter by chapter. The manuscript explicitly explains the finite transfer boundary for the classical properties used.

## What the source review does not establish

The review identifies relevant prior frameworks but does not certify historical priority of the determinant-ideal synthesis, the adaptive recognition formulation, the nonadaptive obstruction, or the rank-two interval theorem. “Proved here” means that a proof is supplied, not that the statement is guaranteed absent from earlier literature.

The article resolves structural problems formulated in it. It does not claim to settle a named previously published major open conjecture. The higher-dimensional realization problem remains a proposed continuation, not an accomplished result.
