# Source and originality audit

## Repository pin and access boundary

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `738a39017285045f8eeeac1286b4c8f37d34bef1`.

The repository interface returned this commit as the head snapshot during the investigation. Its message records nine newly delivered manuscripts awaiting integration and says the 61 maintained reports and 3,871-result inventory are unchanged. The pin, rather than an assumed publication date, identifies the inspected state.

Read through the GitHub connector:

- Root `README.md`: repository overview and the distinction between report claims and formalized results.
- `docs/README.md`: reader's guide, report scope and recent integrations.
- `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`: source reconciliation and report scope.
- Selected portions of that report's `article.tex`, including normal-form and normalization discussion, numerical polynomial and rational-map results, and explicit limitations.
- A pinned fetch of source lines 9378–9403 of that article, including the source-22 scope statement leaving algebraic and semialgebraic maps unclassified. The returned blob SHA was `ef7aef1d92813d54dc5a074be2eb40eb3f6b2c4c`.

Pinned file:
https://github.com/VladimirReshetnikov/Surreal/blob/738a39017285045f8eeeac1286b4c8f37d34bef1/docs/surreal/set-sized-quotients-of-omnific-integers/article.tex

Some long connector responses were truncated. This audit does not treat those as complete-file reads. An empty repository search was not treated as proof that a topic was absent. A network checkout failed in the working container; no repository clone or build was completed. The article therefore makes only a targeted comparison with selected maintained material, not an exhaustive claim about the entire repository or its unintegrated deliveries.

## What the repository already contributes

The manuscript credits the ordinary constant-term split of Oz, the purely infinite ideal, numerical-polynomial and binomial-basis arithmetic, rational-collapse context, and previous fresh-scale / no-universal-set-test arguments. It does not present those results as newly discovered.

The specific scope statement motivating the project says that algebraic and semialgebraic maps are not classified, with absolute value given as an example of a lattice-preserving function that is only piecewise polynomial. The present article addresses that direction through tail classification, global smoothness, bounded-scale counterexamples, and their interaction. It does not purport to answer a named conjecture from that statement.

## External sources

1. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised power series and omnific integers*, arXiv:1710.07304v5, revised 22 January 2024; Advances in Mathematics 442 (2024), 109513.
   - https://arxiv.org/abs/1710.07304
   - https://arxiv.org/pdf/1710.07304
   - https://doi.org/10.1016/j.aim.2024.109513
   The abstract, normal-form introduction and Hahn-field preliminaries were inspected. The PDF page containing Fact 2.1.1 was also inspected as a rendered image. The article uses the normal-form definition and the real-closed Hahn-field theorem, not the factorization results as a new contribution. The integer-part floor formula is stated in the new article with the negative-infinitesimal correction explicitly included.

2. G. O. Jones, M. E. M. Thomas and A. J. Wilkie, *Integer-valued definable functions*, Bulletin of the London Mathematical Society 44(6) (2012), 1285–1291.
   - https://doi.org/10.1112/blms/bds059
   - https://kops.uni-konstanz.de/bitstreams/20b313d7-1eb5-4a70-9b95-b91ab184ecc2/download
   Bibliographic details and the author-deposited abstract establish the classical analytic definable integer-valued rigidity antecedent. The article does not import an unstated theorem over non-Archimedean integer parts from this source.

3. Neer Bhardwaj, Raymond McCulloch, Nandagopal Ramachandran and Katharine Woo, *Integer-valued o-minimal functions*, arXiv:2404.10737v1 (2024).
   - https://arxiv.org/abs/2404.10737
   - https://arxiv.org/html/2404.10737v1
   The preprint's abstract, finite-difference context and bibliography were inspected. The article cites the inspected version without transferring its numerical exponential growth constants or asserting that they agree with later versions.

4. Chris Miller, *Infinite differentiability in polynomially bounded o-minimal structures*, Proceedings of the American Mathematical Society 123(8) (1995), 2551–2555.
   - https://doi.org/10.1090/S0002-9939-1995-1257118-1
   - https://www.jstor.org/stable/2161287
   Bibliographic and conceptual antecedent. Publisher/full-text access was limited. The new article proves its particular semialgebraic nonflatness and graph-contact arguments instead of claiming a detailed new reading of this entire source.

5. Jacek Bochnak, Michel Coste and Marie-Françoise Roy, *Real Algebraic Geometry*, Springer, 1998, Ergebnisse vol. 36.
   - https://link.springer.com/book/10.1007/978-3-662-03718-8
   - https://doi.org/10.1007/978-3-662-03718-8
   The official bibliographic page and table of contents were verified. The monograph was not reread in full. It is standard background for quantifier elimination and semialgebraic calculus.

6. The user-specified Wikipedia page on surreal numbers was used for orientation only, not as the technical foundation for a new theorem.
   - https://en.wikipedia.org/wiki/Surreal_number

## Proposed originality boundary

Principal candidate additions:

- A cofinal-discrete-ring tail and global smooth classification, formulated and proved over arbitrary real closed fields.
- The explicit dimension-independent C^(D^2) threshold for scalar graph degree D, with total polynomial degree at most D.
- Exact support-field absorption, its bounded-window use, and the necessary-and-sufficient square-root scale threshold.
- The explicit non-finite-piecewise-polynomial C^k family for every finite k, and lattice-preserving shears.
- The globally smooth, irreducible quadratic, fixed-graph-degree refinement of the no-universal-set-test phenomenon.

Classical or inherited ingredients: finite differences, semialgebraic monotonicity and nonflatness, ordinary graph factorization and contact bounds in principle, Hahn-field real closedness, Newton interpolation, omnific numerical-polynomial descriptions, elementary triangular Jacobians, and fresh-scale support clearing for sets.

This is a bounded originality assessment. No priority certification, exhaustive search, independent referee report, or proof-assistant result is implied. No major named factorization conjecture is claimed solved.
