# Category, continuous-model, and normed-complex evidence

Repository snapshot inspected: `b2341af5370cd8a43f72ebb2341c0d7d7395b634`
(main branch returned by the GitHub plugin on 20 November 2026).

## Repository sources actually fetched

- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/paper/sections/04_categories.tex`
  - Git blob `c4690f44f0db27207a6595fcfe2f4ddb4d24e56a`.
  - https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/paper/sections/04_categories.tex
  - Distinguishes fixed PR presentations, finite tables, and external categories of specified programs; gives finite categories, Yoneda and finite universal constructions. Cite key `repo-categories`.
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/paper/sections/07_obstacles.tex`
  - Git blob `f5e3fdd3302e54f0faec388bf0aae1981a784b36`.
  - https://github.com/VladimirReshetnikov/ProveIt/blob/b2341af5370cd8a43f72ebb2341c0d7d7395b634/Logic/PrimitiveRecursiveArithmetic/docs/proofs/foundations/ipra_categorical_methods/paper/sections/07_obstacles.tex
  - Proves no uniform computable finite covering representatives from a decidable two-class bound; a supplied finite cover does produce a skeleton. Cite key `repo-obstacles`.
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
  - Git blob `bf288a3df2dd6e1a91f6809fa0473fd4ba948a0a`.
  - Current inventory inspected; root agent separately reviewed recent 20 November frameworks. Our section makes no novelty claim for existing completion/continuous-formula methods.

## Primary external sources opened

- Marius Crainic, *On the perturbation lemma, and deformations* (2004), arXiv:math/0403266.
  - https://arxiv.org/abs/math/0403266
  - Full text read at https://arxiv.org/html/math/0403266v1
  - Relevant: §§2.2–2.3 (small perturbations, inverse and Banach-norm criterion), §3.4 (perturbing contractions), §3.8 (topological variants).
  - Root must open the URL itself before using web citation refs. Child refs were `turn639949191view0` (abstract), `turn177243843view0` (full text).
  - Cite key `crainic2004`. The section's mathematical idea is explicitly acknowledged as classical. The exact finite-defect packaging, PR schedule, and observation-specific cutoff are our present derivation, not a claim of a new homological perturbation theorem.
- Itaï Ben Yaacov, Alexander Berenstein, C. Ward Henson, Alexander Usvyatsov, *Model theory for metric structures*, in *Model Theory with Applications to Algebra and Analysis*, vol. 2, LMS Lecture Note Series 350 (2008), pp. 315–427.
  - Author manuscript: https://math.univ-lyon1.fr/~begnac/articles/mtfms.pdf
  - Publisher: https://doi.org/10.1017/CBO9780511735219.011
  - Opened author PDF; pp. 1–5 and continuous predicate / sup-inf definitions examined. The section borrows only the model-theoretic viewpoint, not its compactness theorem.
  - Child ref `turn639949191view1`; root must open for citation.
  - Cite key `bbhu2008`.
- Russell O'Connor, *A Monadic, Functional Implementation of Real Numbers*, MSCS 17(1) (2007), 129–159; arXiv:cs/0605058.
  - https://arxiv.org/abs/cs/0605058
  - Relevant background for metric completion. Not cited directly in our topology section because root covers completion separately.

## Delivered material

- `paper/sections/category_models.tex`: approximately 2,700 words plus mathematical displays; exact finite defect lemma, explicit tail and input precision schedules, repaired contraction, observation-only boundary schedule, perturbation neighborhoods, mapping-cone homotopy inverse, continuous-predicate interface and zero-gap counterexample, formalization obligations.
- `code/check_chain_contraction.py` and `evidence/chain_contraction_check.json`: exact rational 4×4 example with h² nonzero and hR unequal to Rh; all 6 finite-cutoff cases and 9 precision schedules passed. It independently computes the rational inverse by Gauss–Jordan and compares the actual error with the analytic bound.
- Checked general finite algebra kernel owned by Lean agent: `lean/ObservableAnalysis/Neumann.lean`.

## Important boundaries

- No claim of general computation of homology, arbitrary image membership, or quotients.
- No finite-net assumption for infinite-dimensional Banach unit balls.
- The square-zero law for the perturbed differential must be exact; small square is insufficient for the commutation argument.
- Operator norm notation is used as a supplied universal majorant, not a computed supremum.
- Core-preserving fixed PR operators give a direct construction. More general represented operators need finite composition evaluation contracts; the error ledger must include those errors.
- The compiled Lean algebra theorem is a metatheorem; the object iPRA derivation needs the explicitly listed presentation and finite arithmetic bridge.
