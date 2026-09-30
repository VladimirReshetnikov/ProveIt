# Source and priority audit

Consulted on 30 September 2026. The article's conventional bibliography
contains all sources actually used as mathematical background. URLs below
are reproducibility identifiers, not claims of unrestricted access to books.

## Repository evidence

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned main commit: 6996fee43cc97b6c16351def7507d59a95bf62f0
Commit timestamp: 2026-09-30T16:07:39Z

The main commit identity was obtained through the connected GitHub API.
The indexed code-search results observed during the inspection used its
parent 5e0f4e05046bacda3c6ba2643f19b91aa632436b. Indexed search freshness was
not assumed to be identical to current branch freshness.

The following concrete source was then read at the pinned main commit:

    Algebra/SurrealNumbers/Surreal/Algebra/Geometry.lean
    blob: 450fd4bbfc017e0da24c28e538af1cc02037ad5a

https://github.com/VladimirReshetnikov/ProveIt/blob/6996fee43cc97b6c16351def7507d59a95bf62f0/Algebra/SurrealNumbers/Surreal/Algebra/Geometry.lean

The source defines dot and cross products in `Surreal.Complexify` and contains
`cross_def`, `cross_swap`, Gram, Ptolemy, triangle-area, and Heron statements.
The header separates proved finite algebra from angle and cyclic-equality
obligations. The new polytope and history results are not claimed to occur
in that source. No repository Lean build was run.

Also read as project orientation, on the main branch during the same session:

    Algebra/SurrealNumbers/README.md
    Algebra/SurrealNumbers/docs/README.md

Those README files report their own formalization and research-draft status.
Their assertions are not substituted for checking individual theorem sources.
A targeted search for polytope and lexicographic terminology is not an
exhaustive review of the repository. No absence or uniqueness claim is based
on an incomplete code-search result. No repository file was modified.

## Mathematical background

1. Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*,
   LMS Lecture Note Series 110, Cambridge University Press, 1986.
   DOI: https://doi.org/10.1017/CBO9780511629143
   Normal Form, Chapter 5, pp. 52-94:
   https://doi.org/10.1017/CBO9780511629143.006
   Role: classical Conway normal forms, ordered leading coefficients, and
   the surreal setting. Publisher book/chapter metadata was checked.

2. Lou van den Dries, “Alfred Tarski's elimination theory for real closed
   fields,” *Journal of Symbolic Logic* 53(1), 1988, pp. 7-19.
   https://doi.org/10.2307/2274424
   Role: uniform quantifier elimination, completeness, and transfer over
   real parameters. The publisher page was read. Its online publication
   date is not the original 1988 journal publication date.

3. Michael Joswig, Georg Loho, Benjamin Lorenz, Benjamin Schröter,
   “Linear programs and convex hulls over fields of Puiseux fractions,”
   MACIS 2015 proceedings, LNCS 9582, Springer, 2016, pp. 429-445.
   https://doi.org/10.1007/978-3-319-32859-1_37
   https://arxiv.org/abs/1507.08092
   https://arxiv.org/html/1507.08092
   Role: established ordered-field linear programming and convex hulls;
   Theorem 3.1 on finite specialization preserving combinatorial type.
   Full HTML was read; bibliographic venue was checked against arXiv metadata.
   These results are not claimed as new in the article.

4. Marten Wortel, “Lexicographic cones and the ordered projective tensor
   product,” 2018, arXiv:1812.04830.
   https://arxiv.org/html/1812.04830v1
   Role: Proposition 4.4 gives the classical lexicographic description of
   finite-dimensional totally ordered real vector spaces. Full HTML was read.
   The article's proof adds explicit support-initial compatibility, but
   does not claim to originate finite-dimensional lexicographic orders.

5. Carl W. Lee and Francisco Santos, “Subdivisions and triangulations of
   polytopes,” Chapter 16 in *Handbook of Discrete and Computational Geometry*,
   3rd edition, Goodman/O'Rourke/Tóth, eds., CRC Press, 2017, pp. 415-447.
   https://www.csun.edu/~ctoth/Handbook/chap16.pdf
   Role: regular subdivisions, perturbations, and Theorem 16.4.1 describing
   the secondary polytope of dimension n-d-1 and its refinement face poset.
   Parsed text and page screenshots were inspected, including printed
   page 424 (PDF page index 9). The n-d-1 coherent-chain bound is classical
   in this framework. The manuscript supplies its own direct proof and
   explicit sharp polygon realization rather than claiming that dimension
   formula as new.

6. Jacek Bochnak, Michel Coste, Marie-Françoise Roy,
   *Real Algebraic Geometry*, Ergebnisse, 3rd series, vol. 36, Springer, 1998.
   https://doi.org/10.1007/978-3-662-03718-8
   Role: classical semialgebraic curve selection and algebraic Puiseux germs.
   Publisher bibliographic metadata was checked; no claim of having read
   the entire book in this session is made.

7. Saugata Basu and Marie-Françoise Roy, “Quantitative Curve Selection Lemma,”
   2018, arXiv:1803.00505.
   https://arxiv.org/html/1803.00505v3
   Role: primary research exposition of curve selection over real closed
   fields and the algebraic-Puiseux framework. Full HTML was inspected.
   No new quantitative bound or reproduction of that paper's complexity
   estimates is claimed here.

## Claim-specific novelty assessment

- Real algebraic realization of a finite surreal face lattice: a classical
  consequence of real-closed-field transfer, with a direct proof here.
- Finite lexicographic representation: classical ordered-vector-space
  background. The supplied proof explicitly selects the first independent
  normal-form coefficient classes and preserves all initial cuts.
- Chain length n-d-1 and coherent-chain classification: constructive
  consequences/synthesis of standard secondary-polytope ideas, proved here.
- Explicit all-slack real parameter bound: elementary finite leading-term
  domination; not claimed as the first Puiseux specialization algorithm.
- Universal prescribed four-point coordinate-truncation histories,
  convergent rational-coefficient reciprocal construction, and independent
  uniform transfinite endpoint: specific constructions advanced by this
  manuscript, with full proofs. A focused search did not establish historical
  priority. No exhaustive novelty certification is asserted.
- Standard-part and finite Puiseux results: elementary consequences and
  standard-tool synthesis, with hypotheses and limitations made explicit.

All proposed future questions are labeled as directions arising here, not
as verified longstanding open problems in the published literature.
