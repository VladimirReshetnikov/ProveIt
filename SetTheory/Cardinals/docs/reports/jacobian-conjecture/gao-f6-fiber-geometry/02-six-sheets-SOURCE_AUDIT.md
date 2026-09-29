# Source audit and claim boundary

Audit date: 24 September 2026, Pacific time.

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

The GitHub API reported `main` at:

`e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`

Relevant directly inspected files:

1. `README.md` (orientation and repository map).
2. `Algebra/JacobianConjecture/README.md`.
   Blob: `67e25dcb94cb7a38fb508ea65e3a35455df859ac`.
3. `Algebra/JacobianConjecture/Research/README.md`.
   Blob: `f0605a788b98bed23df91318aa2069e6802fc66e`.
4. A code-search result in `ProveIt_Walkthrough.tex` citing Gao's paper.

The polynomial-formulas checkpoint and combinatorics directory were also
inspected while choosing the topic. This was a scoped audit; the repository
was not cloned or rebuilt, and all its files/branches/reports were not read.
Repository claims of formal verification are not passed through as claims
that this article's new results have been formalized.

## Primary paper

Shuhong Gao, *Counterexamples to the Jacobian conjecture in dimensions
greater than two*, arXiv:2608.00222v1, 31 July 2026.

https://arxiv.org/abs/2608.00222v1

Sections read for this article include Section 4.5.1, Theorem 4.5 and its proof,
the concluding remarks, and Appendix A.3. The PDF's printed pages 23 and 24
were visually inspected to verify formulas and notation. The current abstract
page still listed v1 as the available submission during this audit.

Already in that source: the map F_6, stage and sweep formulas, polynomiality,
determinant -290, coordinate degree profile, generic six-point fiber, the
sextic R_Y, and four-point nonzero axis fibers. These are explicitly credited.

The concluding discussion and Appendix A.3 state that the complete
higher-dimensional stratifications, including F_6, are left for later work.
This article resolves the F_6 fiber-cardinality question with a criterion
valid at every target. It does not claim a Whitney stratification of all
singular discriminant loci, and does not resolve the analogous F_4, F_5,
or F_7 problems.

Developed in this article: the derivative identity; uniform root chart at
c=0; exact omitted locus; explicit six-element normalized algebra and its
smoothness; original-source open embedding and its boundary; normalized
discriminant and nonproperness set; geometric and arithmetic S_6 results;
real fiber spectrum; the general quadratic-contraction lemma.

## Standard mathematical references

- Stacks Project, Tag 02GH: morphisms between schemes etale over a common base.
- Stacks Project, Tag 025G: universally injective etale morphisms are open immersions.
- Stacks Project, Tag 0BJF: finite locally free discriminants and etaleness.
- J.S. Milne, *Fields and Galois Theory*, v5.10, September 2022:
  Theorem 4.28, Lemma 4.31, and the solvability-by-radicals theorem.

These facts support explicit proofs; they do not supply the new numerical
coefficients or the map-specific normalization.

## Novelty and reproducibility limits

A bounded primary-source search used combinations of the paper identifier,
Gao, F_6/F6, fibers, normalization, and Jacobian. It did not identify an
extension matching the results here. This is not an exhaustive priority
search, especially for unpublished material, other repository branches,
or sources not indexed or accessible during the audit.

All 63 exact checks in the supplied driver passed. They are executed
computer-algebra checks, not Lean/Rocq certificates. The universal proofs
of the root chart, normality, boundary, nonproperness and monodromy are in
the article, and have not undergone independent peer review.
