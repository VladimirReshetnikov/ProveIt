# Squarefree products of small primes after arbitrary deletions

Open **squarefree_prime_products.pdf** for the ten-page paper. Theorems 1.1 and 2.1 give the logarithm-squared cutoff and exact quotient description. Theorem 6.1 gives the shorter product length and a polynomial height bound. Section 7 gives unconditional almost-all results. Section 8 constructs a single small prime list that works simultaneously for many moduli. Sections 9–11 contain finite examples, the input-source audit, comparisons and further questions.

## Reproduce

The full LaTeX source is in one file. A standard TeX Live installation with pdfLaTeX, Latin Modern, AMS, mathtools, booktabs, geometry, microtype and hyperref suffices. Run from this folder.

```sh
pdflatex -interaction=nonstopmode -halt-on-error squarefree_prime_products.tex
pdflatex -interaction=nonstopmode -halt-on-error squarefree_prime_products.tex
python3 verify.py > reproduced.json
cmp reproduced.json results.json
```

The verifier uses the Python 3 standard library. It cross-checks exact integer representation counts using direct enumeration and group-ring multiplication, enumerates every retained set in the stated exhaustive examples, and verifies the quadratic and cubic quotient counts. Runtime on this build was under one second. These examples illustrate the theorem; the asymptotic proof is in the paper.

## Proof status and provenance

The new results have a mathematical proof in the paper. The imported Dirichlet GRH declaration and the upstream build records were inspected. This project did not rebuild that Lean development or formalize the new theorems. The compiled PDF and the exact computation output were checked. The report distinguishes the all-modulus application of Dirichlet GRH from the unconditional large-sieve conclusions.

- Upstream Lean commit: 72fead102f663d5c7a407964a13dc0cf9d977207
- ProveIt inventory commit: 4d7990202f9f106b2ffe8c209f073ad01d5e1987
- Closest earlier workspace report: **Squarefree products after adversarial deletion of small primes**, in orthogonal_nullity_and_prime_products.zip (archive SHA-256 2f84a915797bae4d9977a812daaf83275fd9deb1f168a32f5b1e522a11a39409). It supplies the earlier majority result for cutoffs of exponent strictly greater than two and the fixed-cardinality circle method.
- The mathematical articles, pinned repository files, and the requested encyclopedia article are linked in the PDF and LaTeX source. Novelty was checked against the identified sources. Publication priority has not been established.
