# Provenance and research boundary

Prepared September 30, 2026. The paper's bibliography contains the complete
citation list. All mathematical proofs, the Python implementation, test data,
and the article source in this package were prepared for this request.
No existing repository source modules or third-party papers are redistributed.

## Repository snapshot inspected

Repository: https://github.com/VladimirReshetnikov/ProveIt

Revision: `b998f70c6886e6a00339a6f4a02ed8625324d357`

Focused paths:

- `Computability/HilbertTenthProblem/README.md`
- `Computability/HilbertTenthProblem/Lean/MRDP.md`

The repository root README and tree were inspected to orient the work.
The article relies only on the relevant MRDP interfaces and their documented
scope; no unrelated research claim in the root README is adopted. Existing
Lean status statements are attributed to the repository's documentation, not
to a fresh build in this environment.

## Primary literature consulted

- Yu. V. Matiyasevich, Enumerable sets are Diophantine (1970).
  Publisher reprint: https://doi.org/10.1142/9789812564894_0013
- L. G. Valiant, The complexity of enumeration and reliability problems (1979).
  https://doi.org/10.1137/0208032
- B. L. Kaminski and J.-P. Katoen, On the hardness of almost-sure termination.
  https://arxiv.org/abs/1506.01930
- G. Barmpalias and A. Lewis-Pye, Differences of halting probabilities.
  https://arxiv.org/abs/1604.00216
- J. Duda, P?=NP as minimization of degree 4 polynomial, integration or
  Grassmann number problem, and new graph isomorphism problem approaches.
  https://arxiv.org/abs/1703.04456
- A. A. Ahmadi and J. Zhang, Complexity aspects of local minima and related
  notions. https://arxiv.org/abs/2008.06148
- R. Majumdar and V. R. Sathiyanarayana, Positive almost-sure termination --
  complexity and proof rules. https://arxiv.org/abs/2310.16145
- R. Majumdar and V. R. Sathiyanarayana, Sound and complete proof rules for
  probabilistic termination. https://arxiv.org/abs/2404.19724

Bibliographic and abstract pages were used to verify attribution and scope.
The reductions and quantitative estimates in the article are written out
independently. This was not an exhaustive literature or priority audit.

## Executed checks and document build

- Python 3.13.5; exact arithmetic uses integers and fractions.Fraction.
- 6,050 exact finite checks; report seed 20260930.
- 60 additional optional NumPy eigenvalue smoke tests.
- A separate 3,000-COPY-gate regression exercised iterative wire evaluation
  (6,004 variables); accepted and rejected input cases both passed. This
  regression is not included in the 6,050-category total.
- pdfTeX 1.40.26, TeX Live 2025/dev/Debian; three successful final passes.
- PDF: 26 pages, letter format. No unresolved references, overfull boxes,
  or LaTeX warnings in the final build log.
- Rendered with the PDF skill's renderer; pages inspected visually.

These checks supplement, and do not replace, the mathematical proofs. No
Lean/Coq checking, external peer review, or repository modification occurred.
