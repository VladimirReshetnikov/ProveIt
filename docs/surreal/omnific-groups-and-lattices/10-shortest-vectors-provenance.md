# Provenance and evidence boundaries

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `220784a4766b9dd9ab3deb92f9f28ddfdd866187`

Inspected September 23, 2026. Repository content was read through the connected
GitHub tools; the repository was not modified.

The targeted review included:

- Root `README.md`, opening overview and later capability/status material.
- `docs/README.md`, opening report inventory and reading routes.
- Opening scope/status material in `docs/FORMALIZATION.md`.
- `docs/surreal/omnific-diophantine-geometry/article.tex`, opening definitions,
  scope and principal results (lines 1–220 of the pinned source).
- `Surreal/Algebra/LatticeEnergyCertificate.lean`, header and initial declarations
  (lines 1–120 of the pinned source).

A repository search for “shortest vector” returned no hit. This is NOT treated
as a proof that no related assertion occurs anywhere in the repository. The
review was not a complete code audit or a read of all reports.

The new proofs do not depend on accepting an unverified main theorem from a
repository research draft. They use the classical surreal normal-form facts
stated in the article and give the additional algebraic and optimization proofs.

## Primary literature

- Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*, LMS Lecture
  Note Series 110, Cambridge University Press, 1986.
  DOI: https://doi.org/10.1017/CBO9780511629143
  Classical background reference; the bibliographic record and normal-form
  context were also checked against the L’Innocente–Mantova primary paper.
- Sonia L’Innocente and Vincenzo Mantova, *A factorisation theory for generalised
  power series and omnific integers*, arXiv:1710.07304v5, January 22, 2024.
  https://arxiv.org/abs/1710.07304
  The introduction and normal-form discussion were inspected; its Theorem B
  already proves the Gonshor prime result mentioned in the article.
- Omid Amini and Noema Nicolussi, *Higher rank inner products, Voronoi tilings
  and metric degenerations of tori*, arXiv:2310.06523v1, October 10, 2023.
  https://arxiv.org/abs/2310.06523
  Especially Example 3.2, Theorems 3.9 and 8.1, Corollary 8.3. Relevant PDF pages
  were inspected. This is an acknowledged predecessor, not a result claimed
  anew by the present article.
- A. K. Lenstra, H. W. Lenstra Jr., L. Lovász, *Factoring polynomials with rational
  coefficients*, Mathematische Annalen 261 (1982), 515–534.
  https://doi.org/10.1007/BF01457454
  Publisher metadata was checked. The reduction inequalities used in the article
  are explicitly stated and their consequences proved directly; no execution of
  the classical algorithm over omnific inputs is claimed.

Web and repository searches were not exhaustive. Some broad web searches
returned irrelevant results. Novelty should be assessed by independent expert
review rather than inferred from an unsuccessful search.

## Verification actually performed

1. Exact SymPy identities for the matrices, triangular factorization,
   Gram–Schmidt expression, Pell recurrence, and target-perturbation example.
2. Exact integer Pell norm, consecutive determinant, and gcd checks for indices
   0 through 80 (81 checks of each type).
3. Repeated pdfLaTeX compilation to stabilize references, with a final log check.
4. PDF rendering and visual inspection of the layout, plus extracted-text checks
   for unresolved reference tokens and replacement characters.

The finite checks passed using SymPy 1.14.0. They do not amount to formal proof
verification. No Lean formalization, Lean build, or independent peer review of
these new results was performed. No actual surreal number was represented by a
small positive floating-point substitute.

The PDF/source pair is the article; these supporting files document evidence and
reproduction steps, not extra mathematical assumptions.
